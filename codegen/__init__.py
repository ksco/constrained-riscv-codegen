from __future__ import annotations
from enum import Enum, auto
from typing import Type, List, Tuple, Set
import z3


class Relation(Enum):
    @staticmethod
    def _generate_next_value_(name, start, count, last_values):
        return count

    EQ = auto()


class Name(Enum):
    @staticmethod
    def _generate_next_value_(name, start, count, last_values):
        return count

    ADDI = auto()
    BEQ = auto()
    BNE = auto()
    Count = auto()


class Arg(z3.BitVecRef):
    def __init__(self, name: str, bv: int):
        ctx = z3.get_ctx(None)
        bv = z3.BitVecSort(bv, ctx)
        super().__init__(
            z3.Z3_mk_const(ctx.ref(), z3.to_symbol(name, ctx), bv.ast), ctx
        )

    @staticmethod
    def name(val: int) -> str:
        return str(val)


class Imm12Arg(Arg):
    pass


class Imm13Arg(Arg):
    pass


class GPRArg(Arg):
    @staticmethod
    def name(val: int) -> str:
        return f"x{val}"


class NameArg(Arg):
    @staticmethod
    def name(val: int) -> str:
        return str(Name(val).name).lower()


def check_type(*args: Tuple[Arg, str, Type]):
    for arg in args:
        if not isinstance(arg[0], arg[2]):
            raise TypeError(f"{arg[1]} must be of type {arg[2].__name__}")


class Inst:
    name: Name | NameArg
    args: List[Arg] = []

    def __init__(self, name: Name | NameArg, *args: Arg):
        self.name = name
        self.args = list(args)

    def disassembly(self, vals: List[int]) -> str:
        if isinstance(self.name, NameArg):
            assert len(vals) == len(self.args) + 1
            name = self.name.name(int(vals[0]))
            vals = vals[1:]
        else:
            assert len(vals) == len(self.args)
            name = str(self.name.name).lower()
        return f"{name:8} {', '.join([self.args[i].name(vals[i]) for i in range(len(self.args))])}"


class Kernel:
    args: Set[Arg] = set()
    solver: z3.Solver = z3.Solver()
    instructions: List[Inst] = []

    def __init__(self):
        pass

    def itype(self, name: NameArg | Name, rd: GPRArg, rs1: GPRArg, imm12: Imm12Arg):
        check_type((rd, "rd", GPRArg), (rs1, "rs1", GPRArg), (imm12, "imm12", Imm12Arg))
        self.instructions.append(Inst(name, rd, rs1, imm12))

    def btype(self, name: NameArg | Name, rd: GPRArg, rs1: GPRArg, imm13: Imm13Arg):
        check_type((rd, "rd", GPRArg), (rs1, "rs1", GPRArg), (imm13, "imm13", Imm13Arg))
        self.instructions.append(Inst(name, rd, rs1, imm13))

    def addi(self, rd: GPRArg, rs1: GPRArg, imm12: Imm12Arg):
        self.itype(Name.ADDI, rd, rs1, imm12)

    def beq(self, rd: GPRArg, rs1: GPRArg, imm13: Imm13Arg):
        self.btype(Name.BEQ, rd, rs1, imm13)

    def bne(self, rd: GPRArg, rs1: GPRArg, imm13: Imm13Arg):
        self.btype(Name.BNE, rd, rs1, imm13)

    def imm12(self, name: str) -> Imm12Arg:
        v = Imm12Arg(name, 12)
        self.args.add(v)
        return v

    def imm13(self, name: str) -> Imm13Arg:
        v = Imm13Arg(name, 13)
        self.add_constraints(v % 2 == 0)
        self.args.add(v)
        return v

    def gpr(self, name: str) -> GPRArg:
        v = GPRArg(name, 5)
        self.args.add(v)
        return v

    def name(self, name: str) -> NameArg:
        v = NameArg(name, 16)
        self.add_constraints(z3.And(v >= 0, v < Name.Count.value))
        self.args.add(v)
        return v

    def add_constraints(self, *args):
        self.solver.add(*args)

    def collect_args(self) -> Set[Arg]:
        s = set()
        s.update(
            inst.name for inst in self.instructions if isinstance(inst.name, NameArg)
        )
        s.update(arg for inst in self.instructions for arg in inst.args)
        return s

    def solve(self):
        assert self.collect_args() == self.args

        while self.solver.check() == z3.sat:
            model = self.solver.model()
            res: str = ""
            for inst in self.instructions:
                vals = (
                    [int(model[inst.name].as_signed_long())]
                    if isinstance(inst.name, NameArg)
                    else []
                ) + [int(model[arg].as_signed_long()) for arg in inst.args]
                res += inst.disassembly(vals) + "\n"
            yield res
            self.solver.add(
                z3.Or([f() != model[f] for f in model.decls() if f.arity() == 0])
            )
