from enum import Enum, auto
from typing import TypeAlias, List
import z3


class Variable(z3.BitVecRef):
    def __init__(self, name: str, bv: int):
        ctx = z3.get_ctx(None)
        bv = z3.BitVecSort(bv, ctx)
        super().__init__(
            z3.Z3_mk_const(ctx.ref(), z3.to_symbol(name, ctx), bv.ast), ctx
        )

    def initial_constraints(self):
        return []

    @staticmethod
    def name(val: int) -> str:
        return str(val)


class Imm(Variable):
    pass


class GPR(Variable):
    @staticmethod
    def name(val: int) -> str:
        return f"x{val}"


class MEM(GPR):
    @staticmethod
    def name(val: int) -> str:
        return f"(x{val})"


class FPR(Variable):
    @staticmethod
    def name(val: int) -> str:
        return f"f{val}"


class VFR(Variable):
    @staticmethod
    def name(val: int) -> str:
        return f"v{val}"


class LMUL(Variable):
    def initial_constraints(self):
        return [self >= 0, self <= 7, self != 4]

    @staticmethod
    def name(val: int) -> str:
        # page 12, v-spec-1.0
        assert 0 <= val <= 7 and val != 4
        return ["m1", "m2", "m4", "m8", "", "mf8", "f4", "mf2"][val]


class SEW(Variable):
    def initial_constraints(self):
        return [self >= 0, self <= 3]

    @staticmethod
    def name(val: int) -> str:
        # page 10, v-spec-1.0
        assert 0 <= val <= 3
        return ["e8", "e16", "e32", "e64"][val]


class InstNameEnum(Enum):
    @staticmethod
    def _generate_next_value_(name, start, count, last_values):
        return count

    ADDI = auto()
    SLLI = auto()
    SRLI = auto()
    VLE8_V = auto()
    VLE16_V = auto()
    VLE32_V = auto()
    VLE64_V = auto()
    VSE8_V = auto()
    VSE16_V = auto()
    VSE32_V = auto()
    VSE64_V = auto()
    VADD_VV = auto()
    VMUL_VV = auto()
    VSUB_VV = auto()
    Count = auto()


class InstName(Variable):
    @staticmethod
    def name(val: int) -> str:
        return str(InstNameEnum(val).name).lower().replace("_", ".")


Arg: TypeAlias = Variable | str


class Inst:
    name: Arg
    args: List[Arg] = []

    def __init__(self, name: Arg, *args: Arg):
        self.name = name
        self.args = list(args)

    def disassembly(self, vals: List[int]) -> str:
        if isinstance(self.name, InstName):
            assert len(vals) == len(self.args) + 1
            name = self.name.name(int(vals[0]))
            vals = vals[1:]
        else:
            assert len(vals) == len(self.args)
            name = self.name
        return f"{name:8} {', '.join([(arg.name(vals[i]) if isinstance(arg, Variable) else arg) for i, arg in enumerate (self.args)])}"

    @staticmethod
    def make(*args: Arg):
        return Inst(args[0], *args[1:])
