from __future__ import annotations
from typing import Callable, TypedDict, List, Set
import z3

from .inst import Arg, Variable, Inst

RecipeMeta = TypedDict(
    "RecipeMeta",
    {"name": str, "desc": str, "prolog": str, "epilog": str, "reset": str},
)

RecipeMeta.runtime_check = (
    lambda m: isinstance(m["name"], str)
    and isinstance(m["desc"], str)
    and isinstance(m["prolog"], str)
    and isinstance(m["epilog"], str)
    and isinstance(m["reset"], str)
)


class Recipe:
    func: Callable[[Recipe], None] = lambda r: None
    meta: RecipeMeta = {}
    instructions: List[Inst] = []
    vars: Set[Variable] = set()
    solver: z3.Solver = z3.Solver()

    def __init__(self, func: Callable[[Recipe], None], meta: RecipeMeta):
        self.func = func
        self.meta = meta
        RecipeMeta.runtime_check(self.meta)

    def __lshift__(self, e: Inst | Variable | z3.BoolRef | List[z3.BoolRef]):
        if isinstance(e, Inst):
            self.instructions.append(e)
        elif isinstance(e, Variable):
            self.vars.add(e)
        elif isinstance(e, z3.BoolRef):
            self.solver.add(e)
        elif isinstance(e, list):
            if all(isinstance(ee, z3.BoolRef) for ee in e):
                for ee in e:
                    self.solver.add(ee)
            else:
                assert False, "Wrong elements added to the recipe."
        else:
            assert False, "Wrong element added to the recipe."
        return e

    def collect_vars(self) -> Set[Arg]:
        s = set()
        s.update(
            inst.name for inst in self.instructions if isinstance(inst.name, Variable)
        )
        s.update(
            arg
            for inst in self.instructions
            for arg in inst.args
            if isinstance(arg, Variable)
        )
        return s

    def solve(self):
        collected_vars: Set[Arg] = self.collect_vars()
        if collected_vars != self.vars:
            assert (
                False
            ), "Variables in instructions are not matched to the declared ones."

        while self.solver.check() == z3.sat:
            model = self.solver.model()
            res: str = ""
            for inst in self.instructions:
                vals = (
                    [int(model[inst.name].as_signed_long())]
                    if isinstance(inst.name, Variable)
                    else []
                ) + [int(model[arg].as_signed_long()) for arg in inst.args]
                res += "    " + inst.disassembly(vals) + "\n"
            yield res
            self.solver.add(
                z3.Or([f() != model[f] for f in model.decls() if f.arity() == 0])
            )

    def output(self):
        res: str = ""
        res += self.meta["prolog"] + "\n\n"
        for case in self.solve():
            res += self.meta["reset"] + "\n\n"
            res += case
        res += self.meta["reset"] + "\n\n"
        res += self.meta["epilog"] + "\n\n"
        return res
