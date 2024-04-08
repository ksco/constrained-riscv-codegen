from framework.recipe import Recipe
from framework.inst import Imm, GPR, Nst, Inst, InstName, InstNameEnum
from z3 import *


# noinspection PyStatementEffect
def branch(r: Recipe):
    imm1 = r << Imm("imm1", 5)
    imm2 = r << Imm("imm2", 5)
    branch1 = r << InstName("branch1", 16)
    reg1 = r << GPR("reg1", 5)
    reg2 = r << GPR("reg2", 5)
    label1 = r << Nst("label1", 5)

    r << [
        imm1 < 5,
        imm2 < 6,
        reg2 == reg1 + 1,
        Or(reg1 == 11, reg1 == 12),
        Or(branch1 == InstNameEnum.BEQ.value, branch1 == InstNameEnum.BNE.value),
        Or(label1 == 4, label1 == 5),
    ]

    r << Inst.make("addi", reg1, "zero", imm1)
    r << Inst.make("addi", reg2, "zero", imm2)
    r << Inst.make(branch1, reg1, reg2, label1)
    r << Inst.make("nop")
    r << Inst.make("nop")
