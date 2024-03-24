from framework.recipe import Recipe
from framework.inst import Inst, Imm, GPR, InstName, InstNameEnum
from z3 import *


# noinspection PyStatementEffect
def hello(r: Recipe):
    imm1 = r << Imm("imm1", 12)
    imm2 = r << Imm("imm2", 6)
    reg1 = r << GPR("reg1", 5)
    reg2 = r << GPR("reg2", 5)
    shift1 = r << InstName("shift1", 16)

    r << [
        imm1 < 5,
        imm1 > 0,
        imm2 >= 8,
        imm2 <= 16,
        imm2 % 4 == 0,
        reg2 == reg1 + 1,
        Or(reg1 == 1, reg1 == 2),
        Or(shift1 == InstNameEnum.SLLI.value, shift1 == InstNameEnum.SRLI.value)
    ]

    r << Inst.make("addi", reg1, reg2, imm1)
    r << Inst.make(shift1, reg1, reg2, imm2)
