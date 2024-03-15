from codegen import *
from z3 import *

k = Kernel()

imm1 = k.imm12("imm1")
imm2 = k.imm13("imm2")
reg1 = k.gpr("reg1")
reg2 = k.gpr("reg2")
name = k.name("name")

k.add_constraints(imm1 < 5, imm1 > 0)
k.add_constraints(imm2 >= 8, imm2 <= 16, imm2 % 4 == 0)
k.add_constraints(reg2 == reg1 + 1)
k.add_constraints(Or(reg1 == 0, reg1 == 1))
k.add_constraints(Or(name == Name.BEQ.value, name == Name.BNE.value))

k.addi(reg1, reg2, imm1)
k.btype(name, reg1, reg2, imm2)
k.addi(reg1, reg2, imm1)
k.addi(reg1, reg2, imm1)
k.addi(reg1, reg2, imm1)


for case in k.solve():
    print(case)
    print("-----")
