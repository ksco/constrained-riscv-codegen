from framework.recipe import Recipe
from framework.inst import Inst, Imm, GPR, InstName, InstNameEnum, LMUL, SEW, VFR, MEM
from z3 import *

VLEN = 1024
RV32 = True


# noinspection PyStatementEffect
def rvv_integer_chaining_basic(r: Recipe):
    emul = r << LMUL("emul", 6)
    eew = r << SEW("eew", 6)
    vle = r << InstName("vle", 6)
    vse = r << InstName("vse", 6)
    op1 = r << InstName("op1", 6)
    op2 = r << InstName("op2", 6)
    op3 = r << InstName("op3", 6)
    v1 = r << VFR("v1", 6)
    v2 = r << VFR("v2", 6)
    v3 = r << VFR("v3", 6)
    vr1 = r << VFR("vr1", 6)
    vr2 = r << VFR("vr2", 6)
    vr3 = r << VFR("vr3", 6)

    r << [
        vle - InstNameEnum.VLE8_V.value == eew,
        vse - InstNameEnum.VSE8_V.value == eew,
        v1 == If(emul > 4, 1, 1 << emul),
        v2 == v1 * 2,
        v3 == v1 * 3,
        Or(vr1 == v1, vr1 == v2, vr1 == v3),
        Or(vr2 == v1, vr2 == v2, vr2 == v3),
        Or(vr3 == v1, vr3 == v2, vr3 == v3),
        Or(
            op1 == InstNameEnum.VADD_VV.value,
            op1 == InstNameEnum.VMUL_VV.value,
            op1 == InstNameEnum.VSUB_VV.value,
        ),
        Or(
            op2 == InstNameEnum.VADD_VV.value,
            op2 == InstNameEnum.VMUL_VV.value,
            op2 == InstNameEnum.VSUB_VV.value,
        ),
        Or(
            op3 == InstNameEnum.VADD_VV.value,
            op3 == InstNameEnum.VMUL_VV.value,
            op3 == InstNameEnum.VSUB_VV.value,
        ),
    ] + ([eew != 3] if RV32 else [])

    r << Inst.make("la", "a0", "test_data")
    r << Inst.make("la", "a1", "result_data")
    r << Inst.make("li", "t0", "-1")
    r << Inst.make("vsetvli", "t1", "t0", eew, emul, "ta", "ma")
    for idx, vreg in enumerate([v1, v2, v3]):
        if idx > 0:
            r << Inst.make("li", "a2", f"{idx * VLEN}")
            r << Inst.make("add", "a2", "a2", "a0")
        r << Inst.make(vle, vreg, "0(a2)" if idx > 0 else "0(a0)")
    vregs = [vr1, vr2, vr3]
    for idx, op in enumerate([op1, op2, op3]):
        r << Inst.make(op, vregs[idx], vregs[(idx + 1) % 3], vregs[(idx + 2) % 3])
    r << Inst.make(vse, vr3, "0(a1)")
