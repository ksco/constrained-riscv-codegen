init_gprs = """li       x1, 0
    li       x2, 0
    li       x3, 0
    li       x4, 0
    li       x5, 0
    li       x6, 0
    li       x7, 0
    li       x8, 0
    li       x9, 0
    li       x10, 0
    li       x11, 0
    li       x12, 0
    li       x13, 0
    li       x14, 0
    li       x15, 0
    li       x16, 0
    li       x17, 0
    li       x18, 0
    li       x19, 0
    li       x20, 0
    li       x21, 0
    li       x22, 0
    li       x23, 0
    li       x24, 0
    li       x25, 0
    li       x26, 0
    li       x27, 0
    li       x28, 0
    li       x29, 0
    li       x30, 0
    li       x31, 0
"""

disable_multicore = """csrr a0, mhartid
1:  bnez     a0, 1b
"""

default_machine_prolog = f"""# PROLOG: Initialize all GPRs to zero
    .section .text.init
    .align  6
    .globl _start
_start:
    j        reset_vector
    .align 2
reset_vector:
    {init_gprs}

run:
"""

default_machine_epilog = """# EPILOG: Exit
    li       a0, 0
    li       a7, 93
    ecall
"""
default_machine_reset = "# RESET: nothing to do in reset stage"
