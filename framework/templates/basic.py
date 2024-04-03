from .common import init_gprs, disable_multicore

# Simple userspace template
template = {
    "prolog": f"""    #### Generated using trivial template ####

    # PROLOG: Initialize all GPRs to zero
    .section .text.init
    .align  6
    .globl _start
_start:
    j reset_vector
    .align 2
reset_vector:
    {init_gprs}
    {disable_multicore}
run:
""",
    "epilog": """    # EPILOG: User mode exit
    li a0, 0
    li a7, 93
    ecall
""",
    "reset": "",
}
