from .common import init_gprs, disable_multicore, enable_vector

# t1 template
template = {
    "prolog": f"""    #### Generated using t1 template ####

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
    {enable_vector}
run:
""",
    "epilog": """    # EPILOG: Write our custom CSR msimend to exit simulation
    csrwi 0x7cc, 0

    .data
    .align 4
test_data:
    .zero 4096

result_data:
    .zero 1024
""",
    "reset": "",
}
