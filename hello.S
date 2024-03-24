# PROLOG: Initialize all GPRs to zero
    .section .text.init
    .align  6
    .globl _start
_start:
    j        reset_vector
    .align 2
reset_vector:
    li       x1, 0
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


run:


# RESET: nothing to do in reset stage

    addi     x2, x3, 1
    srli     x2, x3, 16
# RESET: nothing to do in reset stage

    addi     x1, x2, 4
    slli     x1, x2, 12
# RESET: nothing to do in reset stage

    addi     x1, x2, 4
    srli     x1, x2, 12
# RESET: nothing to do in reset stage

    addi     x1, x2, 4
    slli     x1, x2, 8
# RESET: nothing to do in reset stage

    addi     x1, x2, 4
    slli     x1, x2, 16
# RESET: nothing to do in reset stage

    addi     x1, x2, 4
    srli     x1, x2, 16
# RESET: nothing to do in reset stage

    addi     x1, x2, 2
    slli     x1, x2, 16
# RESET: nothing to do in reset stage

    addi     x1, x2, 2
    slli     x1, x2, 8
# RESET: nothing to do in reset stage

    addi     x1, x2, 1
    slli     x1, x2, 8
# RESET: nothing to do in reset stage

    addi     x1, x2, 1
    srli     x1, x2, 8
# RESET: nothing to do in reset stage

    addi     x1, x2, 1
    slli     x1, x2, 12
# RESET: nothing to do in reset stage

    addi     x1, x2, 2
    slli     x1, x2, 12
# RESET: nothing to do in reset stage

    addi     x1, x2, 2
    srli     x1, x2, 12
# RESET: nothing to do in reset stage

    addi     x1, x2, 2
    srli     x1, x2, 8
# RESET: nothing to do in reset stage

    addi     x1, x2, 3
    srli     x1, x2, 8
# RESET: nothing to do in reset stage

    addi     x1, x2, 4
    srli     x1, x2, 8
# RESET: nothing to do in reset stage

    addi     x1, x2, 2
    srli     x1, x2, 16
# RESET: nothing to do in reset stage

    addi     x1, x2, 3
    srli     x1, x2, 16
# RESET: nothing to do in reset stage

    addi     x1, x2, 1
    srli     x1, x2, 16
# RESET: nothing to do in reset stage

    addi     x1, x2, 3
    slli     x1, x2, 16
# RESET: nothing to do in reset stage

    addi     x1, x2, 1
    slli     x1, x2, 16
# RESET: nothing to do in reset stage

    addi     x1, x2, 3
    slli     x1, x2, 12
# RESET: nothing to do in reset stage

    addi     x1, x2, 3
    slli     x1, x2, 8
# RESET: nothing to do in reset stage

    addi     x1, x2, 3
    srli     x1, x2, 12
# RESET: nothing to do in reset stage

    addi     x1, x2, 1
    srli     x1, x2, 12
# RESET: nothing to do in reset stage

    addi     x2, x3, 4
    srli     x2, x3, 16
# RESET: nothing to do in reset stage

    addi     x2, x3, 2
    srli     x2, x3, 16
# RESET: nothing to do in reset stage

    addi     x2, x3, 4
    srli     x2, x3, 12
# RESET: nothing to do in reset stage

    addi     x2, x3, 2
    srli     x2, x3, 12
# RESET: nothing to do in reset stage

    addi     x2, x3, 4
    slli     x2, x3, 12
# RESET: nothing to do in reset stage

    addi     x2, x3, 2
    slli     x2, x3, 12
# RESET: nothing to do in reset stage

    addi     x2, x3, 4
    slli     x2, x3, 16
# RESET: nothing to do in reset stage

    addi     x2, x3, 4
    slli     x2, x3, 8
# RESET: nothing to do in reset stage

    addi     x2, x3, 2
    slli     x2, x3, 8
# RESET: nothing to do in reset stage

    addi     x2, x3, 4
    srli     x2, x3, 8
# RESET: nothing to do in reset stage

    addi     x2, x3, 2
    srli     x2, x3, 8
# RESET: nothing to do in reset stage

    addi     x2, x3, 2
    slli     x2, x3, 16
# RESET: nothing to do in reset stage

    addi     x2, x3, 3
    srli     x2, x3, 12
# RESET: nothing to do in reset stage

    addi     x2, x3, 1
    srli     x2, x3, 12
# RESET: nothing to do in reset stage

    addi     x2, x3, 3
    srli     x2, x3, 16
# RESET: nothing to do in reset stage

    addi     x2, x3, 3
    srli     x2, x3, 8
# RESET: nothing to do in reset stage

    addi     x2, x3, 1
    srli     x2, x3, 8
# RESET: nothing to do in reset stage

    addi     x2, x3, 3
    slli     x2, x3, 12
# RESET: nothing to do in reset stage

    addi     x2, x3, 1
    slli     x2, x3, 12
# RESET: nothing to do in reset stage

    addi     x2, x3, 3
    slli     x2, x3, 16
# RESET: nothing to do in reset stage

    addi     x2, x3, 1
    slli     x2, x3, 16
# RESET: nothing to do in reset stage

    addi     x2, x3, 3
    slli     x2, x3, 8
# RESET: nothing to do in reset stage

    addi     x2, x3, 1
    slli     x2, x3, 8
# RESET: nothing to do in reset stage

# EPILOG: Exit
    li       a0, 0
    li       a7, 93
    ecall


