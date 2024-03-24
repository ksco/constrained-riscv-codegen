# constrained-riscv-codegen

**Work in progress**

Generate RISC-V programs based on small recipes, see [recipes/hello.py](recipes/hello.py) as an example:

```python
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
```

As you can see, there are three parts in the recipe. The first part declares the variables to be used next. The variables may be registers, instruction names, or immediate values. The second part adds constraints to the variables. The third part guides the instruction generation.

After having the recipe, our codegen infra will use [z3](https://github.com/Z3Prover/z3) to generate all possible combinations to achieve 100% coverage for the recipe. So you will get something like this:

```assembly
...

addi     x2, x3, 1
srli     x2, x3, 16

addi     x1, x2, 4
slli     x1, x2, 12

addi     x1, x2, 4
srli     x1, x2, 12

...
```



But what's the use of this? Well, if you want to verify the correctness of a specific pattern, you can write a small recipe, then directly generate all possible combinations, and then combine it with cosim to completely verify the pattern.

## Usage

```bash
# List all the recipes
python crv.py list
# Generate program.S using a recipe named hello
python crv.py generate --name hello --filename program.S
```

## TODOs

Too many, I'll make a list when this becomes more mature.
