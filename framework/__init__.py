from typing import Set, List, Optional
from argparse import ArgumentParser, Namespace
from recipes.branch import branch
from recipes.hello import hello
from recipes.rvv_integer_chaining_basic import rvv_integer_chaining_basic

from .recipe import Recipe, RecipeMeta
import framework.templates.basic as basic
import framework.templates.t1 as t1

registered_recipes: List[Recipe] = [
    Recipe(
        hello,
        {"name": "hello", "desc": "Hello world recipe as an simple example of the API."}
        | basic.template,
    ),
    Recipe(
        branch,
        {"name": "branch", "desc": "Demonstrate how branches works."} | basic.template,
    ),
    Recipe(
        rvv_integer_chaining_basic,
        {
            "name": "rvv_integer_chaining_basic_t1",
            "desc": "Basic RISC-V Vector integer chaining test for the t1 project.",
        }
        | t1.template,
    ),
]


def check_registered_recipes():
    names: Set[str] = set()
    for r in registered_recipes:
        if r.meta["name"] in names:
            assert (
                False
            ), 'Trying to register recipes with the same name: {r.meta["name"]}'
        names.add(r.meta["name"])


def list_all_recipes(_: Namespace):
    res: str = ""
    for r in registered_recipes:
        res += r.meta["name"] + "\n"
        res += "    " + ("\n    ".join(r.meta["desc"].split("\n"))) + "\n"
    return res


def generate_recipe(namespace: Namespace):
    found_recipe: Optional[Recipe] = None
    for r in registered_recipes:
        if namespace.name == r.meta["name"]:
            found_recipe = r

    if found_recipe is None:
        assert (
            False
        ), f"Recipe {namespace.name} not found, are you sure it's registered?"

    found_recipe.func(found_recipe)
    return found_recipe.output()


def initialize_cli():
    parser: ArgumentParser = ArgumentParser(
        description="Constrained RISC-V code generator."
    )
    subparsers = parser.add_subparsers(help="Supported sub commands")
    subparser_list = subparsers.add_parser(
        "list",
        help="List all the recipes",
    )
    subparser_list.set_defaults(func=list_all_recipes)

    subparser_generate = subparsers.add_parser(
        "generate", help="Generate an Assembly file using specified recipe"
    )
    subparser_generate.set_defaults(func=generate_recipe)

    subparser_generate.add_argument(
        "--name", help="Specify a recipe name to generate", required=True
    )
    subparser_generate.add_argument(
        "--filename",
        help="Write the result into a file instead of stdout",
        default=None,
    )

    args: Namespace = parser.parse_args()
    if "func" not in args:
        parser.print_usage()
        parser.exit()
    res = args.func(args)
    if "filename" in args and args.filename is not None:
        with open(args.filename, "w") as file:
            file.write(res)
    else:
        print(res)
