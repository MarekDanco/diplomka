"""Make DIMACS files for an algebra for different domain sizes."""

from itertools import product
from pysat.formula import IDPool, CNF
from basics import var_enc
import argparse
import sys
from parsing import Parser, find_inv, collect, Const, transform
from splitting import Splitting
from grounding import Grounding
from canset import alg1, alg2
from minmod import minimal
import os


def cnf2dimacs(cnf, s, args):
    """Export the computed CNF to simplified DIMACS format."""
    dimacs = CNF(from_clauses=cnf)

    file = f"{args.path}{s}.cnf"
    dimacs.to_file(file)

    rng = range(s)
    proj = " ".join(
        [str(var_enc(s, True, x, y, d)) for x, y, d in product(rng, repeat=3)]
    )

    with open(file, "r") as out:
        lines = out.readlines()

    lines.insert(1, f"c ind {proj} 0\n")

    with open(file, "w") as out:
        out.writelines(lines)
    return


def mkdimacs(data, args):
    p = Parser()
    tree = p.parse(data)
    inverses = find_inv(tree)
    constants = tuple(sorted(collect(tree, Const)))

    flattened = transform(tree)
    split = Splitting().transform(flattened)

    if args.path != "":
        if not os.path.exists(args.path):
            os.mkdir(args.path)
            print(f"Directory '{args.path}' created.")

    for s in range(args.lowbound, args.upbound + 1):
        print("===")
        print(f"making DIMACS for domain size {s}")
        ids = IDPool(occupied=[[1, s**3]])
        cnf = []

        g = Grounding(s, ids)
        cnf += g.ground(split)
        cnf += g.one_hot(constants, inverses)

        p = alg1(ids, cnf, s, args, constants=constants, main=True)
        p = alg2(ids, cnf, s, p, args, main=True)

        cnf += minimal(ids, s, args, perms=p)
        cnf2dimacs(cnf, s, args)
    return


def run_main(inp):
    """Run the whole program."""
    arg_parser = argparse.ArgumentParser()
    arg_parser.add_argument(
        "upbound",
        help="domain upper bound",
        nargs="?",
        type=int,
    )
    arg_parser.add_argument(
        "filename",
        help="filename with input formula",
        default="-",
        nargs="?",
        type=str,
    )
    arg_parser.add_argument(
        "-p",
        "--path",
        help="path to the output directory, output here by default",
        default="",
        nargs="?",
        type=str,
    )
    arg_parser.add_argument(
        "-l",
        "--lowbound",
        help="domain lower bound",
        nargs="?",
        default=2,
        type=int,
    )
    arg_parser.add_argument("--permutations", default=False)
    arg_parser.add_argument("--transpositions", default=False)
    arg_parser.add_argument("--concentric", default=False)
    arg_parser.add_argument("-lnh", default=False)
    arg_parser.add_argument("--solver", default="cd19")
    args = arg_parser.parse_args()

    if args.filename == "-":
        data = inp
    else:
        with open(args.filename, "r", encoding="utf-8") as infile:
            data = infile.read()
    mkdimacs(data, args)
    return 0


if __name__ == "__main__":
    sys.exit(run_main("."))