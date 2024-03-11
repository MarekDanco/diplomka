"""Compute the instance-independent canonizing set of permutations."""

from pysat.solvers import Solver
from pysat.formula import IDPool
from basics import pick_one, print_cnf, debug_model
from itertools import product


def var(ids, sign, op, args, d):
    """Propositional variable for equality of terms."""
    rv = ids.id(f"{op}_{args}={d}")
    return rv if sign else -rv


def perm(ids, s):
    """CNF encoding for a permutation."""
    rng = range(s)
    clauses = []
    for i in rng:
        clauses += pick_one([var(ids, True, "pi", i, d) for d in rng])  # 1-hot
    for d in rng:
        clauses += [
            [var(ids, False, "pi", i, d), var(ids, False, "pi", j, d)]
            for i in rng
            for j in rng
            if i < j
        ]  # all different
    return clauses


def rhs(ids, *args):
    return ids.id(f"rhs_{args}")


def sub_rhs(ids, s):
    """Substitute formula on the right-hand side of iso formula with a variable."""
    clauses = []
    for x, i, j, y, k, l in product(range(s), repeat=6):
        clauses += [
            [-rhs(ids, x, i, j, y, k, l), var(ids, True, "pi", y, x)],
            [-rhs(ids, x, i, j, y, k, l), var(ids, True, "pi", k, i)],
            [-rhs(ids, x, i, j, y, k, l), var(ids, True, "pi", l, j)],
            [-rhs(ids, x, i, j, y, k, l), var(ids, True, "a", [k, l], y)],
        ]
        clauses += [
            [
                rhs(ids, x, i, j, y, k, l),
                var(ids, False, "pi", y, x),
                var(ids, False, "pi", k, i),
                var(ids, False, "pi", l, j),
                var(ids, False, "a", [k, l], y),
            ]
        ]
    return clauses


def one_hot(ids, s, alg):
    clauses = []
    rng = range(s)
    for x, y in product(rng, repeat=2):
        clauses += pick_one([var(ids, True, alg, [x, y], d) for d in rng])
    return clauses


def iso(ids, s):
    """Constraints for isomorphism of algebras."""
    rng = range(s)
    clauses = sub_rhs(ids, s)
    clauses += one_hot(ids, s, "a")
    clauses += one_hot(ids, s, "b")
    for x, i, j in product(rng, repeat=3):
        # =>
        clauses += [
            [var(ids, False, "b", [i, j], x)]
            + [rhs(ids, x, i, j, y, k, l) for y, k, l in product(rng, repeat=3)]
        ]
        # <=
        clauses += [
            [var(ids, True, "b", [i, j], x), -rhs(ids, x, i, j, y, k, l)]
            for y, k, l in product(rng, repeat=3)
        ]
    return clauses


"""
def greater(ids, s):
    clauses = []
    rng = range(s)
    for x, i, j in product(rng, repeat=3):
        
    return clauses
"""


def print_table(ids, model, alg, s):
    for x, y in product(range(s), repeat=2):
        for d in range(s):
            if model[var(ids, True, alg, [x, y], d) - 1] > 0:
                print(d, end=" ")
        if y == s - 1:
            print()
    print()


def minimality(ids, s, pi):
    """Constraints for canonizing permutation set."""
    clauses = []
    return clauses


def testme(s):
    ids = IDPool()
    cnf = []

    cnf += perm(ids, s)
    cnf += iso(ids, s)
    # cnf += greater(ids, s)

    solver = Solver(name="lgl", bootstrap_with=cnf)

    perms = []
    while solver.solve():
        model = solver.get_model()
        cl = []  # blocking clause for current permutation
        prm = []  # current permutation
        print_table(ids, model, "a", s)
        print_table(ids, model, "b", s)
        for i, d in product(range(s), repeat=2):
            if model[var(ids, True, "pi", i, d) - 1] > 0:
                cl.append(var(ids, False, "pi", i, d))
                prm.append(d)
        print(prm, "\n")
        solver.add_clause(cl)
        # solver.append_formula(minimality(ids, s, prm))
        perms += [prm]
    print(len(perms))


if __name__ == "__main__":
    testme(4)
