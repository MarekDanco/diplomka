from pysat.solvers import Solver
from pysat.formula import IDPool
from itertools import product
from itertools import permutations
import sys

def var(ids, func, args, d):
    return ids.id(f"x_{func}[{args}]={d}")

# relaxation variable for "following cells are less or equal"
def relax(ids, pi, i):
    return ids.id(f"r_{pi}_{i}")

# relaxation variable for "cell is less than another cell"
def less(ids, pi, cell):
    args = ','.join(str(arg) for arg in cell)
    return ids.id(f"l_{pi}_[{args}]")

# relaxation variable for "cells are equal"
def equal(ids, pi, cell):
    args = ','.join(str(arg) for arg in cell)
    return ids.id(f"e_{pi}_[{args}]")

# returns propositional variable for f(x_1, ..., x_n) = d for arbitrary function symbol f of arbitrary arity > 0
# ['-f', ['x_1', ..., 'x_n'], 'd'] means f(x_1, ..., x_n) != d -> return negated variable
def func(ids, lit):
    f = lit[0]
    sign = True
    if f[0] == '-':
        f = f[1:]
        sign = False
    args = ','.join(str(arg) for arg in lit[1])
    d = str(lit[2])
    ret = var(ids, f, args, d)
    return ret if sign else -ret

# returns propositional variable for a = d for arbitrary constant symbol a
def const(ids, lit):
    a = lit[0]
    sign = True
    if a[0] == '-':
        a = a[1:]
        sign = False
    d = str(lit[1])
    ret = ids.id(f"x_{a}={d}")
    return ret if sign else -ret

# outputs the function table
def out(ids, model, s):
    cl = []
    rng = range(s)

    for x in rng:
        for y in rng:
            for d in rng:
                if model[abs(func(ids, ['f', [x, y], d])) - 1] > 0:
                    cl.append(-func(ids, ['f', [x, y], d]))
                    print(d, end =" ", flush = True) if s < 11 else print(f"{d:2}", end = " ", flush = True)
        print()
    return cl

# exactly one of the lits is true
def pick_one(lits):
    return [lits] + at_most_one(lits)

# at most one of the lits is true
def at_most_one(lits):
    return [[-v1, -v2] for v1 in lits for v2 in lits if v1 < v2]

# encodes first order logic non-abelian group axioms into cnf
def encode(ids, s):
    clauses = []
    rng = range(s)

    # functional + totality definitions of f
    for args in product(rng, repeat = 2):
            clauses += pick_one([func(ids, ['f', [arg for arg in args], d]) for d in rng])

    # functional + totality definitions of g
    for x in rng:
        clauses += pick_one([func(ids, ['g', [x], d]) for d in rng])

    # latin square property of f table
        # columns
    for y in rng:
        for d in rng:
            clauses += at_most_one([func(ids, ['f', [x, y], d]) for x in rng])

        # rows
    for x in rng:
        for d in rng:
            clauses += at_most_one([func(ids, ['f', [x, y], d]) for y in rng])

        # first row = {0, 1, ..., s-1}
    clauses += [[func(ids, ['f', [0, y], y])] for y in rng]

        # first column = {0, 1, ..., s-1}
    clauses += [[func(ids, ['f', [x, 0], x])] for x in rng]

    # "latin square" property of g table
    for d in rng:
        clauses += at_most_one([func(ids, ['g', [x], d]) for x in rng])

    # g(0) = 0
    clauses += [[func(ids, ['g', [0], 0])]]

    # axiom: for all x (f(x, g(x)) = 0 and f(g(x), x) = 0)
    for x in rng:
        for y in rng:
            clauses += [[func(ids, ['f', [x, y], 0]), func(ids, ['-g', [x], y])]]
            clauses += [[func(ids, ['f', [y, x], 0]), func(ids, ['-g', [x], y])]]

    # axiom: for all x,y,z (f(f(x, y), z) = f(x, f(y, z)))
    for args in product(rng, repeat = 6):
        x, y, z, w1, w2, w3 = args[0], args[1], args[2], args[3], args[4], args[5]
        clauses += [[func(ids, ['f', [w1, z], w3]),
                     func(ids, ['-f', [x, w2], w3]),
                     func(ids, ['-f', [x, y], w1]),
                     func(ids, ['-f', [y, z], w2])]]

    return clauses

def not_abelian(ids, s):
    clauses = []
    rng = range(s)

    # functional and totality definitions of constants a, b
    clauses += pick_one([const(ids, ['a', d]) for d in rng])
    clauses += pick_one([const(ids, ['b', d]) for d in rng])

    # axiom: f(a, b) != f(b, a)
    for args in product(rng, repeat = 3):
        x, y, z = args[0], args[1], args[2]
        clauses += [[func(ids, ['-f', [x, y], z]), func(ids, ['-f', [y, x], z]), const(ids, ['-a', x]), const(ids, ['-b', y])]]

    return clauses

# returns the set of values larger than d under given pi
def larger_set(pi, d, s):
    return {d2 for d2 in range(s) if pi[d2] > d}

# substitute "cell is less than another cell"
def sub_l(ids, pi, cell, s):
    clauses = []
    l = -less(ids, pi, cell)
    clauses += [[l, func(ids, ['-f', cell, d])] + [func(ids, ['f', [pi.index(arg) for arg in cell], d2]) for d2 in larger_set(pi, d, s)] for d in range(s)]

    return clauses

# substitute "cells are equal"
def sub_e(ids, pi, cell, s):
    clauses = []
    e = -equal(ids, pi, cell)
    clauses += [[e, func(ids, ['-f', cell, d]), func(ids, ['f', [pi.index(arg) for arg in cell], pi.index(d)])] for d in range(s)]
    clauses += [[e, func(ids, ['f', cell, d]), func(ids, ['-f', [pi.index(arg) for arg in cell], pi.index(d)])] for d in range(s)]

    return clauses

# all transpositions on range(s)
def transps(s):
    tps = []
    id = [i for i in range(s)]

    for i in range(s):
        for j in range(i+1, s):
            tpn = id[:]
            tpn[i], tpn[j] = tpn[j], tpn[i]
            tps.append(tuple(tpn))
    
    return tps

def minimal(ids, s, nonabelian, transpositions, concentric):
    clauses = []
    rng = range(s)

    if nonabelian:
        clauses += not_abelian(ids, s)

    perms = transps(s) if transpositions else permutations(rng)

    cells = [(x, y) for x in range(1, s-1) for y in range(1, s-1)]
    if concentric:
        cells.sort(key=lambda e: max(e[0],e[1]))

    for pi in perms:
        # skip identity permutation and permutations s.t. pi[0] != 0
        if (pi == tuple([i for i in rng])) or (pi[0] != 0):
            continue

        for cell in product(range(1, s-1), repeat=2):
            clauses += sub_l(ids, pi, cell, s)
            clauses += sub_e(ids, pi, cell, s)

        clauses += [[less(ids, pi, [1, 1]), equal(ids, pi, [1, 1])], [less(ids, pi, [1, 1]), relax(ids, pi, 0)]]

        i = -1
        for cell in cells:
            i += 1
            if cell == (1, 1) or cell == (s-2, s-2):
                continue

            r = -relax(ids, pi, i-1)
            l = less(ids, pi, cell)
            e = equal(ids, pi, cell)
            clauses += [[r, l, e], [r, l, relax(ids, pi, i)]]
        # last cell uses relax variable from the second last cell
        clauses += [[-relax(ids, pi, (s-2)**2 - 2), less(ids, pi, [s-2, s-2]), equal(ids, pi, [s-2, s-2])]]

    return clauses

def group():
    ids = IDPool()

    s = int(sys.argv[1])
    nonabelian = int(sys.argv[2])
    transpositions = int(sys.argv[3])
    concentric = int(sys.argv[4])

    clauses = []
    clauses += encode(ids, s)

    m = minimal(ids, s, nonabelian, transpositions, concentric)
    clauses += m

    solver = Solver(name = 'g3', bootstrap_with = clauses)
    counter = 0
    while True:
        counter += 1
        print('===', counter, flush = True)
        if solver.solve():
            model = solver.get_model()
            cl = out(ids, model, s)
            # find a new model
            solver.add_clause(cl)
        else:
            print('unsat')
            break
    return

if __name__ == "__main__":
    group()
