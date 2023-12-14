from pysat.solvers import Solver
from pysat.formula import IDPool
from itertools import product
from itertools import permutations

def var(ids, func, args, d):
    return ids.id(f"x_{func}[{args}]={d}")

# relaxation variable for strict inequalities in minimal model constraints
def relax(ids, pi, cell):
    args = ','.join(str(arg) for arg in cell)
    return ids.id(f"r_{pi}_[{args}]")

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

    # axiom: for all x,y,z (f(f(x, y), z) = f(x, f(y, z)))
    for args in product(rng, repeat = 6):
        x, y, z, w1, w2, w3 = args[0], args[1], args[2], args[3], args[4], args[5]
        clauses += [[func(ids, ['f', [w1, z], w3]),
                     func(ids, ['-f', [x, w2], w3]),
                     func(ids, ['-f', [x, y], w1]),
                     func(ids, ['-f', [y, z], w2])]]

    return clauses

# returns the set of values larger than d under given pi
def larger_set(pi, d, s):
    return {d2 for d2 in range(s) if pi[d2] > d}

# substitute "one cell is strictly smaller than other" constraint with relaxation variable
def substitue(ids, pi, cell, s):
    clauses = []
    r = -relax(ids, pi, cell)
    clauses += [[r, func(ids, ['-f', cell, d])] + [func(ids, ['f', [pi.index(arg) for arg in cell], d2]) for d2 in larger_set(pi, d, s)] for d in range(s)]

    return clauses

def less_or_equal(ids, pi, visited, args, s):
    rng = range(s)
    clauses = []
    r = [relax(ids, pi, cell) for cell in visited]
    clauses += [r + [func(ids, ['-f', args, d]), func(ids, ['f', [pi.index(arg) for arg in args], pi.index(d)])] for d in rng]
    clauses += [r + [func(ids, ['f', args, d]), func(ids, ['-f', [pi.index(arg) for arg in args], pi.index(d)])] for d in rng]
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

def minimal(ids, s, nonabelian):
    clauses = []
    rng = range(s)

    if nonabelian:
        clauses += not_abelian(ids, s)

    for pi in permutations(rng):
        # skip identity permutation
        if (pi == tuple([i for i in rng])):
            continue

        for args in product(rng, repeat = 2):
            clauses += substitue(ids, pi, [arg for arg in args], s)

        # traverse cells by layers
        visited = []
        for layer in rng:
            for i in range(layer):
                visited.append([i, layer])
                clauses += less_or_equal(ids, pi, visited, [i, layer], s)

                visited.append([layer, i])
                clauses += less_or_equal(ids, pi, visited, [layer, i], s)
            visited.append([layer, layer])
            clauses += less_or_equal(ids, pi, visited, [layer, layer], s)

    return clauses

def semigroup(s):
    ids = IDPool()
    clauses = []
    clauses += encode(ids, s)

    m = minimal(ids, s, False)
    #print_cnf(ids, m)
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

semigroup(6)
