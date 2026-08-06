"""Probe: within-round termination of the pencil refine loop (F2).

Elements of L(1,2) over F2: dict{(a,b):1} for monomials S(a)T(b), words tuples.
Round loop on a narrow unit v:
  pencil over (row-code, col-code) starting at uniform level n;
  T1: B-stack full col rank  -> STOP (window kill, v in H)
  T2: A-stack full row rank  -> STOP (mirror)
  ker[B0;B1;C] != 0          -> STOP (tau-extraction available)
  coker(A0|A1|C) != 0        -> STOP (sigma-extraction available)
  else: right-GL so some CODE column is B-free, refine it (children);
        mirror on rows alternately.  Count refinements until stop.
"""
import random, itertools

def red(a, b):  # T(b)S(a)-collapse sign: returns None or (a', b') with S(a')T(b') = S? no:
    pass

def mul_mono(m1, m2):
    (a, b), (c, d) = m1, m2
    # S(a)T(b) * S(c)T(d)
    if len(b) <= len(c):
        if c[:len(b)] == b:
            e = c[len(b):]
            return (a + e, d)
        return None
    else:
        if b[:len(c)] == c:
            e = b[len(c):]
            return (a, d + e)
        return None

def mul(x, y):
    out = {}
    for m1 in x:
        for m2 in y:
            m = mul_mono(m1, m2)
            if m is not None:
                out[m] = out.get(m, 0) ^ 1
    return {m: 1 for m, c in out.items() if c}

def add(x, y):
    out = dict(x)
    for m in y:
        out[m] = out.get(m, 0) ^ 1
    return {m: 1 for m, c in out.items() if c}

ONE = {((), ()): 1}

def S(w): return {(tuple(w), ()): 1}
def T(w): return {((), tuple(w)): 1}

def window(x):
    degs = [len(a) - len(b) for (a, b) in x]
    return (min(degs), max(degs)) if degs else (0, 0)

def depth(x):
    return max([max(len(a), len(b)) for (a, b) in x], default=0)

# --- random narrow units: products of H-generators, filtered narrow ---
def rand_word(maxlen):
    return tuple(random.randint(0, 1) for _ in range(random.randint(0, maxlen)))

def incomparable(a, b):
    return a[:len(b)] != b and b[:len(a)] != a

def rand_unit_factor():
    t = random.random()
    if t < 0.45:  # incomparable unipotent 1 + S(a) x T(b), x = word-monomial
        while True:
            a, b = rand_word(2), rand_word(2)
            if a and b and incomparable(a, b):
                break
        x = {(rand_word(1), rand_word(1)): 1}
        n = mul(mul(S(a), x), T(b))
        return add(ONE, n), add(ONE, {m: 1 for m in n})  # inverse = 1 - n = 1 + n over F2
    elif t < 0.75:  # cylinder transposition-ish code swap on incomparable a,b (self-inverse)
        while True:
            a, b = rand_word(2), rand_word(2)
            if a and b and incomparable(a, b):
                break
        pa = mul(S(a), T(a)); pb = mul(S(b), T(b))
        u = add(add(add(add(ONE, pa), pb), mul(S(a), T(b))), mul(S(b), T(a)))
        return u, u
    else:  # rho-style code change {0<-00, 11<-01, 10<-1}
        u = add(add(mul(S((0,)), T((0, 0))), mul(S((1, 1)), T((0, 1)))),
                mul(S((1, 0)), T((1,))))
        ui = add(add(mul(S((0, 0)), T((0,))), mul(S((0, 1)), T((1, 1)))),
                 mul(S((1,)), T((1, 0))))
        return (u, ui) if random.random() < 0.5 else (ui, u)

def rand_narrow_unit(nf=4, tries=200):
    for _ in range(tries):
        v = ONE
        for _ in range(nf):
            f, _ = rand_unit_factor()
            v = mul(v, f)
        lo, hi = window(v)
        if -1 <= lo and hi <= 1 and v != ONE and depth(v) <= 4:
            return v
    return None

# --- pencil over (row words R, col words C) ---
GENS = {"t0": ((), (0,)), "t1": ((), (1,)), "one": ((), ()),
        "s0": ((0,), ()), "s1": ((1,), ())}

def entry(v, i, j):
    e = mul(mul(T(i), v), S(j))
    coef = {}
    for m in e:
        for g, gm in GENS.items():
            if m == gm:
                coef[g] = 1
                break
        else:
            return None  # not pencil-legal
    return coef

def pencil(v, R, C):
    E = {}
    for i in R:
        for j in C:
            c = entry(v, i, j)
            if c is None:
                return None
            E[(i, j)] = c
    return E

def rank_f2(rows):
    rows = [r[:] for r in rows]
    rank, ncols = 0, (len(rows[0]) if rows else 0)
    piv = 0
    for col in range(ncols):
        for r in range(rank, len(rows)):
            if rows[r][col]:
                rows[rank], rows[r] = rows[r], rows[rank]
                for r2 in range(len(rows)):
                    if r2 != rank and rows[r2][col]:
                        rows[r2] = [x ^ y for x, y in zip(rows[r2], rows[rank])]
                rank += 1
                break
    return rank

def stack_cols(E, R, C, keys):
    # matrix rows: for each (key,i) a row over C
    return [[E[(i, j)].get(k, 0) for j in C] for k in keys for i in R]

def kernel_vec(rows, ncols):
    # returns a nonzero kernel vector of the column space (rows = stacked rows) or None
    import copy
    m = [r[:] for r in rows]
    pivots = {}
    rank = 0
    for col in range(ncols):
        for r in range(rank, len(m)):
            if m[r][col]:
                m[rank], m[r] = m[r], m[rank]
                for r2 in range(len(m)):
                    if r2 != rank and m[r2][col]:
                        m[r2] = [x ^ y for x, y in zip(m[r2], m[rank])]
                pivots[col] = rank
                rank += 1
                break
    free = [c for c in range(ncols) if c not in pivots]
    if not free:
        return None
    f = free[0]
    vec = [0] * ncols
    vec[f] = 1
    for c, r in pivots.items():
        if m[r][f]:
            vec[c] = 1
    return vec

def col_gl(v, C, vec):
    # right-multiply v by the unit g = embed(G) where G mixes columns so that
    # column j0 (a chosen pivot of vec) becomes the kernel combination.
    # Over F2: g = 1 + sum_{j != j0, vec_j = 1} S(j) T(j0)  (adds col j into col j0)
    j0 = None
    for j, x in zip(C, vec):
        if x:
            j0 = j
            break
    g = dict(ONE)
    ginv = dict(ONE)
    for j, x in zip(C, vec):
        if x and j != j0:
            g = add(g, mul(S(j), T(j0)))
            ginv = add(ginv, mul(S(j), T(j0)))  # self-inverse over F2 (nilpotent square-0? check)
    return mul(v, g), j0

def loop_round(v, n0=None, max_ref=60, verbose=False):
    lo, hi = window(v)
    assert -1 <= lo and hi <= 1
    n = max(depth(v), 1) if n0 is None else n0
    R = [tuple(w) for w in itertools.product((0, 1), repeat=n)]
    C = list(R)
    steps = 0
    side = 0
    while steps <= max_ref:
        E = pencil(v, R, C)
        if E is None:
            return ("ILLEGAL", steps)
        # T1: B-stack full column rank?
        b_stack = stack_cols(E, R, C, ["s0", "s1"])
        if kernel_vec(b_stack, len(C)) is None:
            return ("T1", steps)
        # T2: A-stack full row rank <-> transpose-stack over rows full "column" rank
        a_stack = [[E[(i, j)].get(k, 0) for i in R] for k in ["t0", "t1"] for j in C]
        if kernel_vec(a_stack, len(R)) is None:
            return ("T2", steps)
        # extraction available?
        bc = stack_cols(E, R, C, ["s0", "s1", "one"])
        kv = kernel_vec(bc, len(C))
        if kv is not None:
            return ("EXTRACT-t", steps)
        ac = [[E[(i, j)].get(k, 0) for i in R] for k in ["t0", "t1", "one"] for j in C]
        kw = kernel_vec(ac, len(R))
        if kw is not None:
            return ("EXTRACT-s", steps)
        # refine: pick a kernel vector of the B-stack, GL it into a code column, split
        if side == 0:
            vec = kernel_vec(b_stack, len(C))
            v, j0 = col_gl(v, C, vec)
            C = [j for j in C if j != j0] + [j0 + (0,), j0 + (1,)]
        else:
            vec = kernel_vec(a_stack, len(R))
            # row-GL: left-multiply: g = 1 + sum S(i0) T(i) adding row i into i0
            i0 = None
            for i, x in zip(R, vec):
                if x:
                    i0 = i
                    break
            g = dict(ONE)
            for i, x in zip(R, vec):
                if x and i != i0:
                    g = add(g, mul(S(i0), T(i)))
            v = mul(g, v)
            R = [i for i in R if i != i0] + [i0 + (0,), i0 + (1,)]
        side ^= 1
        steps += 1
        if verbose:
            print(f"  step {steps}: |R|={len(R)} |C|={len(C)}")
    return ("MAXREF", steps)

if __name__ == "__main__":
    random.seed(7)
    from collections import Counter
    results = Counter()
    worst = 0
    for trial in range(120):
        v = rand_narrow_unit(nf=random.randint(2, 5))
        if v is None:
            continue
        out, steps = loop_round(v)
        results[out] += 1
        worst = max(worst, steps)
        if out in ("MAXREF", "ILLEGAL"):
            print("PROBLEM:", out, "unit:", sorted(v)[:8], "...")
    print(results, "worst refinement count:", worst)

# ---------------------------------------------------------------------------
# Session 54 instrumentation: classify the doubly-deficient (case-4) events.
# At each refinement step record the stack ranks, and test the batch-refine
# conjecture: some u0 in coker[A0|A1] is also orthogonal to the C-columns of
# the B-spanned column set J_B  (equivalently, row extraction fires after
# batch-refining every kernel column).
def left_kernel_vec(rows, ncols):
    return kernel_vec(rows, ncols)

def case4_probe(trials=400, seed=11):
    random.seed(seed)
    from collections import Counter
    events = Counter()
    conj_fail = 0
    case4_total = 0
    for trial in range(trials):
        v = rand_narrow_unit(nf=random.randint(2, 5))
        if v is None:
            continue
        n = max(depth(v), 1)
        R = [tuple(w) for w in itertools.product((0, 1), repeat=n)]
        C = list(R)
        steps = 0
        while steps <= 40:
            E = pencil(v, R, C)
            if E is None:
                events["ILLEGAL"] += 1
                break
            b_stack = stack_cols(E, R, C, ["s0", "s1"])
            bker = kernel_vec(b_stack, len(C))
            a_stack = [[E[(i, j)].get(k, 0) for i in R]
                       for k in ["t0", "t1"] for j in C]
            aker = kernel_vec(a_stack, len(R))
            if bker is None and aker is None:
                events["TERMINAL(both full)"] += 1
                break
            if bker is None:
                events["case3(B full, A def)"] += 1
                break
            if aker is None:
                events["case2(B def, A full)"] += 1
                break
            # both deficient: extraction?
            bc = stack_cols(E, R, C, ["s0", "s1", "one"])
            if kernel_vec(bc, len(C)) is not None:
                events["EXTRACT-t"] += 1
                break
            ac = [[E[(i, j)].get(k, 0) for i in R]
                  for k in ["t0", "t1", "one"] for j in C]
            if kernel_vec(ac, len(R)) is not None:
                events["EXTRACT-s"] += 1
                break
            # genuine case 4
            case4_total += 1
            events[f"case4@step{steps}"] += 1
            # conjecture test: batch-refine all kernel columns of [B0;B1],
            # i.e. find J_B = a complement of ker restricted... over F2 we
            # compute ker basis, normalize columns so kernel = coordinate
            # subspace, then ask: exists u0 with u0^T [A0|A1] = 0 and
            # u0^T C(.,j) = 0 for all j in J_B.
            # kernel basis of b_stack:
            m = [r[:] for r in b_stack]
            pivots = {}
            rank = 0
            for col in range(len(C)):
                for r in range(rank, len(m)):
                    if m[r][col]:
                        m[rank], m[r] = m[r], m[rank]
                        for r2 in range(len(m)):
                            if r2 != rank and m[r2][col]:
                                m[r2] = [x ^ y for x, y in zip(m[r2], m[rank])]
                        pivots[col] = rank
                        rank += 1
                        break
            JB = sorted(pivots)  # pivot columns: B-spanned complement
            # rows over R of the test stack: columns of A on ALL j, plus C on JB
            test_rows = [[E[(i, j)].get(k, 0) for i in R]
                         for k in ["t0", "t1"] for j in range(len(C))
                         for j in [C[j]]]
            test_rows += [[E[(i, C[j])].get("one", 0) for i in R] for j in JB]
            if kernel_vec(test_rows, len(R)) is None:
                conj_fail += 1
                events[f"CONJ-FAIL@step{steps}"] += 1
            # refine one kernel column (as before) and continue
            v, j0 = col_gl(v, C, bker)
            C = [j for j in C if j != j0] + [j0 + (0,), j0 + (1,)]
            steps += 1
    print(dict(events))
    print("case4 events:", case4_total, "conjecture failures:", conj_fail)


def rank_evolution_probe(trials=400, seed=11):
    """At each case-4 refinement, record whether rank[B0;B1] strictly grew
    and whether dim ker[B0;B1] (= |C| - rank) changed."""
    random.seed(seed)
    from collections import Counter
    ev = Counter()
    chains = []
    for trial in range(trials):
        v = rand_narrow_unit(nf=random.randint(2, 5))
        if v is None:
            continue
        n = max(depth(v), 1)
        R = [tuple(w) for w in itertools.product((0, 1), repeat=n)]
        C = list(R)
        steps = 0
        chain = []
        while steps <= 40:
            E = pencil(v, R, C)
            if E is None:
                break
            b_stack = stack_cols(E, R, C, ["s0", "s1"])
            rB = rank_f2(b_stack and [list(col) for col in zip(*b_stack)] or [])
            # rank of the stack as a matrix rows=2|R| cols=|C|:
            rB = rank_f2(b_stack) if b_stack else 0
            a_stack = [[E[(i, j)].get(k, 0) for i in R]
                       for k in ["t0", "t1"] for j in C]
            rA = rank_f2(a_stack) if a_stack else 0
            bker = kernel_vec(b_stack, len(C))
            aker = kernel_vec(a_stack, len(R))
            if bker is None or aker is None:
                break
            bc = stack_cols(E, R, C, ["s0", "s1", "one"])
            if kernel_vec(bc, len(C)) is not None:
                break
            ac = [[E[(i, j)].get(k, 0) for i in R]
                  for k in ["t0", "t1", "one"] for j in C]
            if kernel_vec(ac, len(R)) is not None:
                break
            chain.append((len(R), len(C), rB, rA,
                          len(C) - rB, len(R) - rA))
            v, j0 = col_gl(v, C, bker)
            C = [j for j in C if j != j0] + [j0 + (0,), j0 + (1,)]
            steps += 1
        if len(chain) >= 2:
            chains.append(chain)
            for a, b in zip(chain, chain[1:]):
                dRank = b[2] - a[2]
                dKer = b[4] - a[4]
                ev[f"dRankB={dRank},dKerB={dKer}"] += 1
    print(dict(ev))
    for ch in chains[:6]:
        print(ch)


def stall_probe(trials=3000, seed=23):
    """Big sweep: chain lengths, consecutive stalls, and candidate measures
    along column-only case-4 refinement chains."""
    random.seed(seed)
    from collections import Counter
    ev = Counter()
    maxchain, maxstall = 0, 0
    badrows = []
    for trial in range(trials):
        v = rand_narrow_unit(nf=random.randint(2, 6))
        if v is None:
            continue
        n = max(depth(v), 1)
        R = [tuple(w) for w in itertools.product((0, 1), repeat=n)]
        C = list(R)
        steps, stall_run, prev_rB = 0, 0, None
        chain = []
        while steps <= 60:
            E = pencil(v, R, C)
            if E is None:
                ev["ILLEGAL"] += 1
                break
            b_stack = stack_cols(E, R, C, ["s0", "s1"])
            rB = rank_f2(b_stack) if b_stack else 0
            bker = kernel_vec(b_stack, len(C))
            a_stack = [[E[(i, j)].get(k, 0) for i in R]
                       for k in ["t0", "t1"] for j in C]
            aker = kernel_vec(a_stack, len(R))
            if bker is None or aker is None:
                ev["KILL"] += 1
                break
            bc = stack_cols(E, R, C, ["s0", "s1", "one"])
            if kernel_vec(bc, len(C)) is not None:
                ev["EXT-t"] += 1
                break
            ac = [[E[(i, j)].get(k, 0) for i in R]
                  for k in ["t0", "t1", "one"] for j in C]
            if kernel_vec(ac, len(R)) is not None:
                ev["EXT-s"] += 1
                break
            if prev_rB is not None:
                if rB == prev_rB:
                    stall_run += 1
                    maxstall = max(maxstall, stall_run)
                else:
                    stall_run = 0
            prev_rB = rB
            chain.append((len(C), rB))
            v, j0 = col_gl(v, C, bker)
            C = [j for j in C if j != j0] + [j0 + (0,), j0 + (1,)]
            steps += 1
        maxchain = max(maxchain, steps)
        if steps >= 6:
            badrows.append((trial, chain))
    print(dict(ev), "maxchain:", maxchain, "maxstall(consecutive):", maxstall)
    for t, ch in badrows[:8]:
        print("long chain trial", t, ch)

