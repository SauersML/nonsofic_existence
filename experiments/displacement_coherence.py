"""Displacement-coherence feasibility (Heisenberg surrogate), corrected.

Q = Heis(Z/N): (a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab'), N odd.
Flip   thA(a,b,c) = (-a, b, -c).
Shear  thS(a,b,c) = (a-b, b, c - b(b-1)/2)   [minus sign: hom check below].
Two-path invisible element: g = thA(x y) = thS(y z^-1) = (-1, 1, -1).

Ansatz: Z unitary in C := commutant of {lambda(y), lambda(z)} (both frames
carry the <y,z>-web: thA preserves it; Z-transport on it is exact).
D_A := Z thA(Z)*;  E := thS(Z) thA(Z)*.
Coherence defect  Delta := || E lam(g) E* - lam(g) ||_2   (normalized HS).
Mixing absorption alpha := || E_{L(Q)}(D_A lam(x) D_A*) ||_2, the Fourier
mass of the twisted letter on the group algebra: liftable control Z = 1
gives alpha = 1 exactly; mixing survives iff alpha stays well below 1.

Scheme per iteration: project E onto the commutant of lam(g) (average over
<g>-conjugation, unitary polar part), back-solve thS(Z) = Ehat thA(Z) by a
fixed-point step, re-project Z into U(C).
"""

import numpy as np

rng = np.random.default_rng(7)


def upolar(T):
    u, _, vh = np.linalg.svd(T)
    return u @ vh


def run(N, iters=40):
    d = N * N * N
    inv2 = pow(2, -1, N)

    def idx(q):
        return ((q[0] % N) * N + (q[1] % N)) * N + (q[2] % N)

    def unidx(i):
        return (i // (N * N), (i // N) % N, i % N)

    def mul(p, q):
        return ((p[0] + q[0]) % N, (p[1] + q[1]) % N,
                (p[2] + q[2] + p[0] * q[1]) % N)

    def inv(p):
        a, b, c = p
        return ((-a) % N, (-b) % N, (-c + a * b) % N)

    def thA(p):
        return ((-p[0]) % N, p[1], (-p[2]) % N)

    def thS(p):
        a, b, c = p
        return ((a - b) % N, b, (c - b * (b - 1) * inv2) % N)

    def thS_inv(p):
        a, b, c = p
        return ((a + b) % N, b, (c + b * (b - 1) * inv2) % N)

    elems = [unidx(i) for i in range(d)]

    # homomorphism checks
    for th in (thA, thS, thS_inv):
        for p in [(1, 2, 3), (4, 1, 2)]:
            for q in [(2, 0, 1), (1, 1, 1)]:
                assert th(mul(p, q)) == mul(th(p), th(q)), "not a hom"

    x, y, z = (1, 0, 0), (0, 1, 0), (0, 0, 1)
    g = thA(mul(x, y))
    assert g == thS(mul(y, inv(z))), "two-path coincidence failed"
    assert g == ((-1) % N, 1, (-1) % N)

    def left_perm(q):
        """L with (lam(q) T lam(q)^-1)[i,j] = T[L i, L j]; L i = q^-1 i."""
        qi = inv(q)
        L = np.empty(d, dtype=np.int64)
        for i, r in enumerate(elems):
            L[i] = idx(mul(qi, r))
        return L

    def aut_perm(f):
        """P with (pi_f T pi_f^-1)[i,j] = T[P i, P j]; P i = f^-1 i."""
        P = np.empty(d, dtype=np.int64)
        for i, r in enumerate(elems):
            P[idx(f(r))] = i
        return P

    pA, pS, pSi = aut_perm(thA), aut_perm(thS), aut_perm(thS_inv)

    def conj(T, P):
        return T[np.ix_(P, P)]

    Lg = left_perm(g)
    Lx = left_perm(x)
    # order of g
    m, q0 = 1, g
    while q0 != (0, 0, 0):
        q0 = mul(q0, g)
        m += 1

    web = [(0, b, c) for b in range(N) for c in range(N)]  # <y, z>
    Lweb = [left_perm(h) for h in web]
    Lall = [left_perm(q) for q in elems]
    ar = np.arange(d)

    def proj_C(T):
        acc = np.zeros_like(T)
        for L in Lweb:
            acc += T[np.ix_(L, L)]
        return acc / len(web)

    def absorption(M):
        s = 0.0
        for L in Lall:
            s += abs(M[L, ar].sum() / d) ** 2
        return np.sqrt(s)

    def hs(T):
        return np.sqrt(max((np.vdot(T, T) / d).real, 0.0))

    def frames(Z):
        return conj(Z, pA), conj(Z, pS)

    def metrics2(Z):
        tA, tS = frames(Z)
        E = tS @ tA.conj().T
        delta = hs(E[np.ix_(Lg, Lg)] - E)
        DA = Z @ tA.conj().T
        Mtw = DA @ (DA.conj().T[Lx, :])
        alpha = absorption(Mtw)
        return delta, alpha, E, tA

    # liftable control
    d0, a0, _, _ = metrics2(np.eye(d, dtype=complex))

    # Haar-ish Z in U(C)
    Zr = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    Z = upolar(proj_C(Zr))

    # exact-transport sanity: D_A = Z thA(Z)* must commute with the web,
    # which makes rho(A)-transport exact on <y,z>
    DA0 = Z @ conj(Z, pA).conj().T
    Ly = left_perm(y)
    trans_err = hs(DA0[np.ix_(Ly, Ly)] - DA0)

    hist = []
    delta, alpha, E, tA = metrics2(Z)
    hist.append((0, delta, alpha))
    for it in range(1, iters + 1):
        # project E onto commutant of lam(g)
        acc = np.zeros_like(E)
        cur = E
        for _ in range(m):
            acc += cur
            cur = cur[np.ix_(Lg, Lg)]
        Ehat = upolar(acc / m)
        # back-solve thS(Z) = Ehat thA(Z): fixed-point step
        Znew = conj(Ehat @ tA, pSi)
        Z = upolar(proj_C(Znew))
        delta, alpha, E, tA = metrics2(Z)
        hist.append((it, delta, alpha))
    return d, m, d0, a0, trans_err, hist


print("liftable control expected: delta = 0, alpha = 1.0000")
for N, iters in [(5, 40), (7, 40)]:
    d, m, d0, a0, terr, hist = run(N, iters)
    _, dl, al = hist[0]
    _, de, ae = hist[-1]
    print(f"\nN={N} dim={d} ord(g)={m}")
    print(f"  liftable control: delta={d0:.2e}  alpha={a0:.6f}")
    print(f"  web-transport exactness (should be ~0): {terr:.2e}")
    print(f"  init  (Haar Z): coherence={dl:.4f}  absorption={al:.4f}")
    for (it, dd, aa) in hist:
        if it in (5, 10, 20, 30, 40):
            print(f"  it{it:>3}: coherence={dd:.4f}  absorption={aa:.4f}")


# ---------------------------------------------------------------------------
# Exact-coherence stratum: tau := thA^-1 . thS is an involution.
#
# There is an important compatibility condition: Z must be both tau-invariant
# and in C = lambda(<y,z>)'.  Since tau(y)y^-1 z = x, the subgroups <y,z>
# and tau(<y,z>) generate Q.  Thus
#
#   C ∩ Fix(tau) ⊆ lambda(Q)'.
#
# In particular every genuinely admissible exact-coherence Z commutes with
# lambda(x), and the absorption is forced to be 1.  Averaging a C-element
# with its tau-image only, without projecting to the intersection, leaves C
# because tau(C) != C; that was the source of the former false-positive
# low-absorption samples.
# ---------------------------------------------------------------------------

def run_exact(N, samples=3):
    d = N * N * N
    inv2 = pow(2, -1, N)

    def idx(q):
        return ((q[0] % N) * N + (q[1] % N)) * N + (q[2] % N)

    def unidx(i):
        return (i // (N * N), (i // N) % N, i % N)

    def mul(p, q):
        return ((p[0] + q[0]) % N, (p[1] + q[1]) % N,
                (p[2] + q[2] + p[0] * q[1]) % N)

    def inv(p):
        a, b, c = p
        return ((-a) % N, (-b) % N, (-c + a * b) % N)

    def thA(p):
        return ((-p[0]) % N, p[1], (-p[2]) % N)

    def tau(p):
        a, b, c = p
        return ((b - a) % N, b, (b * (b - 1) * inv2 - c) % N)

    assert all(tau(tau(p)) == p for p in [(1, 2, 3), (4, 1, 2), (0, 3, 1)])

    elems = [unidx(i) for i in range(d)]

    def left_perm(q):
        qi = inv(q)
        L = np.empty(d, dtype=np.int64)
        for i, r in enumerate(elems):
            L[i] = idx(mul(qi, r))
        return L

    def aut_perm(f):
        P = np.empty(d, dtype=np.int64)
        for i, r in enumerate(elems):
            P[idx(f(r))] = i
        return P

    pA, pT = aut_perm(thA), aut_perm(tau)

    def conj(T, P):
        return T[np.ix_(P, P)]

    def thS_conj(T):
        return conj(conj(T, pT), pA)  # thS = thA . tau

    Lx = left_perm(x0 := (1, 0, 0))
    web = [(0, b, c) for b in range(N) for c in range(N)]
    Lweb = [left_perm(h) for h in web]
    Lall = [left_perm(q) for q in elems]
    ar = np.arange(d)

    def proj_C(T):
        acc = np.zeros_like(T)
        for L in Lweb:
            acc += T[np.ix_(L, L)]
        return acc / len(web)

    def proj_full_commutant(T):
        """Conditional expectation onto lambda(Q)'."""
        acc = np.zeros_like(T)
        for L in Lall:
            acc += T[np.ix_(L, L)]
        return acc / len(Lall)

    def absorption(M):
        s = 0.0
        for L in Lall:
            s += abs(M[L, ar].sum() / d) ** 2
        return np.sqrt(s)

    def hs(T):
        return np.sqrt(max((np.vdot(T, T) / d).real, 0.0))

    out = []
    for _ in range(samples):
        Zr = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
        # Because <y,z> and tau(<y,z>) generate Q, projecting to the full
        # commutant is the exact joint transport constraint.  This algebra is
        # tau-stable, so tau-averaging and polar projection stay inside it.
        Zr = proj_full_commutant(Zr)
        Zr = (Zr + conj(Zr, pT)) / 2
        Z = upolar(Zr)
        tA = conj(Z, pA)
        E = thS_conj(Z) @ tA.conj().T
        cohere = hs(E - np.eye(d))
        DA = Z @ tA.conj().T
        transport = hs(DA[np.ix_(left_perm((0, 1, 0)),
                                     left_perm((0, 1, 0)))] - DA)
        full_comm = max(hs(Z[np.ix_(L, L)] - Z) for L in Lall)
        alpha = absorption(DA @ (DA.conj().T[Lx, :]))
        out.append((cohere, transport, full_comm, alpha))
    return d, out


print("\n=== admissible exact-coherence stratum: absorption is forced to 1 ===")
for N in (5, 7, 9):
    d, out = run_exact(N)
    cs = ", ".join(f"{c:.2e}" for c, _, _, _ in out)
    ts = ", ".join(f"{t:.2e}" for _, t, _, _ in out)
    fs = ", ".join(f"{f:.2e}" for _, _, f, _ in out)
    as_ = ", ".join(f"{a:.6f}" for _, _, _, a in out)
    print(f"N={N} dim={d}: coherence [{cs}] transport [{ts}]")
    print(f"  full-commutant residuals [{fs}] absorption [{as_}]")


# ---------------------------------------------------------------------------
# NO-GO confirmation (correction of the run above): genuine membership in
# C  cap  Fix(tau) forces Z into lambda(Q)' (since <H, tau(H)> = Q), hence
# D_A commutes with lambda(x) and absorption is exactly 1.  The run_exact
# sampling above applied the tau-average AFTER proj_C, leaving C, so its
# low absorption came from VIOLATED web transport.  Both facts measured.
# ---------------------------------------------------------------------------

def run_nogo(N):
    d = N * N * N
    inv2 = pow(2, -1, N)

    def idx(q):
        return ((q[0] % N) * N + (q[1] % N)) * N + (q[2] % N)

    def unidx(i):
        return (i // (N * N), (i // N) % N, i % N)

    def mul(p, q):
        return ((p[0] + q[0]) % N, (p[1] + q[1]) % N,
                (p[2] + q[2] + p[0] * q[1]) % N)

    def inv(p):
        a, b, c = p
        return ((-a) % N, (-b) % N, (-c + a * b) % N)

    def thA(p):
        return ((-p[0]) % N, p[1], (-p[2]) % N)

    def tau(p):
        a, b, c = p
        return ((b - a) % N, b, (b * (b - 1) * inv2 - c) % N)

    elems = [unidx(i) for i in range(d)]

    def left_perm(q):
        qi = inv(q)
        L = np.empty(d, dtype=np.int64)
        for i, r in enumerate(elems):
            L[i] = idx(mul(qi, r))
        return L

    def aut_perm(f):
        P = np.empty(d, dtype=np.int64)
        for i, r in enumerate(elems):
            P[idx(f(r))] = i
        return P

    pA, pT = aut_perm(thA), aut_perm(tau)

    def conj(T, P):
        return T[np.ix_(P, P)]

    Lx = left_perm((1, 0, 0))
    Ly = left_perm((0, 1, 0))
    web = [(0, b, c) for b in range(N) for c in range(N)]
    Lweb = [left_perm(h) for h in web]
    Lall = [left_perm(q) for q in elems]
    ar = np.arange(d)

    def proj_C(T):
        acc = np.zeros_like(T)
        for L in Lweb:
            acc += T[np.ix_(L, L)]
        return acc / len(web)

    def proj_F(T):
        return (T + conj(T, pT)) / 2

    def absorption(M):
        s = 0.0
        for L in Lall:
            s += abs(M[L, ar].sum() / d) ** 2
        return np.sqrt(s)

    def hs(T):
        return np.sqrt(max((np.vdot(T, T) / d).real, 0.0))

    def report(Z, label):
        tA = conj(Z, pA)
        E = conj(conj(Z, pT), pA) @ tA.conj().T
        cohere = hs(E - np.eye(d))
        DA = Z @ tA.conj().T
        alpha = absorption(DA @ (DA.conj().T[Lx, :]))
        terr = hs(DA[np.ix_(Ly, Ly)] - DA)     # web-transport violation
        print(f"  {label}: coherence={cohere:.2e}  transport_err={terr:.4f}"
              f"  absorption={alpha:.6f}")

    Zr = rng.standard_normal((d, d)) + 1j * rng.standard_normal((d, d))
    # (i) the flawed sampling of run_exact: proj_C then ONE tau-average
    Zbad = upolar(proj_F(proj_C(Zr.copy())))
    report(Zbad, "flawed sampling (tau-avg leaves C) ")
    # (ii) the true intersection: alternate the two orthogonal projections
    T = Zr.copy()
    for _ in range(300):
        T = proj_F(proj_C(T))
    Ztrue = upolar(T)
    report(Ztrue, "true C cap Fix(tau) (300 alt-proj)")


print("\n=== no-go confirmation: exact transport + exact coherence ===")
for N in (5, 7):
    print(f"N={N}:")
    run_nogo(N)
