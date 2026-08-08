# Displacement-coherence feasibility: results (2026-08-08)

Heisenberg surrogate Q = Heis(Z/N); frames: flip thA(a,b,c) = (-a,b,-c) and
shear thS(a,b,c) = (a-b,b,c-b(b-1)/2); two-path invisible element
g = thA(xy) = thS(yz^-1) = (-1,1,-1); Z on the commutant of <y,z>;
absorption = Fourier mass of D_A lam(x) D_A* on the group algebra
(liftable control Z = 1: absorption = 1.000000 exactly, verified).

1. Naive alternating projection (project E to lam(g)-commutant, back-solve,
   re-project to U(C)): STALLS at the random floor. Coherence defect frozen
   at 1.3964 (N=5) / 1.4168 (N=7) ~ sqrt(2) over 40 iterations - the
   predicted random-Z failure, and the projected fixed-point step cannot
   leave it.

2. THE EXACT STRATUM: tau := thA^-1 . thS satisfies tau^2 = id, so
   tau-invariant Z in U(C) gives thS(Z) = thA(Z), hence E = 1 identically:
   EVERY displacement-coherence equation of the frame pair holds at once
   (the XCIX coboundary collapse, realized). Measured:

   | N | dim | coherence residual | absorption (3 samples)   |
   |---|-----|--------------------|--------------------------|
   | 5 | 125 | ~4e-15             | 0.2085, 0.2177, 0.2102   |
   | 7 | 343 | ~7e-15             | 0.1461, 0.1401, 0.1381   |
   | 9 | 729 | ~8e-15             | 0.1144, 0.1140, 0.1114   |

   Exact coherence costs the mixing nothing: absorption on the exact
   stratum (0.21 -> 0.14 -> 0.11) matches the unconstrained decay and sits
   an order of magnitude below the liftable value 1.0, tightly concentrated
   across samples.

Reading: for this frame pair the displacement-coherence system is solved
EXACTLY with the mixing intact and decaying with congruence depth. What
remains open on the true Kun-Thom pair: the full Steinberg web has
non-involutive multi-frame syzygies; the analog of the tau-invariant
stratum is invariance under the whole substitution action, and whether
Haar freedom survives on THAT joint fixed subalgebra with mixing intact is
exactly the (beta)-assembly - the genuinely open certificate. Numerics are
evidence, not proof.
