# Displacement-coherence: CORRECTED record (2026-08-08, supersedes earlier)

## The no-go (analytic, then confirmed numerically)

On the Heisenberg surrogate with H = <y,z> and the flip/shear frame pair:
tau(y) y^-1 z = x, so <H, tau(H)> = Q.  Hence any Z satisfying BOTH ansatz
constraints -- Z in C = lambda(H)' (exact web transport) and tau(Z) = Z
(exact coherence, E = 1) -- lies in lambda(Q)', so D_A = Z thA(Z)* commutes
with lambda(x) and the absorption of the invisible letter is EXACTLY 1:

    exact web transport + exact coherence  ==>  total absorption.

Measured (alternating projections onto C and Fix(tau), 300 rounds):
transport 0.0000, coherence ~1e-15, absorption 1.000000 at N = 5 and 7.

## Retraction

The earlier "exact stratum solves the surrogate" claim is WITHDRAWN.  Its
sampling applied the tau-average after proj_C; the average leaves C
(tau(H) != H), and run_exact never rechecked transport.  Measured
violation: transport_err = 1.3179 / 1.3184 (order one) behind the
apparent absorption 0.20 / 0.15.  The daylight was an artifact of broken
transport, exactly as the counter-audit diagnosed.

## Standing repairs accepted

1. XCIX cocycle convention: D_AB = D_A thA(D_B) corresponds to
   rho(A) = D_A pi(A) = Z pi(A) Z^-1, not pi(A) D_A.
2. XCVI's |tau(rho_n g)| <= 1/2 step needs non-scalar / trace-normalized
   microstates as an explicit hypothesis: u = iI has full HS-separation
   with |tau| = 1 and collapsing tensor powers -- the obstruction
   kernel-checked in Sofic/HyperlinearAmplification
   (tensorPow_phase_collapse) and Sofic/NormTraceGap
   (phase_deviation_no_amplification).
3. One-percent mixing at ONE invisible letter does not imply XCV's
   hypothesis, which needs relative mixing for every non-Gamma interior
   word of each growing window; the one-letter-to-cone propagation
   theorem is missing.

## The sharpened next target

For the actual Steinberg web with constraint subgroup H_W and frame-change
tau: compute the constraint closure <H_W, tau(H_W)>.  If it contains the
witness root subgroup (or the relevant finite quotient), the
global-coboundary ansatz is sterile there by the same argument; if not,
the commutant of the closure identifies exactly where mixing can survive.
Exact strata are sterile in the surrogate; any daylight must be sought at
epsilon-level (approximate transport/coherence within the N19 budget
epsilon = o(rho)), or in a web whose constraint closure is proper.
