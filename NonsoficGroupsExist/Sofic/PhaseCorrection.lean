import NonsoficGroupsExist.Sofic.NoRounding
import Mathlib.Algebra.BigOperators.Fin

/-!
# The non-pointwise correction, and exactly where it stops

`NoRounding` closes every *pointwise* rule for turning a metric phase system
into a combinatorial one.  What it leaves open is a correction that uses the
group being modelled: replace the phases `d_g` by `d_g · b_g` for a correction
`b` chosen with the whole group in view.  This file carries that out, and the
answer is sharp in both directions.

The defect of a phase system is the twisted `2`-cocycle

    c(g,h) = g·d_h + d_g - d_{gh},

and correcting `d` by `b` moves `c` by the coboundary of `b`.  So the question
is whether a cocycle whose values are *uniformly* near zero is the coboundary of
something near zero.  It is, and the correction is an average over the group:

    b_g = (1/|G|) Σ_{k ∈ G} c(g,k)                (`phaseCorrection_eq`)

with `‖b‖ ≤ ‖c‖` (`abs_phaseCorrection_le`).  Two facts make it work, and
neither is pointwise.  The averaging is over `G`, and the passage from the
circle to `ℝ` is a lifting: a cochain that satisfies the cocycle identity only
*modulo* `ℤ` and whose values lie within `1/6` of zero satisfies it exactly,
because the identity has four terms and `4/6 < 1` (`isPhaseCocycle_of_mod`).

So `phase_correctable_of_small` says: a phase system whose defect is uniformly
below `1/6` of the circle can be corrected to an exactly multiplicative one, by
a correction no larger than the defect.

The consequence for Question 3.4 is a dichotomy, and it is the point of the
file.  An obstruction to soficity cannot come from a phase defect that is
uniformly small.  It has to come from a defect that is small *on average over
the model* and large somewhere -- which is exactly the regime the
Hilbert--Schmidt metric permits and the Hamming metric does not, and exactly the
gap priced in `ScalarCocycle`.  Nothing here decides Question 3.4; it removes
the uniform regime from consideration.
-/

namespace NonsoficGroupsExist

open Finset

variable {G : Type*} [Group G] [Fintype G] {Y : Type*}

/-! ## Cochains, coboundaries, cocycles -/

/-- The twisted coboundary of a `1`-cochain of phases.  The action moves a phase
function by `(g · f)(y) = f(g⁻¹ y)`, so this is the usual inhomogeneous
`δ b (g,h) = g·b_h + b_g - b_{gh}`. -/
def phaseCob (act : G → Equiv.Perm Y) (b : G → Y → ℝ) (g h : G) (y : Y) : ℝ :=
  b h ((act g)⁻¹ y) + b g y - b (g * h) y

/-- The twisted `2`-cocycle identity. -/
def IsPhaseCocycle (act : G → Equiv.Perm Y) (c : G → G → Y → ℝ) : Prop :=
  ∀ (g h k : G) (y : Y),
    c g h y + c (g * h) k y = c h k ((act g)⁻¹ y) + c g (h * k) y

omit [Fintype G] in
/-- **Every coboundary is a cocycle**, so the definition above is satisfied by
something.  This is `δ² = 0`, and the only thing it uses is that `act` is a
homomorphism. -/
theorem isPhaseCocycle_phaseCob (act : G → Equiv.Perm Y)
    (hact : ∀ g h : G, act (g * h) = act g * act h) (b : G → Y → ℝ) :
    IsPhaseCocycle act (phaseCob act b) := by
  intro g h k y
  simp only [phaseCob]
  have hcomp : ((act (g * h))⁻¹) y = ((act h)⁻¹) (((act g)⁻¹) y) := by
    rw [hact g h]
    rfl
  rw [hcomp, mul_assoc]
  ring

omit [Fintype G] in
/-- A witness carrying no hypotheses, so `IsPhaseCocycle` is not a certificate
nothing satisfies: the trivial action makes every `1`-cochain's coboundary a
cocycle, and the cochain is arbitrary. -/
theorem isPhaseCocycle_trivialAction (b : G → Y → ℝ) :
    IsPhaseCocycle (fun _ : G ↦ (1 : Equiv.Perm Y))
      (phaseCob (fun _ : G ↦ (1 : Equiv.Perm Y)) b) :=
  isPhaseCocycle_phaseCob _ (fun _ _ ↦ by simp) b

/-! ## The correction, and its size -/

/-- The correction supplied by averaging the defect over the group. -/
noncomputable def phaseCorrection (c : G → G → Y → ℝ) (g : G) (y : Y) : ℝ :=
  (∑ k : G, c g k y) / Fintype.card G

/-- **The correction is no larger than the defect.**  An average of numbers
bounded by `B` is bounded by `B`. -/
theorem abs_phaseCorrection_le (c : G → G → Y → ℝ) {B : ℝ}
    (hbd : ∀ g h y, |c g h y| ≤ B) (g : G) (y : Y) :
    |phaseCorrection c g y| ≤ B := by
  have hpos : (0 : ℝ) < Fintype.card G := by
    have := Fintype.card_pos_iff.mpr (⟨1⟩ : Nonempty G)
    exact_mod_cast this
  rw [phaseCorrection, abs_div, abs_of_pos hpos]
  rw [div_le_iff₀ hpos]
  calc |∑ k : G, c g k y| ≤ ∑ k : G, |c g k y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : G, B := Finset.sum_le_sum fun k _ ↦ hbd g k y
    _ = B * Fintype.card G := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- **The averaging identity.**  A twisted `2`-cocycle on a finite group is the
coboundary of its own average over the group.  Summing the cocycle identity over
`k` and reindexing `k ↦ hk` is the whole proof; note that it is not pointwise in
the model, since it averages over `G`. -/
theorem phaseCorrection_eq (act : G → Equiv.Perm Y) (c : G → G → Y → ℝ)
    (hc : IsPhaseCocycle act c) (g h : G) (y : Y) :
    c g h y = phaseCob act (phaseCorrection c) g h y := by
  classical
  have hpos : (0 : ℝ) < Fintype.card G := by
    have := Fintype.card_pos_iff.mpr (⟨1⟩ : Nonempty G)
    exact_mod_cast this
  -- sum the cocycle identity over `k`
  have hsum : ∑ k : G, (c g h y + c (g * h) k y)
      = ∑ k : G, (c h k ((act g)⁻¹ y) + c g (h * k) y) :=
    Finset.sum_congr rfl fun k _ ↦ hc g h k y
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  -- reindex the last sum
  have hre : ∑ k : G, c g (h * k) y = ∑ k : G, c g k y :=
    Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun k ↦ rfl
  rw [hre] at hsum
  -- unfold and clear the denominator
  simp only [phaseCob, phaseCorrection]
  field_simp
  linarith [hsum]

/-! ## Lifting from the circle -/

omit [Fintype G] in
/-- **A nearly-trivial cochain that is a cocycle modulo `ℤ` is one exactly.**
The identity has four terms; if each is within `1/6` of zero the total is within
`4/6 < 1` of an integer, so that integer is zero.  This is the step that uses
the circle rather than the reals, and it is where the constant comes from. -/
theorem isPhaseCocycle_of_mod (act : G → Equiv.Perm Y) (c : G → G → Y → ℝ)
    (hbd : ∀ g h y, |c g h y| ≤ 1 / 6)
    (hmod : ∀ (g h k : G) (y : Y), ∃ n : ℤ,
      c g h y + c (g * h) k y - c h k ((act g)⁻¹ y) - c g (h * k) y = (n : ℝ)) :
    IsPhaseCocycle act c := by
  intro g h k y
  obtain ⟨n, hn⟩ := hmod g h k y
  have h1 := abs_le.mp (hbd g h y)
  have h2 := abs_le.mp (hbd (g * h) k y)
  have h3 := abs_le.mp (hbd h k ((act g)⁻¹ y))
  have h4 := abs_le.mp (hbd g (h * k) y)
  have habs : |(n : ℝ)| < 1 := by
    rw [← hn, abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  have hn0 : n = 0 := by
    have hlt : |n| < 1 := by exact_mod_cast habs
    obtain ⟨h5, h6⟩ := abs_lt.mp hlt
    omega
  rw [hn0] at hn
  push_cast at hn
  linarith [hn]

/-! ## The dichotomy -/

/-- **A uniformly small phase defect is correctable.**  If the defect of a phase
system is a cocycle modulo `ℤ` -- which is what it means to live on the circle
-- and is uniformly within `1/6` of zero, then it is the exact coboundary of a
correction that is itself within `1/6` of zero.

So no obstruction to soficity can come from a uniformly small phase defect.  An
obstruction has to be a defect that is small *on average over the model* and
large somewhere: precisely the regime the Hilbert--Schmidt metric permits and
the Hamming metric does not. -/
theorem phase_correctable_of_small (act : G → Equiv.Perm Y) (c : G → G → Y → ℝ)
    (hbd : ∀ g h y, |c g h y| ≤ 1 / 6)
    (hmod : ∀ (g h k : G) (y : Y), ∃ n : ℤ,
      c g h y + c (g * h) k y - c h k ((act g)⁻¹ y) - c g (h * k) y = (n : ℝ)) :
    ∃ b : G → Y → ℝ, (∀ g y, |b g y| ≤ 1 / 6) ∧
      ∀ g h y, c g h y = phaseCob act b g h y :=
  ⟨phaseCorrection c,
    fun g y ↦ abs_phaseCorrection_le c hbd g y,
    fun g h y ↦ phaseCorrection_eq act c (isPhaseCocycle_of_mod act c hbd hmod) g h y⟩

end NonsoficGroupsExist
