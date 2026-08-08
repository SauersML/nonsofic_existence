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
gap priced in `ScalarCocycle`.

The second half of the file asks what happens when `G` is infinite, so that the
average must be taken over a finite window `F` instead.  The reindexing
`k ↦ hk`, which is the single step that made the argument work, then no longer
maps the window to itself, and what it costs is *exactly* the boundary:

    c(g,h) - δb(g,h)  =  (1/|F|) ( Σ_{hF \ F} c(g,·) - Σ_{F \ hF} c(g,·) )

(`window_defect_eq`), whence `‖c - δb‖ ≤ ‖c‖ · |hF △ F| / |F|`
(`abs_window_defect_le`).  So the group-averaged correction survives to an
infinite group exactly when almost invariant windows exist -- that is, exactly
for amenable groups, which are sofic already.  The route recovers what is known
and stalls precisely at non-amenability, and the stalling is a named quantity
rather than a vague difficulty.

Nothing here decides Question 3.4.  It removes the uniform regime from
consideration and prices the windowed one.
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


/-! ## The windowed correction: the failure is a Følner boundary

The averaging above runs over all of `G`, so it is available only for a finite
group.  For an infinite group one can only average over a finite window `F`, and
then the reindexing `k ↦ hk` -- the single step that made the proof work -- no
longer maps the window to itself.  What it costs is exactly the boundary.
-/

/-- The correction obtained by averaging the defect over a finite window. -/
noncomputable def windowCorrection [DecidableEq G] (F : Finset G)
    (c : G → G → Y → ℝ) (g : G) (y : Y) : ℝ :=
  (∑ k ∈ F, c g k y) / F.card

omit [Fintype G] in
/-- **The windowed averaging identity.**  Averaging over a window corrects the
defect up to a term supported on the boundary `hF △ F`, and nothing else: the
identity is exact, with the boundary term written out. -/
theorem window_defect_eq [DecidableEq G] (act : G → Equiv.Perm Y) (F : Finset G)
    (hF : F.Nonempty) (c : G → G → Y → ℝ) (hc : IsPhaseCocycle act c)
    (g h : G) (y : Y) :
    c g h y - phaseCob act (windowCorrection F c) g h y
      = ((∑ k ∈ F.image (fun k ↦ h * k) \ F, c g k y)
          - ∑ k ∈ F \ F.image (fun k ↦ h * k), c g k y) / F.card := by
  classical
  have hcard : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hF
  have hsum : ∑ k ∈ F, (c g h y + c (g * h) k y)
      = ∑ k ∈ F, (c h k ((act g)⁻¹ y) + c g (h * k) y) :=
    Finset.sum_congr rfl fun k _ ↦ hc g h k y
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have hre : ∑ k ∈ F, c g (h * k) y
      = ∑ k ∈ F.image (fun k ↦ h * k), c g k y := by
    rw [Finset.sum_image]
    intro x _ z _ hxz
    exact mul_left_cancel hxz
  have h1 := Finset.sum_inter_add_sum_sdiff (F.image (fun k ↦ h * k)) F
    (fun k ↦ c g k y)
  have h2 := Finset.sum_inter_add_sum_sdiff F (F.image (fun k ↦ h * k))
    (fun k ↦ c g k y)
  rw [Finset.inter_comm] at h1
  rw [hre] at hsum
  simp only [phaseCob, windowCorrection]
  field_simp
  linarith [hsum, h1, h2]

omit [Fintype G] in
/-- **The Følner bound.**  The correction fails by at most the defect size times
the relative boundary of the window.  So the group-averaged correction succeeds
for an infinite group exactly when almost invariant windows are available --
that is, exactly for amenable groups.  Amenable groups are sofic anyway, so this
route recovers what is already known and stalls precisely at non-amenability. -/
theorem abs_window_defect_le [DecidableEq G] (act : G → Equiv.Perm Y)
    (F : Finset G) (hF : F.Nonempty) (c : G → G → Y → ℝ)
    (hc : IsPhaseCocycle act c) {B : ℝ} (hbd : ∀ g h y, |c g h y| ≤ B)
    (g h : G) (y : Y) :
    |c g h y - phaseCob act (windowCorrection F c) g h y|
      ≤ B * (((F.image (fun k ↦ h * k) \ F).card
              + (F \ F.image (fun k ↦ h * k)).card : ℕ) : ℝ) / F.card := by
  classical
  have hcard : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hF
  have hboundA : |∑ k ∈ F.image (fun k ↦ h * k) \ F, c g k y|
      ≤ B * ((F.image (fun k ↦ h * k) \ F).card : ℝ) := by
    calc |∑ k ∈ F.image (fun k ↦ h * k) \ F, c g k y|
        ≤ ∑ k ∈ F.image (fun k ↦ h * k) \ F, |c g k y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ F.image (fun k ↦ h * k) \ F, B :=
          Finset.sum_le_sum fun k _ ↦ hbd g k y
      _ = B * ((F.image (fun k ↦ h * k) \ F).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hboundB : |∑ k ∈ F \ F.image (fun k ↦ h * k), c g k y|
      ≤ B * ((F \ F.image (fun k ↦ h * k)).card : ℝ) := by
    calc |∑ k ∈ F \ F.image (fun k ↦ h * k), c g k y|
        ≤ ∑ k ∈ F \ F.image (fun k ↦ h * k), |c g k y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ F \ F.image (fun k ↦ h * k), B :=
          Finset.sum_le_sum fun k _ ↦ hbd g k y
      _ = B * ((F \ F.image (fun k ↦ h * k)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [window_defect_eq act F hF c hc g h y, abs_div, abs_of_pos hcard]
  gcongr
  push_cast
  calc |(∑ k ∈ F.image (fun k ↦ h * k) \ F, c g k y)
          - ∑ k ∈ F \ F.image (fun k ↦ h * k), c g k y|
      ≤ |∑ k ∈ F.image (fun k ↦ h * k) \ F, c g k y|
          + |∑ k ∈ F \ F.image (fun k ↦ h * k), c g k y| := abs_sub _ _
    _ ≤ B * ((F.image (fun k ↦ h * k) \ F).card : ℝ)
          + B * ((F \ F.image (fun k ↦ h * k)).card : ℝ) := by
        exact add_le_add hboundA hboundB
    _ = B * (((F.image (fun k ↦ h * k) \ F).card : ℝ)
          + ((F \ F.image (fun k ↦ h * k)).card : ℝ)) := by ring

end NonsoficGroupsExist
