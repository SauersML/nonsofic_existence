import NonsoficGroupsExist.Sofic.PhaseCorrection

/-!
# The scalar class: what the correction has to kill, and where it lives

`PhaseCorrection` fences the problem: a phase defect that is uniformly small is
correctable when the average can be taken over the group, and the windowed
version fails by a Følner boundary.  This file identifies *what* the correction
has to kill, by averaging in the other direction.

Average the defect over the **model** rather than the group:

    ĉ(g,h) = (1/|Y|) Σ_{y ∈ Y} c(g,h)(y).

Two things happen at once.  The action disappears, because `act g` is a
bijection of `Y` and averaging over `Y` cannot see a relabelling; so the twisted
cocycle identity becomes the *untwisted* one (`isScalarCocycle_scalarPart`).
And the bound survives: `‖ĉ‖ ≤ ‖c‖` (`abs_scalarPart_le`).  So the average of a
small twisted defect is a **bounded `2`-cocycle on `G` with trivial
coefficients** -- exactly the object bounded cohomology is about.

The identification is completed by `scalarPart_phaseCob`: the scalar part of a
coboundary is the coboundary of the scalar part, with `‖β‖ ≤ ‖b‖`.  Contrapose
it (`scalarClass_obstructs`) and the reading is:

  *if the bounded class of `ĉ` does not vanish, no bounded correction of `c`
  exists at all.*

That places the scalar obstruction in `H²_b(G, ℝ)`, and it explains the shape of
everything in `PhaseCorrection`.  Bounded cohomology vanishes for amenable
groups and does not in general; the averaging argument there works exactly when
the window is almost invariant; and the two facts are the same fact.  It also
explains why the scalar witness of `ScalarCocycle` is the extreme case: a
constant defect *is* its own scalar part, carrying no mean-zero component at
all, and it is precisely the part the Hilbert--Schmidt metric cannot see.

What this does not do is produce a group with a non-vanishing class that is
forced on every model.  Soficity is a statement about finite windows, and a
bounded class is a statement about the whole group; any single window can be
corrected by extending the correction arbitrarily.  An obstruction would have to
be uniform over windows.  That gap is not closed here, and Question 3.4 is not
decided.
-/

namespace NonsoficGroupsExist

open Finset

variable {G : Type*} [Group G] {Y : Type*} [Fintype Y]

/-! ## Averaging over the model -/

/-- The average of a function over the model. -/
noncomputable def modelMean (f : Y → ℝ) : ℝ := (∑ y : Y, f y) / Fintype.card Y

/-- The scalar part of a defect: its average over the model. -/
noncomputable def scalarPart (c : G → G → Y → ℝ) (g h : G) : ℝ :=
  modelMean (c g h)

/-- The untwisted `2`-cocycle identity, for scalars. -/
def IsScalarCocycle (d : G → G → ℝ) : Prop :=
  ∀ g h k : G, d g h + d (g * h) k = d h k + d g (h * k)

/-- The untwisted coboundary of a scalar `1`-cochain. -/
def scalarCob (β : G → ℝ) (g h : G) : ℝ := β h + β g - β (g * h)

/-- A witness carrying no hypotheses, so `IsScalarCocycle` is not a certificate
nothing satisfies. -/
theorem isScalarCocycle_scalarCob (β : G → ℝ) : IsScalarCocycle (scalarCob β) := by
  intro g h k
  simp only [scalarCob, mul_assoc]
  ring

/-! ## The action disappears -/

/-- **Averaging over the model untwists the cocycle identity.**  The action
enters the identity only as a relabelling of `Y`, and an average over `Y` cannot
see a relabelling.  So the scalar part of a twisted defect is an ordinary
`2`-cocycle on `G` with trivial coefficients. -/
theorem isScalarCocycle_scalarPart (hY : 0 < Fintype.card Y)
    (act : G → Equiv.Perm Y) (c : G → G → Y → ℝ)
    (hc : IsPhaseCocycle act c) : IsScalarCocycle (scalarPart c) := by
  intro g h k
  have hcard : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hsum : ∑ y : Y, (c g h y + c (g * h) k y)
      = ∑ y : Y, (c h k ((act g)⁻¹ y) + c g (h * k) y) :=
    Finset.sum_congr rfl fun y _ ↦ hc g h k y
  have hrelabel : ∑ y : Y, c h k ((act g)⁻¹ y) = ∑ y : Y, c h k y :=
    Equiv.sum_comp ((act g)⁻¹) (fun y ↦ c h k y)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hrelabel] at hsum
  simp only [scalarPart, modelMean]
  field_simp
  linarith [hsum]

omit [Group G] in
/-- **The bound survives averaging.** -/
theorem abs_scalarPart_le (hY : 0 < Fintype.card Y) (c : G → G → Y → ℝ) {B : ℝ}
    (hbd : ∀ g h y, |c g h y| ≤ B) (g h : G) : |scalarPart c g h| ≤ B := by
  have hcard : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  rw [scalarPart, modelMean, abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  calc |∑ y : Y, c g h y| ≤ ∑ y : Y, |c g h y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y : Y, B := Finset.sum_le_sum fun y _ ↦ hbd g h y
    _ = B * Fintype.card Y := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-! ## The scalar part of a correction -/

/-- **The scalar part of a coboundary is the coboundary of the scalar part.**
Averaging over the model commutes with correcting, so a correction of `c`
descends to a correction of `ĉ`. -/
theorem scalarPart_phaseCob (act : G → Equiv.Perm Y) (b : G → Y → ℝ) (g h : G) :
    scalarPart (phaseCob act b) g h = scalarCob (fun g ↦ modelMean (b g)) g h := by
  have hrelabel : ∑ y : Y, b h ((act g)⁻¹ y) = ∑ y : Y, b h y :=
    Equiv.sum_comp ((act g)⁻¹) (fun y ↦ b h y)
  simp only [scalarPart, scalarCob, modelMean, phaseCob]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hrelabel]
  ring

/-- **The scalar class obstructs every correction.**  If the scalar part of a
defect is not the coboundary of a scalar `1`-cochain bounded by `B`, then the
defect is not the coboundary of any phase correction bounded by `B`.

So the obstruction to correcting a monomial model lives, in its scalar
direction, in bounded cohomology `H²_b(G, ℝ)`: a bounded `2`-cocycle with
trivial coefficients, modulo coboundaries of bounded `1`-cochains.  That is why
`PhaseCorrection` succeeds exactly when the window is almost invariant --
bounded cohomology vanishes for amenable groups and does not in general. -/
theorem scalarClass_obstructs (hY : 0 < Fintype.card Y)
    (act : G → Equiv.Perm Y) (c : G → G → Y → ℝ)
    {B : ℝ} (hobs : ∀ β : G → ℝ, (∀ g, |β g| ≤ B) →
      ∃ g h, scalarPart c g h ≠ scalarCob β g h) :
    ∀ b : G → Y → ℝ, (∀ g y, |b g y| ≤ B) →
      ∃ g h y, c g h y ≠ phaseCob act b g h y := by
  intro b hb
  have hcard : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hY
  have hbmean : ∀ g, |modelMean (b g)| ≤ B := by
    intro g
    rw [modelMean, abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
    calc |∑ y : Y, b g y| ≤ ∑ y : Y, |b g y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y : Y, B := Finset.sum_le_sum fun y _ ↦ hb g y
      _ = B * Fintype.card Y := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  obtain ⟨g, h, hgh⟩ := hobs (fun g ↦ modelMean (b g)) hbmean
  by_contra hcon
  have heq : ∀ (g' h' : G) (y : Y), c g' h' y = phaseCob act b g' h' y := by
    intro g' h' y
    by_contra hne
    exact hcon ⟨g', h', y, hne⟩
  apply hgh
  have hstep : scalarPart c g h = scalarPart (phaseCob act b) g h := by
    simp only [scalarPart, modelMean]
    congr 1
    exact Finset.sum_congr rfl fun y _ ↦ heq g h y
  rw [hstep, scalarPart_phaseCob]

end NonsoficGroupsExist
