import NonsoficGroupsExist.Sofic.HyperlinearScalar

/-!
# Two obstructions beyond elementwise approximation

Both statements here are due to an external referee audit of this development
(August 2026); they are formalized because they are exactly the kind of claim
that should not travel as prose.  Neither bears on Theorem A; both bear on how
a hyperlinear model of a wreath-type candidate could be built.

## Implementer coherence is a cocycle problem

Suppose an action is implemented elementwise -- for each `g` there is a unitary
`v g` with `Ad (v g)` the right automorphism.  Being able to do this for every
`g` separately is *not* the same as having a representation.  The failure is
measured by

  `c g h = v g * v h * (v (g * h))⁻¹`,

which satisfies the twisted `2`-cocycle identity
(`implementerCocycle_twisted`), and correcting the implementers by `b g` moves
`c` by a coboundary: `g ↦ b g * v g` is a homomorphism exactly when

  `b g * (v g) (b h) (v g)⁻¹ * c g h * (b (g * h))⁻¹ = 1`

(`mul_isMulHom_iff`).  So "each automorphism is approximately inner" is
incomplete data, and a construction that chooses implementers one element at a
time still owes the trivialization of a class.  The finite-dimensional
calibration is the Pauli pair: `Ad X` and `Ad Z` commute on `M₂(ℂ)` because
`XZ = -ZX`, both are inner, and no commuting pair of implementers exists --
the action is represented projectively and not otherwise.

Everything here is a group identity, so it is stated for an arbitrary group of
units rather than for unitaries in an ultraproduct; that is the level at which
it is true, and specializing costs nothing.

## Normalized rank blindness

Two *orthogonal* rank-one projections on a model of size `n` are at normalized
squared Hilbert--Schmidt distance `2/n`, which tends to zero
(`hsDistSq_orthogonal_rankOne`).  So the metric that hyperlinearity uses can
regard two completely different microscopic atoms as asymptotically identical.
Any argument that tracks a distinguished lamp vector, or transports a Kazhdan
fixed vector, or preserves an orbit chart, must therefore first supply a lower
bound on the *relative trace* of the support it tracks; normalized-rank
information alone will not do it.
-/

namespace NonsoficGroupsExist

open Matrix

/-! ## The implementer cocycle -/

variable {G M : Type*} [Group G] [Group M]

/-- The failure of a family of implementers to be a homomorphism. -/
def implementerCocycle (v : G → M) (g h : G) : M :=
  v g * v h * (v (g * h))⁻¹

@[simp] theorem implementerCocycle_apply (v : G → M) (g h : G) :
    implementerCocycle v g h = v g * v h * (v (g * h))⁻¹ := rfl

/-- **The twisted cocycle identity.**  With `α g = Ad (v g)`, the defect
satisfies `c(g,h) c(gh,k) = α_g(c(h,k)) c(g,hk)`.  Both sides are
`v g * v h * v k * (v (g*h*k))⁻¹`. -/
theorem implementerCocycle_twisted (v : G → M) (g h k : G) :
    implementerCocycle v g h * implementerCocycle v (g * h) k
      = (v g * implementerCocycle v h k * (v g)⁻¹)
        * implementerCocycle v g (h * k) := by
  simp only [implementerCocycle_apply, mul_assoc]
  group

/-- A family of implementers is a homomorphism exactly when its defect is
trivial. -/
theorem implementerCocycle_eq_one_iff (v : G → M) (g h : G) :
    implementerCocycle v g h = 1 ↔ v (g * h) = v g * v h := by
  rw [implementerCocycle_apply, _root_.mul_inv_eq_one]
  exact eq_comm

/-- **Correcting the implementers moves the defect by a coboundary.**  The
corrected family `g ↦ b g * v g` is a homomorphism exactly when the displayed
combination is trivial, which is the statement that `c` is a coboundary for the
twisted action. -/
theorem correctedImplementer_defect (v b : G → M) (g h : G) :
    (b g * v g) * (b h * v h) * ((b (g * h) * v (g * h)))⁻¹
      = b g * (v g * b h * (v g)⁻¹) * implementerCocycle v g h
        * (b (g * h))⁻¹ := by
  simp only [implementerCocycle_apply, _root_.mul_inv_rev, mul_assoc]
  group

/-- Consequently the corrected family is multiplicative at `(g, h)` exactly
when the coboundary equation holds there. -/
theorem correctedImplementer_mul_iff (v b : G → M) (g h : G) :
    (b (g * h) * v (g * h)) = (b g * v g) * (b h * v h)
      ↔ b g * (v g * b h * (v g)⁻¹) * implementerCocycle v g h
          * (b (g * h))⁻¹ = 1 := by
  rw [← correctedImplementer_defect v b g h, _root_.mul_inv_eq_one]
  exact eq_comm

/-! ## Normalized rank blindness -/

/-- The rank-one projection onto a coordinate. -/
def coordProjection (Y : FiniteModel) (a : Y) : Matrix Y Y ℂ :=
  fun i j ↦ if i = a ∧ j = a then 1 else 0

@[simp] theorem coordProjection_apply (Y : FiniteModel) (a : Y) (i j : Y) :
    coordProjection Y a i j = if i = a ∧ j = a then 1 else 0 := rfl

/-- Distinct coordinate projections are orthogonal. -/
theorem coordProjection_mul_eq_zero (Y : FiniteModel) {a b : Y} (hab : a ≠ b) :
    coordProjection Y a * coordProjection Y b = 0 := by
  classical
  ext i k
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [coordProjection_apply, coordProjection_apply]
  by_cases h1 : i = a ∧ j = a
  · rw [if_pos h1, if_neg (fun h2 ↦ hab (h1.2 ▸ h2.1)), mul_zero]
  · rw [if_neg h1, zero_mul]

/-- **Normalized rank blindness.**  Two orthogonal rank-one projections sit at
normalized squared Hilbert--Schmidt distance `2/n`, which tends to zero with the
size of the model even though the projections are as different as two
projections can be. -/
theorem hsDistSq_orthogonal_rankOne (Y : FiniteModel) {a b : Y} (hab : a ≠ b) :
    hsDistSq Y (coordProjection Y a) (coordProjection Y b)
      = 2 / Fintype.card Y := by
  classical
  have hterm : ∀ i j : Y, Complex.normSq
      (coordProjection Y a i j - coordProjection Y b i j)
      = (if i = a then (1 : ℝ) else 0) * (if j = a then (1 : ℝ) else 0)
        + (if i = b then (1 : ℝ) else 0) * (if j = b then (1 : ℝ) else 0) := by
    intro i j
    rw [coordProjection_apply, coordProjection_apply]
    by_cases h1 : i = a <;> by_cases h2 : j = a <;>
      by_cases h3 : i = b <;> by_cases h4 : j = b <;>
      simp_all [Complex.normSq_apply]
  have hinner : ∀ i : Y, (∑ j : Y, Complex.normSq
      (coordProjection Y a i j - coordProjection Y b i j))
      = (if i = a then (1 : ℝ) else 0) + (if i = b then (1 : ℝ) else 0) := by
    intro i
    rw [Finset.sum_congr rfl fun j _ ↦ hterm i j, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ a (fun _ : Y ↦ (1 : ℝ)),
      Finset.sum_ite_eq' Finset.univ b (fun _ : Y ↦ (1 : ℝ))]
    simp
  rw [hsDistSq, Finset.sum_congr rfl fun i _ ↦ hinner i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ a (fun _ : Y ↦ (1 : ℝ)),
    Finset.sum_ite_eq' Finset.univ b (fun _ : Y ↦ (1 : ℝ))]
  norm_num

end NonsoficGroupsExist
