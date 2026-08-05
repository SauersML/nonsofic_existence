import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The Chebyshev center of a bounded set in a Hilbert space

Every nonempty bounded subset of a complete real inner product space has
a unique circumcenter: the unique minimizer of the supremal distance to
the set.  The parallelogram law makes the covering radius function
uniformly convex, so minimizing sequences are Cauchy and the minimizer is
unique.  This is the fixed-point engine behind the Delorme direction of
the Delorme–Guichardet theorem: an affine isometric action with a bounded
orbit fixes the circumcenter of that orbit.
-/

namespace NonsoficGroupsExist
namespace Circumcenter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The covering radius of a set from a point. -/
noncomputable def coveringRadius (S : Set E) (x : E) : ℝ :=
  sSup ((fun s ↦ dist x s) '' S)

omit [InnerProductSpace ℝ E] in
theorem dist_le_coveringRadius {S : Set E} (hbdd : Bornology.IsBounded S)
    (x : E) {s : E} (hs : s ∈ S) : dist x s ≤ coveringRadius S x := by
  apply le_csSup
  · obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall x).1 hbdd
    exact ⟨R, by
      rintro _ ⟨t, ht, rfl⟩
      exact Metric.mem_closedBall'.mp (hR ht)⟩
  · exact ⟨s, hs, rfl⟩

omit [InnerProductSpace ℝ E] in
theorem coveringRadius_le {S : Set E} (hne : S.Nonempty) {x : E} {r : ℝ}
    (h : ∀ s ∈ S, dist x s ≤ r) : coveringRadius S x ≤ r := by
  apply csSup_le
  · exact hne.image _
  · rintro _ ⟨s, hs, rfl⟩
    exact h s hs

omit [InnerProductSpace ℝ E] in
theorem coveringRadius_nonneg {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (x : E) :
    0 ≤ coveringRadius S x := by
  obtain ⟨s, hs⟩ := hne
  exact le_trans dist_nonneg (dist_le_coveringRadius hbdd x hs)

omit [InnerProductSpace ℝ E] in
theorem coveringRadius_lipschitz {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (x y : E) :
    coveringRadius S x ≤ coveringRadius S y + dist x y := by
  apply coveringRadius_le hne
  intro s hs
  calc
    dist x s ≤ dist x y + dist y s := dist_triangle x y s
    _ ≤ dist x y + coveringRadius S y :=
      add_le_add le_rfl (dist_le_coveringRadius hbdd y hs)
    _ = coveringRadius S y + dist x y := by ring

/-- The parallelogram estimate for covering radii: the radius at a
midpoint improves quadratically in the separation. -/
theorem coveringRadius_midpoint_sq {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (x y : E) :
    coveringRadius S (midpoint ℝ x y) ^ 2 + dist x y ^ 2 / 4 ≤
      (coveringRadius S x ^ 2 + coveringRadius S y ^ 2) / 2 := by
  have hmid : ∀ s ∈ S, dist (midpoint ℝ x y) s ^ 2 ≤
      (coveringRadius S x ^ 2 + coveringRadius S y ^ 2) / 2 -
        dist x y ^ 2 / 4 := by
    intro s hs
    have hpar := parallelogram_law_with_norm ℝ (x - s) (y - s)
    have hxs : dist x s ≤ coveringRadius S x :=
      dist_le_coveringRadius hbdd x hs
    have hys : dist y s ≤ coveringRadius S y :=
      dist_le_coveringRadius hbdd y hs
    have hmids : dist (midpoint ℝ x y) s =
        ‖(x - s) + (y - s)‖ / 2 := by
      rw [dist_eq_norm]
      rw [show midpoint ℝ x y - s =
          (2 : ℝ)⁻¹ • ((x - s) + (y - s)) from by
        rw [midpoint_eq_smul_add, invOf_eq_inv]
        module]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      ring
    have hd : dist x y = ‖(x - s) - (y - s)‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    have hx' : ‖x - s‖ = dist x s := (dist_eq_norm x s).symm
    have hy' : ‖y - s‖ = dist y s := (dist_eq_norm y s).symm
    have hxsq : dist x s ^ 2 ≤ coveringRadius S x ^ 2 := by
      have h0 : (0 : ℝ) ≤ dist x s := dist_nonneg
      nlinarith
    have hysq : dist y s ^ 2 ≤ coveringRadius S y ^ 2 := by
      have h0 : (0 : ℝ) ≤ dist y s := dist_nonneg
      nlinarith
    have hxn : ‖x - s‖ ^ 2 ≤ coveringRadius S x ^ 2 := by
      rw [hx']
      exact hxsq
    have hyn : ‖y - s‖ ^ 2 ≤ coveringRadius S y ^ 2 := by
      rw [hy']
      exact hysq
    rw [hmids]
    rw [div_pow]
    rw [hd]
    nlinarith [hpar, hxn, hyn, sq_nonneg (dist x y)]
  have h2 : coveringRadius S (midpoint ℝ x y) ^ 2 ≤
      (coveringRadius S x ^ 2 + coveringRadius S y ^ 2) / 2 -
        dist x y ^ 2 / 4 := by
    have hrad0 : 0 ≤ coveringRadius S (midpoint ℝ x y) :=
      coveringRadius_nonneg hne hbdd _
    have hbound : coveringRadius S (midpoint ℝ x y) ≤
        Real.sqrt ((coveringRadius S x ^ 2 +
          coveringRadius S y ^ 2) / 2 - dist x y ^ 2 / 4) := by
      apply coveringRadius_le hne
      intro s hs
      have := hmid s hs
      have h0 : (0 : ℝ) ≤ dist (midpoint ℝ x y) s := dist_nonneg
      calc
        dist (midpoint ℝ x y) s =
            Real.sqrt (dist (midpoint ℝ x y) s ^ 2) := by
          rw [Real.sqrt_sq h0]
        _ ≤ Real.sqrt ((coveringRadius S x ^ 2 +
            coveringRadius S y ^ 2) / 2 - dist x y ^ 2 / 4) :=
          Real.sqrt_le_sqrt this
    have hsqrtnn : (0 : ℝ) ≤ (coveringRadius S x ^ 2 +
        coveringRadius S y ^ 2) / 2 - dist x y ^ 2 / 4 := by
      obtain ⟨s, hs⟩ := hne
      have := hmid s hs
      nlinarith [sq_nonneg (dist (midpoint ℝ x y) s)]
    calc
      coveringRadius S (midpoint ℝ x y) ^ 2 ≤
          Real.sqrt ((coveringRadius S x ^ 2 +
            coveringRadius S y ^ 2) / 2 - dist x y ^ 2 / 4) ^ 2 := by
        have := hbound
        nlinarith [Real.sqrt_nonneg ((coveringRadius S x ^ 2 +
          coveringRadius S y ^ 2) / 2 - dist x y ^ 2 / 4)]
      _ = (coveringRadius S x ^ 2 + coveringRadius S y ^ 2) / 2 -
          dist x y ^ 2 / 4 := Real.sq_sqrt hsqrtnn
  linarith

/-- The Chebyshev radius of a set. -/
noncomputable def chebyshevRadius (S : Set E) : ℝ :=
  ⨅ x : E, coveringRadius S x

omit [InnerProductSpace ℝ E] in
theorem coveringRadius_bddBelow (S : Set E) (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) :
    BddBelow (Set.range (coveringRadius S)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact coveringRadius_nonneg hne hbdd y

omit [InnerProductSpace ℝ E] in
theorem chebyshevRadius_le {S : Set E} (hne : S.Nonempty)
    (hbdd : Bornology.IsBounded S) (x : E) :
    chebyshevRadius S ≤ coveringRadius S x :=
  ciInf_le (coveringRadius_bddBelow S hne hbdd) x

omit [InnerProductSpace ℝ E] in
theorem exists_coveringRadius_lt {S : Set E} [Nonempty E] {r : ℝ}
    (hr : chebyshevRadius S < r) :
    ∃ x : E, coveringRadius S x < r := by
  by_contra hall
  push Not at hall
  have hge : r ≤ chebyshevRadius S := le_ciInf hall
  linarith

/-- **Existence and uniqueness of the Chebyshev center** of a nonempty
bounded set in a complete real inner product space. -/
theorem existsUnique_center [CompleteSpace E] {S : Set E}
    (hne : S.Nonempty) (hbdd : Bornology.IsBounded S) :
    ∃! c : E, coveringRadius S c = chebyshevRadius S := by
  obtain ⟨s₀, hs₀⟩ := id hne
  haveI : Nonempty E := ⟨s₀⟩
  set ρ := chebyshevRadius S with hρ
  have hρ0 : 0 ≤ ρ := by
    rw [hρ, chebyshevRadius]
    exact le_ciInf fun x ↦ coveringRadius_nonneg hne hbdd x
  have hseq : ∀ n : ℕ, ∃ x : E,
      coveringRadius S x < ρ + 1 / (n + 1) := by
    intro n
    apply exists_coveringRadius_lt
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose x hx using hseq
  have hsep : ∀ y z : E, dist y z ^ 2 ≤
      2 * coveringRadius S y ^ 2 + 2 * coveringRadius S z ^ 2 -
        4 * ρ ^ 2 := by
    intro y z
    have hmid := coveringRadius_midpoint_sq hne hbdd y z
    have hmin : ρ ≤ coveringRadius S (midpoint ℝ y z) :=
      chebyshevRadius_le hne hbdd _
    have hmidnn : 0 ≤ coveringRadius S (midpoint ℝ y z) :=
      coveringRadius_nonneg hne hbdd _
    nlinarith
  have hdist_sq : ∀ m n : ℕ, dist (x m) (x n) ^ 2 ≤
      8 * (ρ + 1) * (1 / (m + 1) + 1 / (n + 1)) := by
    intro m n
    have h1 := hsep (x m) (x n)
    have h2 := (hx m).le
    have h3 := (hx n).le
    have h4 : 0 ≤ coveringRadius S (x m) :=
      coveringRadius_nonneg hne hbdd _
    have h5 : 0 ≤ coveringRadius S (x n) :=
      coveringRadius_nonneg hne hbdd _
    have hm1 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hn1 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hm2 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
    have hn2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    nlinarith
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (16 * (ρ + 1) / ε ^ 2)
    refine ⟨N, fun n hn m hm ↦ ?_⟩
    have hm1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
    have hn1 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        linarith
    have hd := hdist_sq n m
    have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hkey : 16 * (ρ + 1) / ((N : ℝ) + 1) < ε ^ 2 := by
      rw [div_lt_iff₀ hNpos]
      have h16 : (0 : ℝ) < 16 * (ρ + 1) := by nlinarith
      have hN2 : 16 * (ρ + 1) / ε ^ 2 < (N : ℝ) := hN
      have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
      rw [div_lt_iff₀ hε2] at hN2
      nlinarith
    have hd2 : dist (x n) (x m) ^ 2 < ε ^ 2 := by
      have h8 : (0 : ℝ) ≤ 8 * (ρ + 1) := by nlinarith
      calc
        dist (x n) (x m) ^ 2 ≤
            8 * (ρ + 1) * (1 / (n + 1) + 1 / (m + 1)) := hd
        _ ≤ 8 * (ρ + 1) * (2 / ((N : ℝ) + 1)) := by
          have : 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) ≤
              2 / ((N : ℝ) + 1) := by
            rw [show (2 : ℝ) / ((N : ℝ) + 1) =
              1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) by ring]
            linarith
          nlinarith
        _ = 16 * (ρ + 1) / ((N : ℝ) + 1) := by ring
        _ < ε ^ 2 := hkey
    nlinarith [dist_nonneg (x := x n) (y := x m)]
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hrc : coveringRadius S c = ρ := by
    apply le_antisymm
    · by_contra hgt
      push Not at hgt
      set η := coveringRadius S c - ρ with hη
      have hηpos : 0 < η := by
        rw [hη]
        linarith
      obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, 1 / ((n : ℝ) + 1) < η / 2 ∧
          dist c (x n) < η / 2 := by
        obtain ⟨n₁, hn₁⟩ := exists_nat_gt (2 / η)
        have hd := Metric.tendsto_atTop.1 hc (η / 2) (by linarith)
        obtain ⟨n₂, hn₂⟩ := hd
        refine ⟨max n₁ n₂, ?_, ?_⟩
        · have hle : (n₁ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by
            exact_mod_cast le_max_left n₁ n₂
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hηpos] at hn₁
          nlinarith
        · rw [dist_comm]
          exact hn₂ (max n₁ n₂) (le_max_right n₁ n₂)
      have hlip := coveringRadius_lipschitz hne hbdd c (x n)
      have := (hx n).le
      have : coveringRadius S c ≤ ρ + 1 / (n + 1) + dist c (x n) := by
        calc
          coveringRadius S c ≤ coveringRadius S (x n) + dist c (x n) :=
            hlip
          _ ≤ ρ + 1 / (n + 1) + dist c (x n) := by linarith
      rw [hη] at hηpos hn1
      linarith
    · exact chebyshevRadius_le hne hbdd c
  refine ⟨c, hrc, ?_⟩
  intro c' hc'
  have hd := hsep c' c
  rw [hrc, hc'] at hd
  have : dist c' c ^ 2 ≤ 0 := by linarith
  have : dist c' c = 0 := by
    nlinarith [dist_nonneg (x := c') (y := c)]
  exact dist_eq_zero.1 this

omit [InnerProductSpace ℝ E] in
/-- Covering radii transform along isometries. -/
theorem coveringRadius_image {f : E → E} (hf : Isometry f)
    (S : Set E) (x : E) :
    coveringRadius (f '' S) (f x) = coveringRadius S x := by
  unfold coveringRadius
  congr 1
  ext r
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, (hf.dist_eq x s).symm⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨f s, ⟨s, hs, rfl⟩, hf.dist_eq x s⟩

/-- **Every isometric action with a bounded orbit has a fixed point**:
the Chebyshev center of the orbit. -/
theorem exists_fixed_of_bounded_orbit [CompleteSpace E] {G : Type*}
    [Group G] (φ : G → E → E) (hiso : ∀ g, Isometry (φ g))
    (hmul : ∀ g h x, φ (g * h) x = φ g (φ h x))
    (hone : ∀ x : E, φ 1 x = x) (x₀ : E)
    (hbdd : Bornology.IsBounded (Set.range fun g ↦ φ g x₀)) :
    ∃ c : E, ∀ g : G, φ g c = c := by
  set S := Set.range fun g ↦ φ g x₀ with hS
  have hne : S.Nonempty := ⟨x₀, 1, hone x₀⟩
  have hinv : ∀ g : G, φ g '' S = S := by
    intro g
    ext y
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      refine ⟨g * h, ?_⟩
      show φ (g * h) x₀ = φ g (φ h x₀)
      exact hmul g h x₀
    · rintro ⟨h, rfl⟩
      exact ⟨φ (g⁻¹ * h) x₀, ⟨g⁻¹ * h, rfl⟩, by
        rw [← hmul, mul_inv_cancel_left]⟩
  obtain ⟨c, hc, hcuniq⟩ := existsUnique_center hne hbdd
  refine ⟨c, fun g ↦ ?_⟩
  apply hcuniq
  calc
    coveringRadius S (φ g c) = coveringRadius (φ g '' S) (φ g c) := by
      rw [hinv g]
    _ = coveringRadius S c := coveringRadius_image (hiso g) S c
    _ = chebyshevRadius S := hc

end Circumcenter
end NonsoficGroupsExist
