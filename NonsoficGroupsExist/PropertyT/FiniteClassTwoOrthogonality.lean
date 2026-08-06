import NonsoficGroupsExist.PropertyT.FiniteGroupAverage
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Ring.GeomSum

/-!
# The central-fixed part of the finite class-two angle estimate

For two subgroups generating a finite class-two group, the components of
their fixed spaces on which the commutator subgroup acts trivially are
exactly orthogonal in a representation without invariant vectors.  This is
the zero-angle half of the finite-stage argument; the complementary central
moving part carries the quantitative `1 / sqrt 2` estimate.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

universe u v

namespace FiniteClassTwoOrthogonality

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Standard irreducibility for an orthogonal representation, expressed in
the lattice of invariant real linear subspaces. -/
def IsOrthogonallyIrreducible (rho : G →* (E ≃ₗᵢ[ℝ] E)) : Prop :=
  Nontrivial E ∧
    ∀ U : Submodule ℝ E,
      (∀ g : G, ∀ z ∈ U, rho g z ∈ U) → U = ⊥ ∨ U = ⊤

/-- In an irreducible orthogonal representation, a central element either
acts trivially or has no fixed vectors.  This characteristic-free dichotomy
is the starting point for the finite-order central-character argument. -/
theorem central_eq_one_or_fixedSubmodule_bot
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (hirr : IsOrthogonallyIrreducible rho) {c : G}
    (hc : c ∈ Subgroup.center G) :
    rho c = 1 ∨
      (rho c).toLinearEquiv.toLinearMap.fixedSubmodule = ⊥ := by
  let U : Submodule ℝ E :=
    (rho c).toLinearEquiv.toLinearMap.fixedSubmodule
  have hUinv : ∀ g : G, ∀ z ∈ U, rho g z ∈ U := by
    intro g z hz
    change rho c z = z at hz
    change rho c (rho g z) = rho g z
    have hcg : c * g = g * c := (Subgroup.mem_center_iff.mp hc g).symm
    calc
      rho c (rho g z) = rho (c * g) z := by
        change (rho c * rho g) z = rho (c * g) z
        rw [← map_mul]
      _ = rho (g * c) z := by rw [hcg]
      _ = rho g (rho c z) := by
        change rho (g * c) z = (rho g * rho c) z
        rw [map_mul]
      _ = rho g z := by rw [hz]
  rcases hirr.2 U hUinv with hbot | htop
  · exact Or.inr hbot
  · left
    ext z
    have hzU : z ∈ U := by rw [htop]; exact Submodule.mem_top
    change rho c z = z at hzU
    simpa using hzU

/-- If a finite-order linear operator has no fixed vectors, its full cyclic
orbit sum vanishes.  This replaces the sign-eigenvalue shortcut available only for
central involutions. -/
theorem geomSum_apply_eq_zero_of_fixedSubmodule_bot
    (T : Module.End ℝ E) (n : ℕ) (hpow : T ^ n = 1)
    (hbot : T.fixedSubmodule = ⊥) (z : E) :
    (∑ i ∈ Finset.range n, T ^ i) z = 0 := by
  let S : Module.End ℝ E := ∑ i ∈ Finset.range n, T ^ i
  have hprod : (T - 1) * S = 0 := by
    simpa [S, hpow] using mul_geom_sum T n
  have hfixed : T (S z) = S z := by
    have hz := LinearMap.congr_fun hprod z
    change T (S z) - S z = 0 at hz
    exact sub_eq_zero.mp hz
  have hmem : S z ∈ T.fixedSubmodule := hfixed
  rw [hbot] at hmem
  have hz0 : S z = 0 := by simpa using hmem
  change S z = 0
  exact hz0

/-- A central involution acts by `+1` or `-1` in an irreducible real
orthogonal representation. -/
theorem central_involution_scalar
    (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (hirr : IsOrthogonallyIrreducible rho) {c : G}
    (hc : c ∈ Subgroup.center G) (hcsq : c ^ 2 = 1) :
    rho c = 1 ∨ ∀ z : E, rho c z = -z := by
  let U : Submodule ℝ E :=
    (rho c).toLinearEquiv.toLinearMap.fixedSubmodule
  rcases central_eq_one_or_fixedSubmodule_bot rho hirr hc with htrivial | hbot
  · exact Or.inl htrivial
  · right
    change U = ⊥ at hbot
    intro z
    have hfixed : rho c (rho c z + z) = rho c z + z := by
      calc
        rho c (rho c z + z) = rho c (rho c z) + rho c z := by rw [map_add]
        _ = rho (c * c) z + rho c z := by
          congr 1
          change (rho c * rho c) z = rho (c * c) z
          rw [← map_mul]
        _ = z + rho c z := by rw [← pow_two, hcsq]; simp
        _ = rho c z + z := add_comm _ _
    have hmem : rho c z + z ∈ U := hfixed
    rw [hbot] at hmem
    have hz0 : rho c z + z = 0 := by simpa using hmem
    exact eq_neg_of_add_eq_zero_left hz0

/-- The subgroup of `X` whose represented operators commute with the
represented image of `Y`.  On a scalar central-character summand this is
the radical of the commutator pairing. -/
def representationRadical
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G) : Subgroup X :=
  (Subgroup.centralizer (Y.map rho : Set (E ≃ₗᵢ[ℝ] E))).comap
    (rho.comp X.subtype)

theorem mem_representationRadical_iff
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G) (x : X) :
    x ∈ representationRadical rho X Y ↔
      ∀ y ∈ Y, rho y * rho x.1 = rho x.1 * rho y := by
  constructor
  · intro hx y hy
    change rho x.1 ∈
      Subgroup.centralizer (Y.map rho : Set (E ≃ₗᵢ[ℝ] E)) at hx
    exact (Subgroup.mem_centralizer_iff.mp hx) (rho y)
      (Subgroup.mem_map_of_mem rho hy)
  · intro hx
    change rho x.1 ∈
      Subgroup.centralizer (Y.map rho : Set (E ≃ₗᵢ[ℝ] E))
    rw [Subgroup.mem_centralizer_iff]
    intro T hT
    obtain ⟨y, hy, rfl⟩ := hT
    exact hx y hy

theorem mem_representationRadical_iff_commutator
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G) (x : X) :
    x ∈ representationRadical rho X Y ↔
      ∀ y ∈ Y, rho ⁅y, x.1⁆ = 1 := by
  rw [mem_representationRadical_iff]
  apply forall₂_congr
  intro y hy
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]

/-- A nontrivial finite group has at least twice as many elements as any
proper subgroup. -/
theorem twice_natCard_le_of_ne_top {K : Type*} [Group K] [Finite K]
    (R : Subgroup K) (hR : R ≠ ⊤) :
    2 * Nat.card R ≤ Nat.card K := by
  have hindex : 2 ≤ R.index := by
    exact Subgroup.one_lt_index_of_ne_top hR
  rw [← R.card_mul_index, mul_comm 2 (Nat.card R)]
  exact Nat.mul_le_mul_left (Nat.card R) hindex

/-- On a scalar central-character summand, a correlation coefficient outside
the radical vanishes.  Conjugating by a `Y`-element leaves the coefficient
unchanged because `v` is `Y`-fixed, while the corresponding nontrivial
commutator acts by negation. -/
theorem inner_translate_eq_zero_of_not_mem_radical
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G)
    (hscalar : ∀ y ∈ Y, ∀ x ∈ X,
      rho ⁅y, x⁆ = 1 ∨ ∀ z : E, rho ⁅y, x⁆ z = -z)
    {v : E} (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y)
    (x : X) (hx : x ∉ representationRadical rho X Y) :
    inner ℝ (rho x.1 v) v = 0 := by
  rw [mem_representationRadical_iff_commutator] at hx
  push Not at hx
  obtain ⟨y, hy, hnontrivial⟩ := hx
  have hneg : ∀ z : E, rho ⁅y, x.1⁆ z = -z :=
    (hscalar y hy x.1 x.2).resolve_left hnontrivial
  have hyfix : rho y v = v :=
    (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY y hy
  have hyinvfix : rho y⁻¹ v = v :=
    (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY y⁻¹
      (Y.inv_mem hy)
  have hop : rho (y * x.1 * y⁻¹) v = rho y (rho x.1 v) := by
    calc
      rho (y * x.1 * y⁻¹) v =
          rho y (rho x.1 (rho y⁻¹ v)) := by
            change rho (y * x.1 * y⁻¹) v =
              (rho y * rho x.1 * rho y⁻¹) v
            simp only [map_mul]
      _ = rho y (rho x.1 v) := by rw [hyinvfix]
  have hconj : inner ℝ (rho (y * x.1 * y⁻¹) v) v =
      inner ℝ (rho x.1 v) v := by
    calc
      inner ℝ (rho (y * x.1 * y⁻¹) v) v =
          inner ℝ (rho y (rho x.1 v)) (rho y v) := by rw [hop, hyfix]
      _ = inner ℝ (rho x.1 v) v := (rho y).inner_map_map _ _
  have hnegconj : rho (y * x.1 * y⁻¹) v = -(rho x.1 v) := by
    calc
      rho (y * x.1 * y⁻¹) v = rho (⁅y, x.1⁆ * x.1) v := by
        congr 2
        exact conj_eq_commutatorElement_mul
      _ = rho ⁅y, x.1⁆ (rho x.1 v) := by
        change rho (⁅y, x.1⁆ * x.1) v =
          (rho ⁅y, x.1⁆ * rho x.1) v
        rw [map_mul]
      _ = -(rho x.1 v) := hneg _
  rw [hnegconj, inner_neg_left] at hconj
  linarith

/-- Characteristic-free version of the vanishing correlation argument on an
irreducible summand.  Instead of requiring a central commutator to act by
`-1`, average its whole finite cyclic orbit. -/
theorem inner_translate_eq_zero_of_not_mem_radical_of_irreducible
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y C : Subgroup G)
    (n : ℕ) (hn : 0 < n)
    (hcomm : ⁅Y, X⁆ ≤ C) (hcentral : C ≤ Subgroup.center G)
    (hexp : ∀ c ∈ C, c ^ n = 1)
    (hirr : IsOrthogonallyIrreducible rho)
    {v : E} (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y)
    (x : X) (hx : x ∉ representationRadical rho X Y) :
    inner ℝ (rho x.1 v) v = 0 := by
  rw [mem_representationRadical_iff_commutator] at hx
  push Not at hx
  obtain ⟨y, hy, hnontrivial⟩ := hx
  let c : G := ⁅y, x.1⁆
  have hcC : c ∈ C :=
    hcomm (Subgroup.commutator_mem_commutator hy x.2)
  have hcCentral : c ∈ Subgroup.center G := hcentral hcC
  have hcPow : c ^ n = 1 := hexp c hcC
  have hbot : (rho c).toLinearEquiv.toLinearMap.fixedSubmodule = ⊥ :=
    (central_eq_one_or_fixedSubmodule_bot rho hirr hcCentral).resolve_left
      hnontrivial
  let T : Module.End ℝ E := (rho c).toLinearEquiv.toLinearMap
  have hTpow_apply (i : ℕ) (z : E) : (T ^ i) z = rho (c ^ i) z := by
    induction i generalizing z with
    | zero => simp
    | succ i ih =>
        rw [pow_succ, pow_succ]
        change (T ^ i) (T z) = rho (c ^ i * c) z
        rw [ih]
        change rho (c ^ i) (rho c z) = rho (c ^ i * c) z
        rw [map_mul]
        rfl
  have hTpow : T ^ n = 1 := by
    ext z
    rw [hTpow_apply, hcPow]
    simp
  have hcy : Commute c y :=
    (Subgroup.mem_center_iff.mp hcCentral y).symm
  have hconjPow (i : ℕ) :
      y ^ i * x.1 * (y ^ i)⁻¹ = c ^ i * x.1 := by
    induction i with
    | zero => simp
    | succ i ih =>
        calc
          y ^ (i + 1) * x.1 * (y ^ (i + 1))⁻¹ =
              y * (y ^ i * x.1 * (y ^ i)⁻¹) * y⁻¹ := by group
          _ = y * (c ^ i * x.1) * y⁻¹ := by rw [ih]
          _ = c ^ i * (y * x.1 * y⁻¹) := by
            calc
              y * (c ^ i * x.1) * y⁻¹ = (y * c ^ i) * x.1 * y⁻¹ := by
                simp only [mul_assoc]
              _ = (c ^ i * y) * x.1 * y⁻¹ := by
                rw [(hcy.symm.pow_right i).eq]
              _ = c ^ i * (y * x.1 * y⁻¹) := by simp only [mul_assoc]
          _ = c ^ i * (c * x.1) := by
            rw [← conj_eq_commutatorElement_mul]
            rfl
          _ = c ^ (i + 1) * x.1 := by rw [pow_succ]; group
  have hinner (i : ℕ) :
      inner ℝ ((T ^ i) (rho x.1 v)) v = inner ℝ (rho x.1 v) v := by
    have hyPow : y ^ i ∈ Y := Y.pow_mem hy i
    have hyfix : rho (y ^ i) v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY _ hyPow
    have hyinvfix : rho (y ^ i)⁻¹ v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY _
        (Y.inv_mem hyPow)
    have hconj :
        inner ℝ (rho (y ^ i * x.1 * (y ^ i)⁻¹) v) v =
          inner ℝ (rho x.1 v) v := by
      calc
        inner ℝ (rho (y ^ i * x.1 * (y ^ i)⁻¹) v) v =
            inner ℝ (rho (y ^ i) (rho x.1 (rho (y ^ i)⁻¹ v))) v := by
              simp only [map_mul]
              rfl
        _ = inner ℝ (rho (y ^ i) (rho x.1 v)) (rho (y ^ i) v) := by
              rw [hyinvfix, hyfix]
        _ = inner ℝ (rho x.1 v) v := (rho (y ^ i)).inner_map_map _ _
    calc
      inner ℝ ((T ^ i) (rho x.1 v)) v =
          inner ℝ (rho (c ^ i * x.1) v) v := by
            rw [hTpow_apply, map_mul]
            rfl
      _ = inner ℝ (rho (y ^ i * x.1 * (y ^ i)⁻¹) v) v := by
            rw [hconjPow i]
      _ = inner ℝ (rho x.1 v) v := hconj
  have hsumZero :
      ∑ i ∈ Finset.range n, inner ℝ ((T ^ i) (rho x.1 v)) v = 0 := by
    have hzero := geomSum_apply_eq_zero_of_fixedSubmodule_bot
      T n hTpow (by simpa [T] using hbot) (rho x.1 v)
    have hinnerZero := congrArg (fun z : E ↦ inner ℝ z v) hzero
    rw [← sum_inner]
    simpa [map_sum] using hinnerZero
  have hnInner : (n : ℝ) * inner ℝ (rho x.1 v) v = 0 := by
    calc
      (n : ℝ) * inner ℝ (rho x.1 v) v =
          ∑ _i ∈ Finset.range n, inner ℝ (rho x.1 v) v := by simp
      _ = ∑ i ∈ Finset.range n,
          inner ℝ ((T ^ i) (rho x.1 v)) v := by
            apply Finset.sum_congr rfl
            intro i _
            exact (hinner i).symm
      _ = 0 := hsumZero
  exact (mul_eq_zero.mp hnInner).resolve_left (by exact_mod_cast hn.ne')

/-- Once correlations vanish outside the represented commutator radical,
averaging a `Y`-fixed vector over `X` decreases squared norm by at least a
factor of two. -/
theorem norm_orbitAverage_sq_le_half_of_vanishing
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G) [Finite X] {v : E}
    (hvanish : ∀ x : X, x ∉ representationRadical rho X Y →
      inner ℝ (rho x.1 v) v = 0)
    (hradical : representationRadical rho X Y ≠ ⊤) :
    ‖FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation rho X) v‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
  classical
  letI := Fintype.ofFinite X
  let rhoX := KazhdanFixedSpace.restrictRepresentation rho X
  let R := representationRadical rho X Y
  let w := FiniteGroupAverage.orbitAverage rhoX v
  have hwfixed : ∀ x : X, rhoX x w = w :=
    fun x ↦ FiniteGroupAverage.orbitAverage_fixed rhoX v x
  have hnorminner : ‖w‖ ^ 2 = inner ℝ w v := by
    have h := FiniteGroupAverage.inner_orbitAverage_eq_of_fixed_right
      rhoX v w hwfixed
    change inner ℝ w w = inner ℝ v w at h
    rw [real_inner_self_eq_norm_sq] at h
    exact h.trans (real_inner_comm w v)
  have hcardR : (Finset.univ.filter fun x : X ↦ x ∈ R).card = Nat.card R := by
    rw [← Fintype.card_subtype (fun x : X ↦ x ∈ R),
      Nat.card_eq_fintype_card]
  have hsum_eq :
      ∑ x : X, inner ℝ (rho x.1 v) v =
        ∑ x ∈ Finset.univ.filter (fun x : X ↦ x ∈ R),
          inner ℝ (rho x.1 v) v := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hvanish x hx
  have hterm (x : X) : inner ℝ (rho x.1 v) v ≤ ‖v‖ ^ 2 := by
    calc
      inner ℝ (rho x.1 v) v ≤ |inner ℝ (rho x.1 v) v| := le_abs_self _
      _ ≤ ‖rho x.1 v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = ‖v‖ ^ 2 := by rw [(rho x.1).norm_map]; ring
  have hsum :
      ∑ x : X, inner ℝ (rho x.1 v) v ≤
        (Nat.card R : ℝ) * ‖v‖ ^ 2 := by
    rw [hsum_eq]
    calc
      ∑ x ∈ Finset.univ.filter (fun x : X ↦ x ∈ R),
          inner ℝ (rho x.1 v) v ≤
          ∑ _x ∈ Finset.univ.filter (fun x : X ↦ x ∈ R), ‖v‖ ^ 2 := by
            exact Finset.sum_le_sum fun x _ ↦ hterm x
      _ = ((Finset.univ.filter fun x : X ↦ x ∈ R).card : ℝ) * ‖v‖ ^ 2 := by
            simp
      _ = (Nat.card R : ℝ) * ‖v‖ ^ 2 := by rw [hcardR]
  have hXpos : (0 : ℝ) < Nat.card X := by exact_mod_cast (Nat.card_pos (α := X))
  have hcardNat : 2 * Nat.card R ≤ Nat.card X :=
    twice_natCard_le_of_ne_top R hradical
  have hcardReal : (2 : ℝ) * Nat.card R ≤ Nat.card X := by
    exact_mod_cast hcardNat
  have hratio : (Nat.card X : ℝ)⁻¹ * Nat.card R ≤ (1 / 2 : ℝ) := by
    rw [inv_mul_le_iff₀ hXpos]
    nlinarith
  calc
    ‖FiniteGroupAverage.orbitAverage rhoX v‖ ^ 2 = ‖w‖ ^ 2 := rfl
    _ = inner ℝ w v := hnorminner
    _ = (Nat.card X : ℝ)⁻¹ *
        ∑ x : X, inner ℝ (rho x.1 v) v := by
          unfold w FiniteGroupAverage.orbitAverage
          rw [real_inner_smul_left, sum_inner]
          rfl
    _ ≤ (Nat.card X : ℝ)⁻¹ * ((Nat.card R : ℝ) * ‖v‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hXpos.le)
    _ = ((Nat.card X : ℝ)⁻¹ * Nat.card R) * ‖v‖ ^ 2 := by ring
    _ ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hratio (sq_nonneg ‖v‖)

/-- If the represented commutator pairing has full radical, the `X`-average
of a `Y`-fixed vector is globally invariant and hence vanishes in a
representation without invariant vectors. -/
theorem orbitAverage_eq_zero_of_radical_eq_top
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G) [Finite X]
    (hgen : X ⊔ Y = ⊤)
    (hradical : representationRadical rho X Y = ⊤)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    {v : E} (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation rho X) v = 0 := by
  let rhoX := KazhdanFixedSpace.restrictRepresentation rho X
  let w := FiniteGroupAverage.orbitAverage rhoX v
  have hwX : w ∈ KazhdanFixedSpace.fixedSubspace rho X := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro x hx
    exact FiniteGroupAverage.orbitAverage_fixed rhoX v ⟨x, hx⟩
  have hwY : w ∈ KazhdanFixedSpace.fixedSubspace rho Y := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro y hy
    letI := Fintype.ofFinite X
    unfold w FiniteGroupAverage.orbitAverage
    rw [map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    have hxrad : x ∈ representationRadical rho X Y := by rw [hradical]; trivial
    have hcommute : rho y * rho x.1 = rho x.1 * rho y :=
      (mem_representationRadical_iff rho X Y x).mp hxrad y hy
    have hyfix : rho y v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY y hy
    change rho y (rho x.1 v) = rho x.1 v
    calc
      rho y (rho x.1 v) = (rho y * rho x.1) v := rfl
      _ = (rho x.1 * rho y) v := by rw [hcommute]
      _ = rho x.1 (rho y v) := rfl
      _ = rho x.1 v := by rw [hyfix]
  have hwTop : w ∈ KazhdanFixedSpace.fixedSubspace rho ⊤ := by
    rw [← hgen, KazhdanFixedSpace.fixedSubspace_sup]
    exact ⟨hwX, hwY⟩
  change w = 0
  apply hno w
  intro g
  exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho ⊤ w).mp hwTop
    g (Subgroup.mem_top g)

/-- The squared-norm half estimate for either scalar-character case. -/
theorem norm_orbitAverage_sq_le_half_of_scalar
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G) [Finite X]
    (hgen : X ⊔ Y = ⊤)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    (hscalar : ∀ y ∈ Y, ∀ x ∈ X,
      rho ⁅y, x⁆ = 1 ∨ ∀ z : E, rho ⁅y, x⁆ z = -z)
    {v : E} (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    ‖FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation rho X) v‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
  by_cases hradical : representationRadical rho X Y = ⊤
  · rw [orbitAverage_eq_zero_of_radical_eq_top
      rho X Y hgen hradical hno hvY]
    rw [norm_zero, zero_pow (by norm_num)]
    exact mul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (sq_nonneg ‖v‖)
  · exact norm_orbitAverage_sq_le_half_of_vanishing
      rho X Y (fun x hx ↦
        inner_translate_eq_zero_of_not_mem_radical
          rho X Y hscalar hvY x hx) hradical

/-- The same half-norm estimate on an irreducible summand for central
commutators of any one positive finite exponent. -/
theorem norm_orbitAverage_sq_le_half_of_irreducible_finiteOrder
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y C : Subgroup G) [Finite X]
    (n : ℕ) (hn : 0 < n)
    (hgen : X ⊔ Y = ⊤) (hcomm : ⁅Y, X⁆ ≤ C)
    (hcentral : C ≤ Subgroup.center G) (hexp : ∀ c ∈ C, c ^ n = 1)
    (hirr : IsOrthogonallyIrreducible rho)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    {v : E} (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    ‖FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation rho X) v‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
  by_cases hradical : representationRadical rho X Y = ⊤
  · rw [orbitAverage_eq_zero_of_radical_eq_top
      rho X Y hgen hradical hno hvY]
    rw [norm_zero, zero_pow (by norm_num)]
    exact mul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (sq_nonneg ‖v‖)
  · exact norm_orbitAverage_sq_le_half_of_vanishing
      rho X Y (fun x hx ↦
        inner_translate_eq_zero_of_not_mem_radical_of_irreducible
          rho X Y C n hn hcomm hcentral hexp hirr hvY x hx)
      hradical

/-- Passing from the squared half estimate to the `1 / sqrt 2` norm
estimate. -/
theorem le_inv_sqrt_two_mul_of_sq_le_half {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ (1 / 2 : ℝ) * b ^ 2) :
    a ≤ (Real.sqrt 2)⁻¹ * b := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hinv : 0 ≤ (Real.sqrt 2)⁻¹ := inv_nonneg.mpr hsqrt.le
  have hsquare : ((Real.sqrt 2)⁻¹ * b) ^ 2 = (1 / 2 : ℝ) * b ^ 2 := by
    have hsqrtSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    field_simp
    rw [hsqrtSq]
    ring
  have hsq : a ^ 2 ≤ ((Real.sqrt 2)⁻¹ * b) ^ 2 := by
    rwa [hsquare]
  exact (sq_le_sq₀ ha (mul_nonneg hinv hb)).mp hsq

/-- The `1 / sqrt 2` averaging estimate in an irreducible real summand of a
finite class-two group with central commutators of one positive bounded
exponent. -/
theorem norm_orbitAverage_le_inv_sqrt_two_of_irreducible
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y C : Subgroup G) [Finite X]
    (n : ℕ) (hn : 0 < n)
    (hgen : X ⊔ Y = ⊤)
    (hcomm : ⁅Y, X⁆ ≤ C)
    (hcentral : C ≤ Subgroup.center G)
    (hexp : ∀ c ∈ C, c ^ n = 1)
    (hirr : IsOrthogonallyIrreducible rho)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    {v : E} (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y) :
    ‖FiniteGroupAverage.orbitAverage
        (KazhdanFixedSpace.restrictRepresentation rho X) v‖ ≤
      (Real.sqrt 2)⁻¹ * ‖v‖ := by
  apply le_inv_sqrt_two_mul_of_sq_le_half (norm_nonneg _) (norm_nonneg _)
  exact norm_orbitAverage_sq_le_half_of_irreducible_finiteOrder
    rho X Y C n hn hgen hcomm hcentral hexp hirr hno hvY

/-- On the part fixed by the commutator subgroup, the fixed spaces of the
two generating subgroups are orthogonal.  The proof uses the literal finite
average over `X`: modulo `C`, every point in the `X`-orbit of a `Y`-fixed
vector is still `Y`-fixed. -/
theorem inner_eq_zero_of_fixed_center
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y C : Subgroup G) [Finite X]
    (hgen : X ⊔ Y = ⊤)
    (hcomm : ⁅Y, X⁆ ≤ C)
    (hXnorm : X ≤ Subgroup.normalizer (C : Set G))
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho)
    {u v : E}
    (huX : u ∈ KazhdanFixedSpace.fixedSubspace rho X)
    (hvY : v ∈ KazhdanFixedSpace.fixedSubspace rho Y)
    (hvC : v ∈ KazhdanFixedSpace.fixedSubspace rho C) :
    inner ℝ u v = 0 := by
  let rhoX := KazhdanFixedSpace.restrictRepresentation rho X
  let w : E := FiniteGroupAverage.orbitAverage rhoX v
  have hwX : w ∈ KazhdanFixedSpace.fixedSubspace rho X := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro x hx
    let xX : X := ⟨x, hx⟩
    exact FiniteGroupAverage.orbitAverage_fixed rhoX v xX
  have hwY : w ∈ KazhdanFixedSpace.fixedSubspace rho Y := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro y hy
    letI := Fintype.ofFinite X
    unfold w FiniteGroupAverage.orbitAverage
    rw [map_smul, map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    change rho y (rho x.1 v) = rho x.1 v
    let c : G := ⁅y, x.1⁆
    have hc : c ∈ C :=
      hcomm (Subgroup.commutator_mem_commutator hy x.2)
    have hcconj : x.1⁻¹ * c * x.1 ∈ C :=
      (Subgroup.mem_normalizer_iff''.mp (hXnorm x.2) c).mp hc
    have hyfix : rho y v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hvY y hy
    have hcfix : rho (x.1⁻¹ * c * x.1) v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho C v).mp hvC
        (x.1⁻¹ * c * x.1) hcconj
    calc
      rho y (rho x.1 v) = rho (y * x.1) v := by
        change (rho y * rho x.1) v = rho (y * x.1) v
        rw [← map_mul]
      _ = rho (c * x.1 * y) v := by
        congr 2
        simp [c, commutatorElement_def, mul_assoc]
      _ = rho c (rho x.1 (rho y v)) := by simp [map_mul]
      _ = rho c (rho x.1 v) := by rw [hyfix]
      _ = rho (c * x.1) v := by
        change (rho c * rho x.1) v = rho (c * x.1) v
        rw [← map_mul]
      _ = rho (x.1 * (x.1⁻¹ * c * x.1)) v := by
        congr 2
        group
      _ = rho x.1 (rho (x.1⁻¹ * c * x.1) v) := by
        change rho (x.1 * (x.1⁻¹ * c * x.1)) v =
          (rho x.1 * rho (x.1⁻¹ * c * x.1)) v
        rw [map_mul]
      _ = rho x.1 v := by rw [hcfix]
  have hwTop : w ∈ KazhdanFixedSpace.fixedSubspace rho ⊤ := by
    rw [← hgen, KazhdanFixedSpace.fixedSubspace_sup]
    exact ⟨hwX, hwY⟩
  have hw0 : w = 0 := by
    apply hno w
    intro g
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho ⊤ w).mp hwTop
      g (Subgroup.mem_top g)
  have huFixed : ∀ x : X, rhoX x u = u := by
    intro x
    exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho X u).mp huX x.1 x.2
  have havg := FiniteGroupAverage.inner_orbitAverage_eq_of_fixed_right
    rhoX v u huFixed
  change inner ℝ w u = inner ℝ v u at havg
  rw [hw0, inner_zero_left] at havg
  rw [real_inner_comm]
  exact havg.symm

end FiniteClassTwoOrthogonality
end NonsoficGroupsExist
