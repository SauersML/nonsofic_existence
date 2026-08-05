import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.FiniteType
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic.NoncommRing

/-!
# Elementary groups over a ring

This file formalizes Section `subsec:elementary` of the manuscript over an
arbitrary unital ring: the elementary matrices `x_{ij}(a) = I + a E_{ij}`, the
group `EL_r(A)` they generate, the Whitehead commutator identity in general
rank, finite generation of `EL_r(A)` over a finitely generated `𝔽₂`-algebra,
and the transport isomorphisms

  `EL_ι(M_κ(A)) ≅ EL_{ι×κ}(A)`,  `EL_ι(A) ≅ EL_κ(A)` for `ι ≃ κ`,
  `EL_ι(R) ≅ EL_ι(S)` for `R ≅ S`,

which are what spreads the conclusion across ranks in Section `sec:panorama`.
-/

namespace NonsoficGroupsExist

open scoped BigOperators commutatorElement

section Basic

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

theorem single_mul_self_eq_zero (i j : ι) (h : i ≠ j) (a : R) :
    Matrix.single i j a * Matrix.single i j a = 0 :=
  Matrix.single_mul_single_of_ne (c := a) i j i h.symm a

/-- The elementary matrix `x_{ij}(a)`, with its inverse written explicitly. -/
def elementaryUnit (i j : ι) (h : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 - Matrix.single i j a
  val_inv := by
    have hx := single_mul_self_eq_zero i j h a
    noncomm_ring [hx]
  inv_val := by
    have hx := single_mul_self_eq_zero i j h a
    noncomm_ring [hx]

@[simp] theorem elementaryUnit_zero (i j : ι) (h : i ≠ j) :
    elementaryUnit (R := R) i j h 0 = 1 := by
  apply Units.ext
  simp [elementaryUnit]

theorem elementaryUnit_mul (i j : ι) (h : i ≠ j) (a b : R) :
    elementaryUnit i j h a * elementaryUnit i j h b = elementaryUnit i j h (a + b) := by
  apply Units.ext
  change (1 + Matrix.single i j a) * (1 + Matrix.single i j b) =
    1 + Matrix.single i j (a + b)
  have hab : Matrix.single i j a * Matrix.single i j b = 0 :=
    Matrix.single_mul_single_of_ne (c := a) i j i h.symm b
  rw [Matrix.single_add]
  noncomm_ring [hab]

theorem elementaryUnit_injective (i j : ι) (h : i ≠ j) :
    Function.Injective (elementaryUnit (R := R) i j h) := by
  intro a b hab
  have he := congrArg (fun z : (Matrix ι ι R)ˣ ↦ (z : Matrix ι ι R) i j) hab
  simpa [elementaryUnit, Matrix.one_apply, h] using he

/-- `EL_ι(R)`. -/
def elementaryGroup (ι R : Type*) [Fintype ι] [DecidableEq ι] [Ring R] :
    Subgroup (Matrix ι ι R)ˣ :=
  Subgroup.closure
    {z | ∃ (i j : ι) (h : i ≠ j) (a : R), elementaryUnit i j h a = z}

theorem elementaryUnit_mem (i j : ι) (h : i ≠ j) (a : R) :
    elementaryUnit i j h a ∈ elementaryGroup ι R :=
  Subgroup.subset_closure ⟨i, j, h, a, rfl⟩

/-- **Lemma `lem:whitehead` in general rank**: the elementary commutator
identity `[x_{ij}(a), x_{jk}(b)] = x_{ik}(ab)`. -/
theorem elementaryUnit_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅elementaryUnit i j hij a, elementaryUnit j k hjk b⁆ =
      elementaryUnit i k hik (a * b) := by
  apply Units.ext
  change
    (1 + Matrix.single i j a) * (1 + Matrix.single j k b) *
      (1 - Matrix.single i j a) * (1 - Matrix.single j k b) =
      1 + Matrix.single i k (a * b)
  have hxx := single_mul_self_eq_zero i j hij a
  have hyy := single_mul_self_eq_zero j k hjk b
  have hyx : Matrix.single j k b * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := b) j k i hik.symm a
  have hxy : Matrix.single i j a * Matrix.single j k b =
      Matrix.single i k (a * b) :=
    Matrix.single_mul_single_same (c := a) i j k b
  have hzx : Matrix.single i k (a * b) * Matrix.single i j a = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k i hik.symm a
  have hzy : Matrix.single i k (a * b) * Matrix.single j k b = 0 :=
    Matrix.single_mul_single_of_ne (c := a * b) i k j hjk.symm b
  have hzz := single_mul_self_eq_zero i k hik (a * b)
  noncomm_ring [hxx, hyy, hyx, hxy, hzx, hzy, hzz]

/-- Two elementary memberships sharing an index produce a third. -/
theorem elementaryUnit_mem_of_two_step (H : Subgroup (Matrix ι ι R)ˣ)
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : R)
    (hleft : elementaryUnit i j hij a ∈ H)
    (hright : elementaryUnit j k hjk 1 ∈ H) :
    elementaryUnit i k hik a ∈ H := by
  have hc : ⁅elementaryUnit i j hij a, elementaryUnit j k hjk 1⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
      (H.inv_mem hright)
  rw [elementaryUnit_commutator i j k hij hjk hik a 1] at hc
  simpa using hc

theorem elementaryGroup_infinite [Infinite R] (i j : ι) (h : i ≠ j) :
    Infinite (elementaryGroup ι R) := by
  apply Infinite.of_injective
    (fun a : R ↦ (⟨elementaryUnit i j h a, elementaryUnit_mem i j h a⟩ :
      elementaryGroup ι R))
  intro a b hab
  exact elementaryUnit_injective i j h (congrArg Subtype.val hab)

end Basic

/-! ### Finite generation -/

section FiniteGeneration

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]

/-- The finite generating set of Lemma `lem:elfg`. -/
noncomputable def finiteElementaryGenerators [DecidableEq R] (n : ℕ)
    (s : Finset R) : Finset (Matrix (Fin n) (Fin n) R)ˣ :=
  Finset.univ.biUnion fun i : Fin n ↦
    Finset.univ.biUnion fun j : Fin n ↦
      if h : i ≠ j then (insert 1 s).image (elementaryUnit i j h) else ∅

omit [Algebra (ZMod 2) R] in
theorem mem_finiteElementaryGenerators [DecidableEq R] (n : ℕ) (s : Finset R)
    (z : (Matrix (Fin n) (Fin n) R)ˣ) :
    z ∈ finiteElementaryGenerators n s ↔
      ∃ (i j : Fin n) (h : i ≠ j) (a : R),
        a ∈ insert 1 s ∧ elementaryUnit i j h a = z := by
  constructor
  · intro hz
    unfold finiteElementaryGenerators at hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hi
    by_cases h : i ≠ j
    · rw [dif_pos h] at hj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
      exact ⟨i, j, h, a, ha, rfl⟩
    · rw [dif_neg h] at hj
      simp at hj
  · rintro ⟨i, j, h, a, ha, rfl⟩
    unfold finiteElementaryGenerators
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_univ j, ?_⟩
    rw [dif_pos h]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩

/-- The set of coefficients whose elementary matrices all lie in a fixed
subgroup is an `𝔽₂`-subalgebra; this is the engine of Lemma `lem:elfg`. -/
def elementaryCoefficientSubalgebra (n : ℕ) (hn : 2 < n)
    (H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hunit : ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h (1 : R) ∈ H) :
    Subalgebra (ZMod 2) R where
  carrier := {a | ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h a ∈ H}
  add_mem' := by
    intro a b ha hb i j hij
    rw [← elementaryUnit_mul]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
    have hik : i ≠ k := hki.symm
    have hc : ⁅elementaryUnit i k hik a, elementaryUnit k j hkj b⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem
        (H.mul_mem (H.mul_mem (ha i k hik) (hb k j hkj))
          (H.inv_mem (ha i k hik)))
        (H.inv_mem (hb k j hkj))
    rw [elementaryUnit_commutator i k j hik hkj hij a b] at hc
    exact hc
  algebraMap_mem' := by
    intro z
    have hz : z = 0 ∨ z = 1 := by
      fin_cases z
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hz with rfl | rfl
    · intro i j hij
      simpa only [map_zero, elementaryUnit_zero] using H.one_mem
    · intro i j hij
      simpa only [map_one] using hunit i j hij

/-- **Lemma `lem:elfg`.**  `EL_n(R)` is finitely generated whenever `R` is a
finitely generated `𝔽₂`-algebra and `n ≥ 3`. -/
theorem elementaryGroup_finitelyGenerated [Algebra.FiniteType (ZMod 2) R]
    (n : ℕ) (hn : 2 < n) : Group.FG (elementaryGroup (Fin n) R) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ZMod 2) (A := R)
  set t : Finset (Matrix (Fin n) (Fin n) R)ˣ := finiteElementaryGenerators n s
  set H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ :=
    Subgroup.closure (t : Set (Matrix (Fin n) (Fin n) R)ˣ)
  have hunit : ∀ (i j : Fin n) (h : i ≠ j),
      elementaryUnit i j h (1 : R) ∈ H := by
    intro i j hij
    apply Subgroup.subset_closure
    exact (mem_finiteElementaryGenerators n s _).mpr
      ⟨i, j, hij, 1, Finset.mem_insert_self 1 s, rfl⟩
  set C : Subalgebra (ZMod 2) R :=
    elementaryCoefficientSubalgebra n hn H hunit
  have hgen : (s : Set R) ⊆ (C : Set R) := by
    intro a ha i j hij
    apply Subgroup.subset_closure
    exact (mem_finiteElementaryGenerators n s _).mpr
      ⟨i, j, hij, a, Finset.mem_insert_of_mem ha, rfl⟩
  have hC : C = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_le hgen
  have heq : H = elementaryGroup (Fin n) R := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      obtain ⟨i, j, hij, a, -, rfl⟩ :=
        (mem_finiteElementaryGenerators n s z).mp hz
      exact elementaryUnit_mem i j hij a
    · rw [elementaryGroup, Subgroup.closure_le]
      rintro _ ⟨i, j, hij, a, rfl⟩
      have ha : a ∈ C := by simp [hC]
      exact ha i j hij
  apply (Group.fg_iff_subgroup_fg (elementaryGroup (Fin n) R)).mpr
  exact ⟨t, heq⟩

end FiniteGeneration

/-! ### Transport across ranks and coefficients -/

section Transport

variable {ι κ R S : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R] [Ring S]

/-- Elementary groups are functorial for ring homomorphisms. -/
def elementaryMatrixUnitMap (f : R →+* S) :
    (Matrix ι ι R)ˣ →* (Matrix ι ι S)ˣ :=
  Units.map f.mapMatrix.toMonoidHom

theorem elementaryMatrixUnitMap_elementaryUnit (f : R →+* S) (i j : ι)
    (hij : i ≠ j) (a : R) :
    elementaryMatrixUnitMap f (elementaryUnit i j hij a) =
      elementaryUnit i j hij (f a) := by
  apply Units.ext
  change f.mapMatrix (1 + Matrix.single i j a) = 1 + Matrix.single i j (f a)
  rw [map_add, map_one]
  congr 1
  ext k l
  change f (if i = k ∧ j = l then a else 0) =
    if i = k ∧ j = l then f a else 0
  split_ifs <;> simp

/-- Entrywise coefficient maps carry the elementary group into the elementary
group, without any surjectivity assumption on the coefficient map. -/
theorem elementaryGroup_map_le (f : R →+* S) :
    (elementaryGroup ι R).map (elementaryMatrixUnitMap f) ≤
      elementaryGroup ι S := by
  rw [elementaryGroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  change elementaryMatrixUnitMap f (elementaryUnit i j hij a) ∈
    elementaryGroup ι S
  rw [elementaryMatrixUnitMap_elementaryUnit]
  exact elementaryUnit_mem i j hij (f a)

theorem elementaryGroup_map_eq_of_surjective (f : R →+* S)
    (hf : Function.Surjective f) :
    (elementaryGroup ι R).map (elementaryMatrixUnitMap f) = elementaryGroup ι S := by
  apply le_antisymm
  · exact elementaryGroup_map_le f
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, b, rfl⟩
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a,
      elementaryMatrixUnitMap_elementaryUnit f i j hij a⟩

/-- The group homomorphism on elementary groups induced by a coefficient-ring
homomorphism. -/
def elementaryGroupMap (f : R →+* S) :
    elementaryGroup ι R →* elementaryGroup ι S :=
  ((elementaryMatrixUnitMap f).comp (elementaryGroup ι R).subtype).codRestrict
    (elementaryGroup ι S) fun g ↦
      elementaryGroup_map_le f
        (Subgroup.apply_coe_mem_map (elementaryMatrixUnitMap f)
          (elementaryGroup ι R) g)

@[simp] theorem elementaryGroupMap_apply (f : R →+* S)
    (g : elementaryGroup ι R) :
    (elementaryGroupMap f g : (Matrix ι ι S)ˣ) =
      elementaryMatrixUnitMap f g := rfl

/-- A surjective coefficient-ring map induces a surjective map of elementary
groups. -/
theorem elementaryGroupMap_surjective_of_surjective (f : R →+* S)
    (hf : Function.Surjective f) :
    Function.Surjective (elementaryGroupMap (ι := ι) f) := by
  intro g
  have hg : (g : (Matrix ι ι S)ˣ) ∈
      (elementaryGroup ι R).map (elementaryMatrixUnitMap f) := by
    rw [elementaryGroup_map_eq_of_surjective f hf]
    exact g.property
  obtain ⟨x, hx, hmap⟩ := hg
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hmap

/-- Coefficient transport: an isomorphism of rings induces one of elementary
groups. -/
def elementaryCoefficientEquiv (f : R ≃+* S) :
    elementaryGroup ι R ≃* elementaryGroup ι S :=
  ((Units.mapEquiv f.mapMatrix.toMulEquiv).subgroupMap
    (elementaryGroup ι R)).trans
    (MulEquiv.subgroupCongr
      (by
        have hmap : (Units.mapEquiv (f.mapMatrix (m := ι)).toMulEquiv).toMonoidHom =
            elementaryMatrixUnitMap f.toRingHom := by
          ext u
          rfl
        change (elementaryGroup ι R).map
            (Units.mapEquiv (f.mapMatrix (m := ι)).toMulEquiv).toMonoidHom =
          elementaryGroup ι S
        rw [hmap]
        exact elementaryGroup_map_eq_of_surjective f.toRingHom f.surjective))

/-- Index transport. -/
def elementaryReindexUnitEquiv (e : ι ≃ κ) :
    (Matrix ι ι R)ˣ ≃* (Matrix κ κ R)ˣ :=
  Units.mapEquiv (Matrix.reindexRingEquiv R e).toMulEquiv

theorem elementaryReindexUnitEquiv_elementaryUnit (e : ι ≃ κ) (i j : ι)
    (hij : i ≠ j) (a : R) :
    elementaryReindexUnitEquiv (R := R) e (elementaryUnit i j hij a) =
      elementaryUnit (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  change (Matrix.reindexRingEquiv R e) (1 + Matrix.single i j a) =
    1 + Matrix.single (e i) (e j) a
  rw [map_add, map_one]
  congr 1
  change Matrix.reindex e e (Matrix.single i j a) = Matrix.single (e i) (e j) a
  simpa only [Matrix.reindex_apply, Equiv.symm_symm] using
    Matrix.submatrix_single_equiv e.symm e.symm i j a

theorem elementaryReindexGroup_map (e : ι ≃ κ) :
    (elementaryGroup ι R).map (elementaryReindexUnitEquiv e).toMonoidHom =
      elementaryGroup κ R := by
  apply le_antisymm
  · rw [elementaryGroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    change elementaryReindexUnitEquiv e (elementaryUnit i j hij a) ∈
      elementaryGroup κ R
    rw [elementaryReindexUnitEquiv_elementaryUnit]
    exact elementaryUnit_mem _ _ _ a
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨k, l, hkl, a, rfl⟩
    have hij : e.symm k ≠ e.symm l := e.symm.injective.ne hkl
    refine ⟨elementaryUnit (e.symm k) (e.symm l) hij a,
      elementaryUnit_mem _ _ _ a, ?_⟩
    simpa using elementaryReindexUnitEquiv_elementaryUnit e (e.symm k) (e.symm l) hij a

def elementaryReindexEquiv (e : ι ≃ κ) :
    elementaryGroup ι R ≃* elementaryGroup κ R :=
  ((elementaryReindexUnitEquiv (R := R) e).subgroupMap (elementaryGroup ι R)).trans
    (MulEquiv.subgroupCongr (elementaryReindexGroup_map e))

/-- Block flattening `M_ι(M_κ(R)) ≅ M_{ι×κ}(R)`. -/
def elementaryBlockUnitEquiv :
    (Matrix ι ι (Matrix κ κ R))ˣ ≃* (Matrix (ι × κ) (ι × κ) R)ˣ :=
  Units.mapEquiv (Matrix.compRingEquiv ι κ R).toMulEquiv

theorem elementaryBlockUnitEquiv_single (i j : ι) (hij : i ≠ j) (k l : κ)
    (a : R) :
    elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
        (elementaryUnit i j hij (Matrix.single k l a)) =
      elementaryUnit (i, k) (j, l) (fun h ↦ hij (congrArg Prod.fst h)) a := by
  apply Units.ext
  change (Matrix.compRingEquiv ι κ R)
      (1 + Matrix.single i j (Matrix.single k l a)) =
    1 + Matrix.single (i, k) (j, l) a
  rw [map_add, map_one]
  congr 1
  exact Matrix.comp_single_single i j k l a

theorem elementaryBlockUnitEquiv_mem (i j : ι) (hij : i ≠ j)
    (M : Matrix κ κ R) :
    elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)
        (elementaryUnit i j hij M) ∈ elementaryGroup (ι × κ) R := by
  induction M using Matrix.induction_on' with
  | h_zero => simp [elementaryUnit_zero]
  | h_add M N hM hN =>
      rw [← elementaryUnit_mul, map_mul]
      exact (elementaryGroup (ι × κ) R).mul_mem hM hN
  | h_std_basis k l a =>
      rw [elementaryBlockUnitEquiv_single i j hij k l a]
      exact elementaryUnit_mem _ _ _ a

theorem elementaryBlockGroup_map [Nontrivial ι] :
    (elementaryGroup ι (Matrix κ κ R)).map
        (elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)).toMonoidHom =
      elementaryGroup (ι × κ) R := by
  set B : Subgroup (Matrix (ι × κ) (ι × κ) R)ˣ :=
    (elementaryGroup ι (Matrix κ κ R)).map
      (elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)).toMonoidHom
  have hcross : ∀ (i j : ι) (hij : i ≠ j) (k l : κ) (a : R),
      elementaryUnit (i, k) (j, l) (fun h ↦ hij (congrArg Prod.fst h)) a ∈ B := by
    intro i j hij k l a
    exact ⟨elementaryUnit i j hij (Matrix.single k l a),
      elementaryUnit_mem i j hij _, elementaryBlockUnitEquiv_single i j hij k l a⟩
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, M, rfl⟩
    exact elementaryBlockUnitEquiv_mem i j hij M
  · change elementaryGroup (ι × κ) R ≤ B
    rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, k⟩, ⟨j, l⟩, hne, a, rfl⟩
    by_cases hij : i = j
    · subst j
      obtain ⟨j, hji⟩ := exists_ne i
      exact elementaryUnit_mem_of_two_step B (i, k) (j, k) (i, l)
        (fun h ↦ hji (congrArg Prod.fst h).symm)
        (fun h ↦ hji (congrArg Prod.fst h))
        hne a (hcross i j hji.symm k k a) (hcross j i hji k l 1)
    · exact hcross i j hij k l a

/-- **Matrix self-similarity for elementary groups**: `EL_ι(M_κ(R)) ≅
EL_{ι×κ}(R)`. -/
def elementaryBlockEquiv [Nontrivial ι] :
    elementaryGroup ι (Matrix κ κ R) ≃* elementaryGroup (ι × κ) R :=
  ((elementaryBlockUnitEquiv (ι := ι) (κ := κ) (R := R)).subgroupMap
    (elementaryGroup ι (Matrix κ κ R))).trans
    (MulEquiv.subgroupCongr (elementaryBlockGroup_map (ι := ι) (κ := κ) (R := R)))

end Transport

end NonsoficGroupsExist
