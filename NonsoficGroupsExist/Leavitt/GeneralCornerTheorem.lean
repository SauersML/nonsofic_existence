import NonsoficGroupsExist.Leavitt.GeneralScheme
import NonsoficGroupsExist.Leavitt.DiagonalCornerCompression
import NonsoficGroupsExist.Kazhdan.KazhdanFiniteGeneration
import NonsoficGroupsExist.Criterion.CriterionAssembly

/-!
# The Leavitt-corner theorem at every adjacent pair of ranks

The manuscript's corner theorem: a nontrivial countable unital ring carrying
a binary Leavitt family, `m ≥ 2`, `n = m + 1`, property `(T)` for `EL_m(A)`
and `EL_n(A)`, and the membership hypothesis `u, z ∈ EL_n(A)` for the two
displayed matrices — then `EL_n(A)` is not sofic.  This module assembles the
theorem from `GeneralScheme` at exactly those hypotheses:

* the embedded core `EL_m(A) ↪ EL_{m+1}(A)` and the closure extensions of
  the conjugation and centralizer identities;
* generation: the embedded core together with `{u, zu}` generates
  `EL_{m+1}(A)`, given the membership hypothesis;
* the diagonal witness at every `m ≥ 2`, by the Whitehead construction in
  the coordinate plane `(0, 1)` — no rank-specific case analysis;
* the centralizer and disjointness of the compressed core against the
  witness, entrywise at every rank;
* the compression setup, with the finite generating data of the core drawn
  from property `(T)` itself;
* the theorem, and its characteristic-two discharge: over a ring of
  characteristic two the memberships of hypothesis (ii) hold
  unconditionally, because `u` and `z` are the explicit elementary words of
  `GeneralRankWords`.
-/

namespace NonsoficGroupsExist
namespace GeneralCornerTheorem

open GeneralRank GeneralScheme

open scoped commutatorElement

variable {R : Type} [Ring R] (L : LeavittFamily R) {m : ℕ}

/-! ### The embedded core -/

/-- The reindexing `Fin m ⊕ Unit ≃ Fin (m + 1)` of the stabilization. -/
def stabIndexEquiv (m : ℕ) : Fin m ⊕ Unit ≃ Fin (m + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) finOneEquiv.symm).trans finSumFinEquiv

@[simp] theorem stabIndexEquiv_inl (i : Fin m) :
    stabIndexEquiv m (Sum.inl i) = i.castSucc := rfl

/-- The upper-left embedding `EL_m(R) →* EL_{m+1}(R)`. -/
noncomputable def coreEmbedding :
    elementaryGroup (Fin m) R →* elementaryGroup (Fin (m + 1)) R :=
  (elementaryReindexEquiv (R := R) (stabIndexEquiv m)).toMonoidHom.comp
    (elementaryStabilization (ι := Fin m) (κ := Unit) (R := R))

theorem coreEmbedding_injective :
    Function.Injective (coreEmbedding (R := R) (m := m)) :=
  (elementaryReindexEquiv (R := R) (stabIndexEquiv m)).injective.comp
    elementaryStabilization_injective

@[simp] theorem coreEmbedding_elementaryRoot (i j : Fin m) (hij : i ≠ j)
    (a : R) :
    coreEmbedding (elementaryRoot i j hij a) =
      elementaryRoot i.castSucc j.castSucc
        (fun h => hij (Fin.castSucc_inj.mp h)) a := by
  apply Subtype.ext
  change elementaryReindexUnitEquiv (R := R) (stabIndexEquiv m)
      (stabilizeUnit (κ := Unit) (elementaryUnit i j hij a)) =
    elementaryUnit i.castSucc j.castSucc
      (fun h => hij (Fin.castSucc_inj.mp h)) a
  rw [stabilizeUnit_elementaryUnit, elementaryReindexUnitEquiv_elementaryUnit]
  rfl

/-- The compression endomorphism acts on roots by coefficient compression. -/
theorem compressionEnd_elementaryRoot (i j : Fin m) (hij : i ≠ j) (a : R) :
    L.elementaryCompressionEnd (elementaryRoot i j hij a) =
      elementaryRoot i j hij (L.s0 * a * L.t0) := by
  apply Subtype.ext
  exact L.matrixCompression_elementaryUnit i j hij a

/-! ### Conjugation and centralization over the whole embedded core -/

/-- Conjugation by `u` implements the compression endomorphism on the whole
embedded core, in mul-past form at the level of ambient units. -/
theorem uUnit_mul_coreEmbedding (g : elementaryGroup (Fin m) R) :
    uUnit L * (coreEmbedding g : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) =
      (coreEmbedding (L.elementaryCompressionEnd g) :
          (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) * uUnit L := by
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [show (⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩ :
          elementaryGroup (Fin m) R) = elementaryRoot i j hij a from
        Subtype.ext rfl]
      rw [compressionEnd_elementaryRoot, coreEmbedding_elementaryRoot,
        coreEmbedding_elementaryRoot]
      exact uUnit_mul_elementaryUnit L i j
        (fun h => hij (Fin.castSucc_inj.mp h)) a
  | one =>
      rw [show (⟨1, _⟩ : elementaryGroup (Fin m) R) = 1 from Subtype.ext rfl,
        map_one, map_one]
      simp
  | mul x y hxmem hymem hx hy =>
      rw [show (⟨x * y, _⟩ : elementaryGroup (Fin m) R) =
          ⟨x, hxmem⟩ * ⟨y, hymem⟩ from Subtype.ext rfl, map_mul, map_mul,
        map_mul]
      push_cast
      rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
  | inv x hxmem hx =>
      rw [show (⟨x⁻¹, _⟩ : elementaryGroup (Fin m) R) =
          (⟨x, hxmem⟩ : elementaryGroup (Fin m) R)⁻¹ from Subtype.ext rfl,
        map_inv, map_inv, map_inv]
      push_cast
      exact SemiconjBy.inv_right hx

/-- The involution centralizes the whole compressed embedded core. -/
theorem zUnit_commute_compressed_core (hm : 0 < m)
    (g : elementaryGroup (Fin m) R) :
    Commute (zUnit L hm)
      (coreEmbedding (L.elementaryCompressionEnd g) :
        (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) := by
  rcases g with ⟨g, hg⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [show (⟨elementaryUnit i j hij a, elementaryUnit_mem i j hij a⟩ :
          elementaryGroup (Fin m) R) = elementaryRoot i j hij a from
        Subtype.ext rfl]
      rw [compressionEnd_elementaryRoot, coreEmbedding_elementaryRoot]
      exact zUnit_commute_compressed L hm i j
        (fun h => hij (Fin.castSucc_inj.mp h)) a
  | one =>
      rw [show (⟨1, _⟩ : elementaryGroup (Fin m) R) = 1 from Subtype.ext rfl,
        map_one, map_one]
      exact Commute.one_right _
  | mul x y hxmem hymem hx hy =>
      rw [show (⟨x * y, _⟩ : elementaryGroup (Fin m) R) =
          ⟨x, hxmem⟩ * ⟨y, hymem⟩ from Subtype.ext rfl, map_mul, map_mul]
      exact hx.mul_right hy
  | inv x hxmem hx =>
      rw [show (⟨x⁻¹, _⟩ : elementaryGroup (Fin m) R) =
          (⟨x, hxmem⟩ : elementaryGroup (Fin m) R)⁻¹ from Subtype.ext rfl,
        map_inv, map_inv]
      exact hx.inv_right

/-! ### Generation -/

section Generation

variable (hm : 0 < m)

/-- The two compressor words, as a finite subset of the ambient elementary
group; membership is the theorem's hypothesis (ii). -/
noncomputable def compressorSet
    (hu : uUnit L (m := m) ∈ elementaryGroup (Fin (m + 1)) R)
    (hz : zUnit L hm ∈ elementaryGroup (Fin (m + 1)) R) :
    Finset (elementaryGroup (Fin (m + 1)) R) := by
  classical
  exact {⟨uUnit L, hu⟩,
    ⟨zUnit L hm * uUnit L, Subgroup.mul_mem _ hz hu⟩}

/-- Roots with equal values are equal; used to transport along equalities of
`Fin` indices without dependent rewriting. -/
theorem elementaryRoot_eq_of_indices {n : ℕ} {i j i' j' : Fin n}
    (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i') (hj : j = j') (a : R) :
    elementaryRoot i j hij a = elementaryRoot i' j' hij' a := by
  subst hi
  subst hj
  rfl

/-- **Generation.**  Given hypothesis (ii), the embedded core together with
`{u, zu}` generates the ambient elementary group. -/
theorem coreEmbedding_compressorSet_generate (hm2 : 2 ≤ m)
    (hu : uUnit L (m := m) ∈ elementaryGroup (Fin (m + 1)) R)
    (hz : zUnit L hm ∈ elementaryGroup (Fin (m + 1)) R) :
    Subgroup.closure
      (Set.range (coreEmbedding (R := R) (m := m)) ∪
        (compressorSet L hm hu hz :
          Set (elementaryGroup (Fin (m + 1)) R))) = ⊤ := by
  classical
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin m := ⟨1, by omega⟩ with hi₁
  have h₀cast : (i₀.castSucc : Fin (m + 1)) = 0 := by
    apply Fin.ext
    simp [hi₀]
  have h₁ne0 : (i₁.castSucc : Fin (m + 1)) ≠ 0 := by
    intro hcon
    have := congrArg Fin.val hcon
    simp [hi₁] at this
  set H : Subgroup (elementaryGroup (Fin (m + 1)) R) := Subgroup.closure
    (Set.range (coreEmbedding (R := R) (m := m)) ∪
      (compressorSet L hm hu hz : Set (elementaryGroup (Fin (m + 1)) R)))
  have hcore : ∀ g, coreEmbedding (R := R) g ∈ H := fun g =>
    Subgroup.subset_closure (Or.inl ⟨g, rfl⟩)
  have huH : (⟨uUnit L, hu⟩ : elementaryGroup (Fin (m + 1)) R) ∈ H := by
    apply Subgroup.subset_closure
    right
    simp [compressorSet]
  have hvH : (⟨zUnit L hm * uUnit L, Subgroup.mul_mem _ hz hu⟩ :
      elementaryGroup (Fin (m + 1)) R) ∈ H := by
    apply Subgroup.subset_closure
    right
    simp [compressorSet]
  have hzH : (⟨zUnit L hm, hz⟩ : elementaryGroup (Fin (m + 1)) R) ∈ H := by
    have heq : (⟨zUnit L hm, hz⟩ : elementaryGroup (Fin (m + 1)) R) =
        ⟨zUnit L hm * uUnit L, Subgroup.mul_mem _ hz hu⟩ *
          (⟨uUnit L, hu⟩ : elementaryGroup (Fin (m + 1)) R)⁻¹ := by
      apply Subtype.ext
      show zUnit L hm = zUnit L hm * uUnit L * (uUnit L)⁻¹
      group
    rw [heq]
    exact H.mul_mem hvH (H.inv_mem huH)
  -- a core root at the zero coordinate, embedded
  have hcoreRoot : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (a : R)
      (k l : Fin m) (hkl : k ≠ l), i = k.castSucc → j = l.castSucc →
      elementaryRoot i j hij a ∈ H := by
    intro i j hij a k l hkl hik hjl
    rw [elementaryRoot_eq_of_indices hij
      (fun h => hkl (Fin.castSucc_inj.mp h)) hik hjl a,
      ← coreEmbedding_elementaryRoot]
    exact hcore _
  -- the conjugated last-row and last-column roots
  have hconj : ∀ {x y : elementaryGroup (Fin (m + 1)) R}, x ∈ H →
      (⟨zUnit L hm, hz⟩ : elementaryGroup (Fin (m + 1)) R) * x *
        ⟨zUnit L hm, hz⟩ = y → y ∈ H := by
    intro x y hx heq
    rw [← heq]
    exact H.mul_mem (H.mul_mem hzH hx) hzH
  have hlastRow : ∀ (j : Fin m), (j.castSucc : Fin (m + 1)) ≠ 0 → ∀ a : R,
      elementaryRoot (last m) j.castSucc
        (Ne.symm (castSucc_ne_last j)) a ∈ H := by
    intro j hj0 a
    refine hconj (x := elementaryRoot 0 j.castSucc (Ne.symm hj0)
      (L.s1 * a)) ?_ ?_
    · exact hcoreRoot _ _ _ _ i₀ j
        (fun h => hj0 (by rw [← h₀cast, h])) h₀cast.symm rfl
    · apply Subtype.ext
      show zUnit L hm * elementaryUnit 0 j.castSucc (Ne.symm hj0)
          (L.s1 * a) * zUnit L hm =
        elementaryUnit (last m) j.castSucc
          (Ne.symm (castSucc_ne_last j)) a
      exact zUnit_conj_lastRow L hm j hj0 (Ne.symm hj0)
        (Ne.symm (castSucc_ne_last j)) a
  have hlastColumn : ∀ (i : Fin m), (i.castSucc : Fin (m + 1)) ≠ 0 →
      ∀ a : R,
      elementaryRoot i.castSucc (last m) (castSucc_ne_last i) a ∈ H := by
    intro i hi0 a
    refine hconj (x := elementaryRoot i.castSucc 0 hi0 (a * L.t1)) ?_ ?_
    · exact hcoreRoot _ _ _ _ i i₀
        (fun h => hi0 (by rw [h, h₀cast])) rfl h₀cast.symm
    · apply Subtype.ext
      show zUnit L hm * elementaryUnit i.castSucc 0 hi0 (a * L.t1) *
          zUnit L hm =
        elementaryUnit i.castSucc (last m) (castSucc_ne_last i) a
      exact zUnit_conj_lastColumn L hm i hi0 (castSucc_ne_last i) a
  have hcommutator : ∀ {x y z : elementaryGroup (Fin (m + 1)) R},
      x ∈ H → y ∈ H → ⁅x, y⁆ = z → z ∈ H := by
    intro x y z hx hy heq
    rw [← heq, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx))
      (H.inv_mem hy)
  have hlastZero : ∀ a : R,
      elementaryRoot (last m) (0 : Fin (m + 1))
        (Ne.symm (zero_ne_last hm)) a ∈ H := by
    intro a
    refine hcommutator
      (x := elementaryRoot (last m) i₁.castSucc
        (Ne.symm (castSucc_ne_last i₁)) a)
      (y := elementaryRoot i₁.castSucc (0 : Fin (m + 1)) h₁ne0 1)
      (hlastRow i₁ h₁ne0 a)
      (hcoreRoot _ _ _ _ i₁ i₀
        (fun h => h₁ne0 (by rw [h, h₀cast])) rfl h₀cast.symm) ?_
    apply Subtype.ext
    have := elementaryUnit_commutator (last m) i₁.castSucc (0 : Fin (m + 1))
      (Ne.symm (castSucc_ne_last i₁)) h₁ne0
      (Ne.symm (zero_ne_last hm)) a 1
    simpa [commutatorElement_def] using this
  have hzeroLast : ∀ a : R,
      elementaryRoot (0 : Fin (m + 1)) (last m) (zero_ne_last hm) a ∈ H := by
    intro a
    refine hcommutator
      (x := elementaryRoot (0 : Fin (m + 1)) i₁.castSucc (Ne.symm h₁ne0) a)
      (y := elementaryRoot i₁.castSucc (last m) (castSucc_ne_last i₁) 1)
      (hcoreRoot _ _ _ _ i₀ i₁
        (fun h => h₁ne0 (by rw [← h, h₀cast])) h₀cast.symm rfl)
      (hlastColumn i₁ h₁ne0 1) ?_
    apply Subtype.ext
    have := elementaryUnit_commutator (0 : Fin (m + 1)) i₁.castSucc (last m)
      (Ne.symm h₁ne0) (castSucc_ne_last i₁) (zero_ne_last hm) a 1
    simpa [commutatorElement_def] using this
  have hall : ∀ (i j : Fin (m + 1)) (hij : i ≠ j) (a : R),
      elementaryRoot i j hij a ∈ H := by
    intro i j hij a
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl
      · exact hcoreRoot _ _ hij a k l
          (fun h => hij (h ▸ rfl)) rfl rfl
      · by_cases hk0 : (k.castSucc : Fin (m + 1)) = 0
        · rw [elementaryRoot_eq_of_indices hij (zero_ne_last hm) hk0 rfl a]
          exact hzeroLast a
        · exact hlastColumn k hk0 a
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨l, rfl⟩ | rfl
      · by_cases hl0 : (l.castSucc : Fin (m + 1)) = 0
        · rw [elementaryRoot_eq_of_indices hij
            (Ne.symm (zero_ne_last hm)) rfl hl0 a]
          exact hlastZero a
        · exact hlastRow l hl0 a
      · exact absurd rfl hij
  apply top_unique
  rintro ⟨g, hg⟩ -
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      exact hall i j hij a
  | one => exact H.one_mem
  | mul x y _ _ hx hy => exact H.mul_mem hx hy
  | inv x _ hx => exact H.inv_mem hx

end Generation

/-! ### The diagonal witness, at every `m ≥ 2` -/

section Witness

variable (hm2 : 2 ≤ m)

def idx0 : Fin m := ⟨0, lt_of_lt_of_le two_pos hm2⟩

def idx1 : Fin m := ⟨1, lt_of_lt_of_le one_lt_two hm2⟩

theorem idx0_ne_idx1 : idx0 hm2 ≠ idx1 hm2 := by
  intro h
  have := congrArg Fin.val h
  simp [idx0, idx1] at this

/-- The unit with `u` in the distinguished diagonal slot. -/
def diagUnit (u : Rˣ) : (Matrix (Fin m) (Fin m) R)ˣ where
  val := Matrix.diagonal fun k => if k = idx0 hm2 then (↑u : R) else 1
  inv := Matrix.diagonal fun k => if k = idx0 hm2 then (↑u⁻¹ : R) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun k => (if k = idx0 hm2 then (↑u : R) else 1) *
        if k = idx0 hm2 then (↑u⁻¹ : R) else 1) =
        fun _ => (1 : R) from funext fun k => by
      by_cases hk : k = idx0 hm2 <;> simp [hk]]
    exact Matrix.diagonal_one
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun k => (if k = idx0 hm2 then (↑u⁻¹ : R) else 1) *
        if k = idx0 hm2 then (↑u : R) else 1) =
        fun _ => (1 : R) from funext fun k => by
      by_cases hk : k = idx0 hm2 <;> simp [hk]]
    exact Matrix.diagonal_one

@[simp] theorem diagUnit_val (u : Rˣ) :
    ((diagUnit hm2 u : (Matrix (Fin m) (Fin m) R)ˣ) :
        Matrix (Fin m) (Fin m) R) =
      Matrix.diagonal fun k => if k = idx0 hm2 then (↑u : R) else 1 := rfl

/-- The diagonal witness as a homomorphism of unit groups. -/
def diagUnitHom : Rˣ →* (Matrix (Fin m) (Fin m) R)ˣ where
  toFun := diagUnit hm2
  map_one' := by
    apply Units.ext
    show Matrix.diagonal _ = 1
    rw [show (fun k => if k = idx0 hm2 then ((1 : Rˣ) : R) else 1) =
        fun _ => (1 : R) from funext fun k => by
      by_cases hk : k = idx0 hm2 <;> simp [hk]]
    exact Matrix.diagonal_one
  map_mul' x y := by
    apply Units.ext
    show Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases hk : k = idx0 hm2 <;> simp [hk]

theorem diagUnitHom_injective :
    Function.Injective (diagUnitHom (R := R) hm2) := by
  intro x y hxy
  apply Units.ext
  have h := congrArg
    (fun M : (Matrix (Fin m) (Fin m) R)ˣ =>
      (↑M : Matrix (Fin m) (Fin m) R) (idx0 hm2) (idx0 hm2)) hxy
  simpa [diagUnitHom, diagUnit, Matrix.diagonal_apply] using h

/-! The Whitehead word placing a commutator of units on the diagonal. -/

/-- `w(u) = x₀₁(u) x₁₀(−u⁻¹) x₀₁(u)`, in the plane `(0, 1)`. -/
def whiteheadWord (u : Rˣ) : (Matrix (Fin m) (Fin m) R)ˣ :=
  elementaryUnit (idx0 hm2) (idx1 hm2) (idx0_ne_idx1 hm2) (↑u : R) *
    (elementaryUnit (idx1 hm2) (idx0 hm2) (Ne.symm (idx0_ne_idx1 hm2))
        (-(↑u⁻¹ : R)) *
      elementaryUnit (idx0 hm2) (idx1 hm2) (idx0_ne_idx1 hm2) (↑u : R))

theorem whiteheadWord_mem (u : Rˣ) :
    whiteheadWord hm2 u ∈ elementaryGroup (Fin m) R :=
  Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
    (Subgroup.mul_mem _ (elementaryUnit_mem _ _ _ _)
      (elementaryUnit_mem _ _ _ _))

theorem whiteheadWord_val (u : Rˣ) :
    ((whiteheadWord hm2 u : (Matrix (Fin m) (Fin m) R)ˣ) :
        Matrix (Fin m) (Fin m) R) =
      planeMatrix (idx0 hm2) (idx1 hm2)
        !![0, (↑u : R); -(↑u⁻¹ : R), 0] := by
  have hne := idx0_ne_idx1 hm2
  rw [whiteheadWord, Units.val_mul, Units.val_mul]
  rw [elementaryUnit_val_planeMatrix _ _ hne (↑u : R)]
  rw [elementaryUnit_val_planeMatrix' _ _ hne (-(↑u⁻¹ : R))]
  rw [planeMatrix_mul _ _ hne, planeMatrix_mul _ _ hne]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The balanced word `w(u)w(−1)`, with value `diag(u, u⁻¹)` in the
plane. -/
def balancedWord (u : Rˣ) : (Matrix (Fin m) (Fin m) R)ˣ :=
  whiteheadWord hm2 u * whiteheadWord hm2 (-1)

theorem balancedWord_mem (u : Rˣ) :
    balancedWord hm2 u ∈ elementaryGroup (Fin m) R :=
  Subgroup.mul_mem _ (whiteheadWord_mem hm2 u) (whiteheadWord_mem hm2 (-1))

theorem balancedWord_val (u : Rˣ) :
    ((balancedWord hm2 u : (Matrix (Fin m) (Fin m) R)ˣ) :
        Matrix (Fin m) (Fin m) R) =
      planeMatrix (idx0 hm2) (idx1 hm2)
        !![(↑u : R), 0; 0, (↑u⁻¹ : R)] := by
  have hne := idx0_ne_idx1 hm2
  rw [balancedWord, Units.val_mul, whiteheadWord_val, whiteheadWord_val,
    planeMatrix_mul _ _ hne]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The three balanced words place a commutator of units in the
distinguished slot: `h(a)h(b)h((ba)⁻¹) = diag(⁅a,b⁆, 1)`. -/
theorem diagUnit_commutator_eq (a b : Rˣ) :
    diagUnit hm2 ⁅a, b⁆ =
      balancedWord hm2 a * balancedWord hm2 b *
        balancedWord hm2 ((b * a)⁻¹) := by
  have hne := idx0_ne_idx1 hm2
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, balancedWord_val, balancedWord_val,
    balancedWord_val, planeMatrix_mul _ _ hne, planeMatrix_mul _ _ hne,
    inv_inv]
  have hblock :
      (!![(↑a : R), 0; 0, (↑a⁻¹ : R)] * !![(↑b : R), 0; 0, (↑b⁻¹ : R)] *
        !![(↑(b * a)⁻¹ : R), 0; 0, (↑(b * a) : R)]) =
      !![(↑(⁅a, b⁆ : Rˣ) : R), 0; 0, 1] := by
    have h1 : (↑a : R) * ↑b * ((↑a⁻¹ : R) * ↑b⁻¹) = ↑(⁅a, b⁆ : Rˣ) := by
      rw [commutatorElement_def]
      push_cast
      rw [← mul_assoc]
    have h2 : (↑a⁻¹ : R) * ↑b⁻¹ * ((↑b : R) * ↑a) = 1 := by
      rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul,
        ← Units.val_one]
      congr 1
      group
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2]
  rw [hblock, diagUnit_val]
  -- `planeMatrix` of a diagonal block with `1` in the second slot is the
  -- distinguished diagonal
  ext r c
  by_cases hr0 : r = idx0 hm2
  · rw [hr0]
    by_cases hc : c = idx0 hm2
    · rw [hc, Matrix.diagonal_apply_eq, planeMatrix_apply_ii]
      simp
    · rw [Matrix.diagonal_apply_ne _ (fun h => hc h.symm)]
      by_cases hc1 : c = idx1 hm2
      · rw [hc1, planeMatrix_apply_ij _ _ _ hne]
        simp
      · rw [planeMatrix_apply_row_i _ _ _ hc hc1]
  · by_cases hr1 : r = idx1 hm2
    · rw [hr1]
      by_cases hc : c = idx1 hm2
      · rw [hc, Matrix.diagonal_apply_eq, planeMatrix_apply_jj _ _ _ hne]
        simp [Ne.symm (idx0_ne_idx1 hm2)]
      · by_cases hc0 : c = idx0 hm2
        · rw [hc0, Matrix.diagonal_apply_ne _
              (Ne.symm (idx0_ne_idx1 hm2)), planeMatrix_apply_ji _ _ _ hne]
          simp
        · rw [Matrix.diagonal_apply_ne _ (fun h => hc h.symm),
            planeMatrix_apply_row_j _ _ _ hne hc0 hc]
    · rw [planeMatrix_apply_off _ _ _ hr0 hr1]
      by_cases hc : r = c
      · subst hc
        rw [Matrix.diagonal_apply_eq, if_pos rfl, if_neg hr0]
      · rw [Matrix.diagonal_apply_ne _ hc, if_neg hc]

/-- Diagonal units at commutators are elementary. -/
theorem diagUnit_commutator_mem (a b : Rˣ) :
    diagUnit hm2 ⁅a, b⁆ ∈ elementaryGroup (Fin m) R := by
  rw [diagUnit_commutator_eq]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (balancedWord_mem hm2 a) (balancedWord_mem hm2 b))
    (balancedWord_mem hm2 ((b * a)⁻¹))

/-- Diagonal units at elements of the commutator subgroup are elementary. -/
theorem diagUnit_mem_of_mem_commutator {u : Rˣ} (hu : u ∈ commutator Rˣ) :
    diagUnit hm2 u ∈ elementaryGroup (Fin m) R := by
  rw [commutator_eq_closure] at hu
  induction hu using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨a, b, rfl⟩ := hz
      exact diagUnit_commutator_mem hm2 a b
  | one =>
      rw [show diagUnit hm2 (1 : Rˣ) = 1 from (diagUnitHom hm2).map_one]
      exact (elementaryGroup (Fin m) R).one_mem
  | mul x y _ _ hx hy =>
      rw [show diagUnit hm2 (x * y) = diagUnit hm2 x * diagUnit hm2 y from
        (diagUnitHom hm2).map_mul x y]
      exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
      rw [show diagUnit hm2 x⁻¹ = (diagUnit hm2 x)⁻¹ from
        (diagUnitHom hm2).map_inv x]
      exact Subgroup.inv_mem _ hx

/-- The corner witness, embedded on the distinguished diagonal slot of
`EL_m(R)`. -/
noncomputable def witnessEmbedding :
    L.cornerWitnessSubgroup →* elementaryGroup (Fin m) R :=
  ((diagUnitHom hm2).comp L.cornerWitnessSubgroup.subtype).codRestrict
    (elementaryGroup (Fin m) R) (fun j =>
      diagUnit_mem_of_mem_commutator hm2
        (L.cornerWitnessSubgroup_le_commutator j.property))

theorem witnessEmbedding_injective :
    Function.Injective (witnessEmbedding L hm2) := by
  intro x y hxy
  apply Subtype.ext
  apply diagUnitHom_injective hm2
  exact congrArg
    (fun z : elementaryGroup (Fin m) R => (z : (Matrix (Fin m) (Fin m) R)ˣ))
    hxy

end Witness

/-! ### Centralization and disjointness of witness and compressed core -/

section WitnessBridge

variable (hm2 : 2 ≤ m)

/-- The compressed matrix commutes with the diagonal witness: the four ring
identities of the corner unit against `p₁` and `s₀ ⬝ t₀`. -/
theorem matrixCompression_commutes_diagUnit
    (M : Matrix (Fin m) (Fin m) R) (u : Rˣ) :
    L.matrixCompression M *
        ((diagUnit hm2 (L.cornerHom u) : (Matrix (Fin m) (Fin m) R)ˣ) :
          Matrix (Fin m) (Fin m) R) =
      ((diagUnit hm2 (L.cornerHom u) : (Matrix (Fin m) (Fin m) R)ˣ) :
          Matrix (Fin m) (Fin m) R) * L.matrixCompression M := by
  have hw_p1 : (↑(L.cornerHom u) : R) * L.p1 = L.p1 * ↑(L.cornerHom u) := by
    rw [show (↑(L.cornerHom u) : R) * L.p1 = L.s1 * ↑u * L.t1 from by
      rw [LeavittFamily.cornerHom, LeavittFamily.p1]
      show (L.p0 + L.s1 * ↑u * L.t1) * (L.s1 * L.t1) = L.s1 * ↑u * L.t1
      rw [add_mul, LeavittFamily.p0, mul_assoc L.s0, ← mul_assoc L.t0,
        L.t0_s1, zero_mul, mul_zero, zero_add, mul_assoc (L.s1 * ↑u),
        ← mul_assoc L.t1, L.t1_s1, one_mul]]
    rw [show L.p1 * (↑(L.cornerHom u) : R) = L.s1 * ↑u * L.t1 from by
      rw [LeavittFamily.cornerHom, LeavittFamily.p1]
      show (L.s1 * L.t1) * (L.p0 + L.s1 * ↑u * L.t1) = L.s1 * ↑u * L.t1
      rw [mul_add, LeavittFamily.p0, mul_assoc L.s1, ← mul_assoc L.t1,
        L.t1_s0, zero_mul, mul_zero, zero_add, ← mul_assoc,
        mul_assoc L.s1, ← mul_assoc L.t1, L.t1_s1, one_mul]]
  have hw_left : ∀ x : R,
      (↑(L.cornerHom u) : R) * (L.s0 * x * L.t0) = L.s0 * x * L.t0 := by
    intro x
    rw [← mul_assoc, ← mul_assoc, L.cornerHom_s0]
  have hw_right : ∀ x : R,
      L.s0 * x * L.t0 * ↑(L.cornerHom u) = L.s0 * x * L.t0 := by
    intro x
    rw [mul_assoc, L.t0_cornerHom]
  ext r c
  rw [show ((diagUnit hm2 (L.cornerHom u) :
      (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R) =
    Matrix.diagonal fun k => if k = idx0 hm2 then ↑(L.cornerHom u) else 1
    from rfl]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [LeavittFamily.matrixCompression_apply]
  by_cases hr : r = idx0 hm2
  · by_cases hc : c = idx0 hm2
    · have hrc : r = c := hr.trans hc.symm
      rw [if_pos hrc, if_pos hc, if_pos hr, add_mul, mul_add,
        hw_right (M r c), hw_left (M r c), hw_p1]
    · have hrc : r ≠ c := fun h => hc (h ▸ hr)
      rw [if_pos hr, if_neg hc, if_neg hrc, zero_add, mul_one, hw_left]
  · by_cases hc : c = idx0 hm2
    · have hrc : r ≠ c := fun h => hr (h.trans hc)
      rw [if_pos hc, if_neg hr, if_neg hrc, zero_add, one_mul, hw_right]
    · rw [if_neg hc, if_neg hr, mul_one, one_mul]

/-- The compression endomorphism commutes with the embedded witness. -/
theorem compressionEnd_commutes_witness (g : elementaryGroup (Fin m) R)
    (j : L.cornerWitnessSubgroup) :
    Commute (L.elementaryCompressionEnd g) (witnessEmbedding L hm2 j) := by
  obtain ⟨u, hu⟩ := L.cornerWitnessSubgroup_le_cornerSubgroup j.property
  have hj : (j : Rˣ) = L.cornerHom u := hu.symm
  apply (commute_iff_eq _ _).2
  apply Subtype.ext
  apply Units.ext
  change
    L.matrixCompression
          (↑(g : (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R) *
        ((diagUnit hm2 (j : Rˣ) : (Matrix (Fin m) (Fin m) R)ˣ) :
          Matrix (Fin m) (Fin m) R) =
      ((diagUnit hm2 (j : Rˣ) : (Matrix (Fin m) (Fin m) R)ˣ) :
          Matrix (Fin m) (Fin m) R) *
        L.matrixCompression
          (↑(g : (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R)
  rw [hj]
  exact matrixCompression_commutes_diagUnit L hm2 _ u

/-- Disjointness: the compressed core meets the witness only at the
identity. -/
theorem compressionEnd_eq_witness_iff (g : elementaryGroup (Fin m) R)
    (j : L.cornerWitnessSubgroup) :
    L.elementaryCompressionEnd g = witnessEmbedding L hm2 j ↔
      g = 1 ∧ j = 1 := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := L.cornerWitnessSubgroup_le_cornerSubgroup j.property
    have hj : (j : Rˣ) = L.cornerHom u := hu.symm
    have hmat : L.matrixCompression
        (↑(g : (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R) =
        ((diagUnit hm2 (L.cornerHom u) : (Matrix (Fin m) (Fin m) R)ˣ) :
          Matrix (Fin m) (Fin m) R) := by
      have hval := congrArg
        (fun z : elementaryGroup (Fin m) R =>
          ((z : (Matrix (Fin m) (Fin m) R)ˣ) :
            Matrix (Fin m) (Fin m) R)) h
      rw [← hj]
      exact hval
    have hentry := congrArg
      (fun M : Matrix (Fin m) (Fin m) R => M (idx0 hm2) (idx0 hm2)) hmat
    simp only [LeavittFamily.matrixCompression_apply] at hentry
    rw [if_true] at hentry
    rw [show ((diagUnit hm2 (L.cornerHom u) :
        (Matrix (Fin m) (Fin m) R)ˣ) : Matrix (Fin m) (Fin m) R)
          (idx0 hm2) (idx0 hm2) = ↑(L.cornerHom u) from by
      show Matrix.diagonal _ (idx0 hm2) (idx0 hm2) = _
      rw [Matrix.diagonal_apply_eq, if_pos rfl]] at hentry
    have hone : L.t1 *
        (L.p1 + L.s0 * (↑(g : (Matrix (Fin m) (Fin m) R)ˣ) :
          Matrix (Fin m) (Fin m) R) (idx0 hm2) (idx0 hm2) * L.t0) *
          L.s1 = 1 := by
      rw [mul_add, add_mul]
      rw [show L.t1 * L.p1 * L.s1 = 1 from by
        rw [LeavittFamily.p1, ← mul_assoc, L.t1_s1, one_mul, L.t1_s1]]
      rw [show L.t1 * (L.s0 * _ * L.t0) * L.s1 = 0 from by
        rw [← mul_assoc, ← mul_assoc, L.t1_s0, zero_mul, zero_mul,
          zero_mul]]
      rw [add_zero]
    rw [hentry] at hone
    rw [L.t1_cornerHom_s1] at hone
    have hu1 : u = 1 := Units.ext hone
    have hj1 : j = 1 := by
      apply Subtype.ext
      show (j : Rˣ) = 1
      rw [hj, hu1, map_one]
    refine ⟨?_, hj1⟩
    apply L.elementaryCompressionEnd_injective
    rw [h, hj1, map_one, map_one]
  · rintro ⟨rfl, rfl⟩
    rw [map_one, map_one]

end WitnessBridge

/-! ### Countability from finite generation -/

section Countability

open scoped Pointwise

/-- A group generated by a finite set is countable: every element is a word
in the generators and their inverses. -/
theorem countable_of_closure_finset_eq_top {G : Type*} [Group G]
    {S : Finset G} (hS : Subgroup.closure (S : Set G) = ⊤) : Countable G := by
  classical
  have hfin : ((S : Set G) ∪ (S : Set G)⁻¹).Finite :=
    S.finite_toSet.union S.finite_toSet.inv
  haveI : Countable ((S : Set G) ∪ (S : Set G)⁻¹ : Set G) :=
    hfin.countable.to_subtype
  apply Function.Surjective.countable
    (f := fun l : List ((S : Set G) ∪ (S : Set G)⁻¹ : Set G) =>
      (l.map Subtype.val).prod)
  intro g
  have hg : g ∈ Submonoid.closure ((S : Set G) ∪ (S : Set G)⁻¹) := by
    rw [← Subgroup.closure_toSubmonoid, Subgroup.mem_toSubmonoid, hS]
    exact Subgroup.mem_top g
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure hg
  refine ⟨l.attach.map fun x => ⟨x.1, hl x.1 x.2⟩, ?_⟩
  simp only [List.map_map]
  have hmap : l.attach.map (Subtype.val ∘ fun x : {a // a ∈ l} =>
      (⟨x.1, hl x.1 x.2⟩ :
        ((S : Set G) ∪ (S : Set G)⁻¹ : Set G))) = l := by
    simp
  rw [hmap, hprod]

/-- A property-`(T)` group is countable, through its finite generating
set. -/
theorem countable_of_hasKazhdanPropertyT {G : Type} [Group G]
    (hT : HasKazhdanPropertyT.{0, 0} G) : Countable G := by
  obtain ⟨Sf, -, -, hSf⟩ :=
    KazhdanFiniteGeneration.exists_symmetric_generating_finset G hT
  exact countable_of_closure_finset_eq_top hSf

end Countability

/-! ### The setup and the theorem -/

section Theorem

variable (hm : 0 < m) (hm2 : 2 ≤ m)

/-- The self-inverse involution unit squares to one. -/
theorem zUnit_mul_self : zUnit L hm * zUnit L hm = 1 :=
  Units.ext (zMatrix_mul_self L hm)

theorem zUnit_inv : (zUnit L hm)⁻¹ = zUnit L hm := Units.ext rfl

/-- Conjugation by the distinguished compressor, at the subgroup level. -/
theorem uSubtype_conj
    (hu : uUnit L (m := m) ∈ elementaryGroup (Fin (m + 1)) R)
    (g : elementaryGroup (Fin m) R) :
    coreEmbedding (L.elementaryCompressionEnd g) =
      (⟨uUnit L, hu⟩ : elementaryGroup (Fin (m + 1)) R) * coreEmbedding g *
        (⟨uUnit L, hu⟩ : elementaryGroup (Fin (m + 1)) R)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  show (coreEmbedding (L.elementaryCompressionEnd g) :
      (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) =
    uUnit L * (coreEmbedding g : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) *
      (uUnit L)⁻¹
  rw [uUnit_mul_coreEmbedding L g]
  group

/-- Conjugation by the second compressor, at the subgroup level. -/
theorem vSubtype_conj
    (hu : uUnit L (m := m) ∈ elementaryGroup (Fin (m + 1)) R)
    (hz : zUnit L hm ∈ elementaryGroup (Fin (m + 1)) R)
    (g : elementaryGroup (Fin m) R) :
    coreEmbedding (L.elementaryCompressionEnd g) =
      (⟨zUnit L hm * uUnit L, Subgroup.mul_mem _ hz hu⟩ :
          elementaryGroup (Fin (m + 1)) R) * coreEmbedding g *
        (⟨zUnit L hm * uUnit L, Subgroup.mul_mem _ hz hu⟩ :
          elementaryGroup (Fin (m + 1)) R)⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  show (coreEmbedding (L.elementaryCompressionEnd g) :
      (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) =
    zUnit L hm * uUnit L *
      (coreEmbedding g : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) *
        (zUnit L hm * uUnit L)⁻¹
  rw [mul_inv_rev, zUnit_inv]
  calc (coreEmbedding (L.elementaryCompressionEnd g) :
      (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ)
      = zUnit L hm * (zUnit L hm *
          (coreEmbedding (L.elementaryCompressionEnd g) :
            (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ)) := by
        rw [← mul_assoc, zUnit_mul_self, one_mul]
    _ = zUnit L hm *
          ((coreEmbedding (L.elementaryCompressionEnd g) :
            (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) * zUnit L hm) := by
        rw [(zUnit_commute_compressed_core L hm g).eq]
    _ = zUnit L hm * ((uUnit L *
          (coreEmbedding g : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) *
            (uUnit L)⁻¹) * zUnit L hm) := by
        rw [show (coreEmbedding (L.elementaryCompressionEnd g) :
            (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) =
          uUnit L * (coreEmbedding g :
            (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) * (uUnit L)⁻¹ from by
          rw [uUnit_mul_coreEmbedding L g]
          group]
    _ = zUnit L hm * uUnit L *
          (coreEmbedding g : (Matrix (Fin (m + 1)) (Fin (m + 1)) R)ˣ) *
            ((uUnit L)⁻¹ * zUnit L hm) := by
        group

/-- The compression setup of the corner theorem at every adjacent pair, with
the generating data of the core supplied by property `(T)`. -/
noncomputable def compressionSetup [Nontrivial R]
    (hu : uUnit L (m := m) ∈ elementaryGroup (Fin (m + 1)) R)
    (hz : zUnit L hm ∈ elementaryGroup (Fin (m + 1)) R)
    (hTΓ : HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin m) R)) :
    CompressionSetup (elementaryGroup (Fin (m + 1)) R)
      (elementaryGroup (Fin m) R) L.cornerWitnessSubgroup := by
  classical
  exact
    { embedΓ := coreEmbedding
      embedΓ_injective := coreEmbedding_injective
      embedJ := witnessEmbedding L hm2
      embedJ_injective := witnessEmbedding_injective L hm2
      generatorsΓ :=
        Classical.choose
          (KazhdanFiniteGeneration.exists_symmetric_generating_finset _ hTΓ)
      generatorsΓ_one :=
        (Classical.choose_spec
          (KazhdanFiniteGeneration.exists_symmetric_generating_finset
            _ hTΓ)).1
      generatorsΓ_symmetric :=
        (Classical.choose_spec
          (KazhdanFiniteGeneration.exists_symmetric_generating_finset
            _ hTΓ)).2.1
      generatorsΓ_generate :=
        (Classical.choose_spec
          (KazhdanFiniteGeneration.exists_symmetric_generating_finset
            _ hTΓ)).2.2
      generatorsJ := L.cornerWitnessGenerators
      generatorsJ_symmetric := L.cornerWitnessGenerators_symmetric
      generatorsJ_generate := L.cornerWitnessGenerators_generate
      infiniteΓ := by
        haveI := L.infinite
        exact elementaryGroup_infinite (R := R) (idx0 hm2) (idx1 hm2)
          (idx0_ne_idx1 hm2)
      compressors := compressorSet L hm hu hz
      distinguished := ⟨uUnit L, hu⟩
      distinguished_mem := by simp [compressorSet]
      compressedEnd := fun _ _ => L.elementaryCompressionEnd
      compressedEnd_spec := by
        intro q hq g
        simp only [compressorSet, Finset.mem_insert,
          Finset.mem_singleton] at hq
        rcases hq with rfl | rfl
        · exact uSubtype_conj L hu g
        · exact vSubtype_conj L hm hu hz g
      generates := coreEmbedding_compressorSet_generate L hm hm2 hu hz
      centralizes := by
        intro g j
        rw [← uSubtype_conj L hu g]
        exact (compressionEnd_commutes_witness L hm2 g j).map coreEmbedding
      disjoint := by
        intro g j h
        rw [← uSubtype_conj L hu g] at h
        exact (compressionEnd_eq_witness_iff L hm2 g j).mp
          (coreEmbedding_injective h) }

include hm2 in
/-- **The Leavitt-corner theorem, at every adjacent pair of ranks.**  Let
`R` be a nontrivial unital ring carrying a binary Leavitt family, `m ≥ 2`,
and suppose: (i) `EL_m(R)` and `EL_{m+1}(R)` have property `(T)`; (ii) the
compressor `u` and the involution `z` lie in `EL_{m+1}(R)`.  Then
`EL_{m+1}(R)` is not sofic.  No countability of `R` is assumed: the groups
of the criterion are countable because property `(T)` makes them finitely
generated. -/
theorem corner_not_isSofic [Nontrivial R]
    (hu : uUnit L (m := m) ∈ elementaryGroup (Fin (m + 1)) R)
    (hz : zUnit L hm ∈ elementaryGroup (Fin (m + 1)) R)
    (hTG : HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin (m + 1)) R))
    (hTΓ : HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin m) R)) :
    ¬ IsSofic (elementaryGroup (Fin (m + 1)) R) := by
  haveI : Countable (elementaryGroup (Fin (m + 1)) R) :=
    countable_of_hasKazhdanPropertyT hTG
  haveI : Countable (elementaryGroup (Fin m) R) :=
    countable_of_hasKazhdanPropertyT hTΓ
  haveI : Countable L.cornerWitnessSubgroup :=
    (witnessEmbedding_injective L hm2).countable
  exact not_isSofic_of_not_isLEF (compressionSetup L hm hm2 hu hz hTΓ) hTG
    hTΓ (FamilyRankFour.witness_not_isLEF L)

end Theorem

/-! ### The characteristic-two discharge of hypothesis (ii) -/

section CharTwoDischarge

variable [CharP R 2]

theorem uUnit_mem_of_charTwo :
    uUnit L (m := m) ∈ elementaryGroup (Fin (m + 1)) R := by
  have h : uUnit L (m := m) = GeneralRank.comb L := by
    apply Units.ext
    rw [comb_val]
    rfl
  rw [h]
  exact comb_mem L

theorem zUnit_mem_of_charTwo (hm : 0 < m) :
    zUnit L hm ∈ elementaryGroup (Fin (m + 1)) R := by
  have h : zUnit L hm = involutionWord L hm := by
    apply Units.ext
    rw [involutionWord_val]
    rfl
  rw [h]
  exact involutionWord_mem L hm

include L in
/-- In characteristic two, hypothesis (ii) is discharged by the explicit
elementary factorizations, and the corner theorem needs only the two
property-`(T)` inputs. -/
theorem corner_not_isSofic_of_charTwo [Nontrivial R]
    (hm : 0 < m) (hm2 : 2 ≤ m)
    (hTG : HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin (m + 1)) R))
    (hTΓ : HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin m) R)) :
    ¬ IsSofic (elementaryGroup (Fin (m + 1)) R) :=
  corner_not_isSofic L hm hm2 (uUnit_mem_of_charTwo L)
    (zUnit_mem_of_charTwo L hm) hTG hTΓ

end CharTwoDischarge

end GeneralCornerTheorem
end NonsoficGroupsExist
