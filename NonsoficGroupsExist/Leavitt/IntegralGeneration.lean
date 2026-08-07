import NonsoficGroupsExist.Leavitt.RawSwapCompressors
import NonsoficGroupsExist.Leavitt.FamilyRankFour

/-!
# Finite generation over finitely generated rings, and the raw-swap setup

Two unconditional layers of the integral story:

* `elementaryGroup_eq_closure_of_adjoin_int` and
  `elementaryGroup_finitelyGenerated_int`: `EL_n(B)` is finitely generated
  for every ring `B` of finite type over `ℤ` and every `n ≥ 3`, with the
  generating set exhibited — root matrices at the ring generators and at
  `1`.  Unlike the finite-field statement, no scalar transvections are
  needed beyond `x_{ij}(1)`: integer multiples are powers.
* `IntegralRankFour.compressionSetup`: the full algebraic compression setup
  over any nontrivial ring of finite type over `ℤ` carrying a binary Leavitt
  family, with the **raw two-word compressor set** `{u, w·u}` of
  `RawSwapCompressors` — no sign correction, no order-two relation, no `K₁`.

This module carries no conditional theorem.  What remains open over `ℤ` is
exactly Ershov–Jaikin-Zapirain's theorem (*Property (T) for noncommutative
universal lattices*, Invent. Math. 179 (2010)) at finitely generated rings:
a formalization of that input would combine with the unconditional corner
theorem `GeneralCornerTheorem.corner_not_isSofic` — which takes the two
`(T)` statements as its printed hypotheses — to close the integral case,
with no further work in this file.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

/-! ### Finite generation of elementary groups over finitely generated rings -/

section IntegralGeneration

variable {R : Type*} [Ring R]

/-- The coefficient set whose elementary root matrices lie in `H` is a
subring once the unit root matrices lie in `H`: sums by the root relation,
negatives by inverses, and products by the Steinberg commutator, which needs
a third coordinate and hence `n ≥ 3`. -/
def elementaryCoefficientSubring (n : ℕ) (hn : 2 < n)
    (H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ)
    (hunit : ∀ (i j : Fin n) (h : i ≠ j),
      elementaryUnit i j h (1 : R) ∈ H) :
    Subring R where
  carrier := {a | ∀ (i j : Fin n) (h : i ≠ j), elementaryUnit i j h a ∈ H}
  zero_mem' := by
    intro i j hij
    simp
  one_mem' := hunit
  add_mem' := by
    intro a b ha hb i j hij
    rw [← elementaryUnit_mul]
    exact H.mul_mem (ha i j hij) (hb i j hij)
  neg_mem' := by
    intro a ha i j hij
    have hmul : elementaryUnit i j hij (-a) * elementaryUnit i j hij a = 1 := by
      rw [elementaryUnit_mul, neg_add_cancel, elementaryUnit_zero]
    rw [eq_inv_of_mul_eq_one_left hmul]
    exact H.inv_mem (ha i j hij)
  mul_mem' := by
    intro a b ha hb i j hij
    obtain ⟨l, hli, hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j hn
    have hil : i ≠ l := hli.symm
    have hc : ⁅elementaryUnit i l hil a, elementaryUnit l j hlj b⁆ ∈ H := by
      rw [commutatorElement_def]
      exact H.mul_mem
        (H.mul_mem (H.mul_mem (ha i l hil) (hb l j hlj))
          (H.inv_mem (ha i l hil)))
        (H.inv_mem (hb l j hlj))
    rw [elementaryUnit_commutator i l j hil hlj hij a b] at hc
    exact hc

/-- **The explicit generating set, over any finitely generated ring.**  If
`s` generates `R` as a ring, then the root matrices at the elements of
`s ∪ {1}` generate `EL_n(R)` for every `n ≥ 3`: this is the printed form of
the finite-generation lemma, with the generating set exhibited rather than
existentially quantified.  Integer scalars need no root matrices of their
own, because `x_{ij}(m·1) = x_{ij}(1)^m`. -/
theorem elementaryGroup_eq_closure_of_adjoin_int [DecidableEq R] (n : ℕ)
    (hn : 2 < n)
    (s : Finset R) (hs : Algebra.adjoin ℤ (s : Set R) = ⊤) :
    Subgroup.closure
        ((finiteElementaryGenerators n s : Finset (Matrix (Fin n) (Fin n) R)ˣ) :
          Set (Matrix (Fin n) (Fin n) R)ˣ) =
      elementaryGroup (Fin n) R := by
  classical
  set t : Finset (Matrix (Fin n) (Fin n) R)ˣ := finiteElementaryGenerators n s
  set H : Subgroup (Matrix (Fin n) (Fin n) R)ˣ :=
    Subgroup.closure (t : Set (Matrix (Fin n) (Fin n) R)ˣ)
  have hunit : ∀ (i j : Fin n) (h : i ≠ j),
      elementaryUnit i j h (1 : R) ∈ H := by
    intro i j hij
    apply Subgroup.subset_closure
    exact (mem_finiteElementaryGenerators n s _).mpr
      ⟨i, j, hij, 1, Finset.mem_insert_self 1 s, rfl⟩
  set C : Subring R := elementaryCoefficientSubring n hn H hunit
  have hgen : (s : Set R) ⊆ (C : Set R) := by
    intro a ha i j hij
    apply Subgroup.subset_closure
    exact (mem_finiteElementaryGenerators n s _).mpr
      ⟨i, j, hij, a, Finset.mem_insert_of_mem ha, rfl⟩
  have hclosure : ∀ a : R, a ∈ Subring.closure (s : Set R) := by
    intro a
    have hmem : a ∈ Algebra.adjoin ℤ (s : Set R) := by
      rw [hs]
      trivial
    rwa [Algebra.adjoin_int] at hmem
  have hall : ∀ a : R, a ∈ C := fun a =>
    Subring.closure_le.mpr hgen (hclosure a)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro z hz
    obtain ⟨i, j, hij, a, -, rfl⟩ :=
      (mem_finiteElementaryGenerators n s z).mp hz
    exact elementaryUnit_mem i j hij a
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    exact hall a i j hij

/-- **Finite generation over `ℤ`.**  `EL_n(R)` is finitely generated whenever
`R` is finitely generated as a ring and `n ≥ 3`; immediate from the explicit
generating set. -/
theorem elementaryGroup_finitelyGenerated_int
    [Algebra.FiniteType ℤ R] (n : ℕ) (hn : 2 < n) :
    Group.FG (elementaryGroup (Fin n) R) := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  apply (Group.fg_iff_subgroup_fg (elementaryGroup (Fin n) R)).mpr
  exact ⟨finiteElementaryGenerators n s,
    elementaryGroup_eq_closure_of_adjoin_int n hn s hs⟩

end IntegralGeneration

/-! ### The compression setup over a finitely generated ring -/

namespace IntegralRankFour

noncomputable section

variable {A : Type} [Ring A] (L : LeavittFamily A)

/-- The full compression–centralizer setup over any nontrivial ring of finite
type over `ℤ` carrying a binary Leavitt family, built on the raw two-word
compressor set `{u, w·u}`: the comb compressor and the three-transvection
swap, with no sign correction.  Property `(T)` is not asserted here; it is
the criterion's remaining input. -/
def compressionSetup [Algebra.FiniteType ℤ A] [Nontrivial A] :
    CompressionSetup (RankFour.Ambient A) (RankFour.Core A)
      L.cornerWitnessSubgroup := by
  classical
  haveI : Group.FG (RankFour.Core A) :=
    elementaryGroup_finitelyGenerated_int 3 (by omega)
  exact
    { embedΓ := RankFour.coreEmbedding
      embedΓ_injective := RankFour.coreEmbedding_injective
      embedJ := FamilyRankFour.witnessEmbedding L
      embedJ_injective := FamilyRankFour.witnessEmbedding_injective L
      generatorsΓ :=
        Classical.choose
          (FamilyRankFour.exists_symmetric_generators (RankFour.Core A))
      generatorsΓ_one :=
        (Classical.choose_spec
          (FamilyRankFour.exists_symmetric_generators (RankFour.Core A))).1
      generatorsΓ_symmetric :=
        (Classical.choose_spec
          (FamilyRankFour.exists_symmetric_generators (RankFour.Core A))).2.1
      generatorsΓ_generate :=
        (Classical.choose_spec
          (FamilyRankFour.exists_symmetric_generators (RankFour.Core A))).2.2
      generatorsJ := L.cornerWitnessGenerators
      generatorsJ_symmetric := L.cornerWitnessGenerators_symmetric
      generatorsJ_generate := L.cornerWitnessGenerators_generate
      infiniteΓ := FamilyRankFour.coreInfinite L
      compressors := RankFour.rawCompressorSet L
      distinguished := RankFour.compressor L
      distinguished_mem := RankFour.compressor_mem_rawCompressorSet L
      compressedEnd := fun _ _ => RankFour.compressionEnd L
      compressedEnd_spec := fun q hq g =>
        RankFour.rawCompressorSet_conjugation L q hq g
      generates := RankFour.coreEmbedding_rawCompressorSet_generate L
      centralizes := by
        intro g j
        rw [← RankFour.rawCompressorSet_conjugation L (RankFour.compressor L)
          (RankFour.compressor_mem_rawCompressorSet L) g]
        exact (FamilyRankFour.compressionEnd_commutes_witnessEmbedding L g j).map
          RankFour.coreEmbedding
      disjoint := by
        intro g j h
        have h' : RankFour.coreEmbedding (RankFour.compressionEnd L g) =
            RankFour.coreEmbedding (FamilyRankFour.witnessEmbedding L j) :=
          (RankFour.rawCompressorSet_conjugation L (RankFour.compressor L)
            (RankFour.compressor_mem_rawCompressorSet L) g).trans h
        exact (FamilyRankFour.compressionEnd_eq_witnessEmbedding_iff L g j).mp
          (RankFour.coreEmbedding_injective h') }

end

end IntegralRankFour
end NonsoficGroupsExist
