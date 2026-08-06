import NonsoficGroupsExist.Leavitt.RawSwapCompressors
import NonsoficGroupsExist.Leavitt.FamilyRankFour
import NonsoficGroupsExist.Leavitt.LeavittOverCommRing
import NonsoficGroupsExist.Kazhdan.KazhdanFiniteGeneration

/-!
# The integral case, conditional on property `(T)` alone

Over finite fields the library derives both property-`(T)` inputs of the
compression–centralizer criterion and closes the rank-four theorem
unconditionally.  Over `ℤ` the literature input is Ershov–Jaikin-Zapirain's
theorem (*Property (T) for noncommutative universal lattices*, Invent. Math.
179 (2010)): `EL_n(B)` has property `(T)` for every finitely generated
associative unital ring `B` and every `n ≥ 3`.  That theorem is not yet
formalized here.

This module isolates it as the *only* missing input.  Everything else in the
rank-four argument is closed over an arbitrary finitely generated ring:

* `elementaryGroup_finitelyGenerated_int`: `EL_n(B)` is finitely generated
  for every ring `B` of finite type over `ℤ` and every `n ≥ 3`.  Unlike the
  finite-field statement, no scalar transvections are needed beyond
  `x_{ij}(1)`: integer multiples are powers.
* `IntegralRankFour.compressionSetup`: the full algebraic compression setup
  over any nontrivial ring of finite type over `ℤ` carrying a binary Leavitt
  family, with the **raw two-word compressor set** `{u, w·u}` of
  `RawSwapCompressors` — no sign correction, no order-two relation, no `K₁`.
* `IntegralRankFour.ambient_not_isSofic_of_propertyT`: given property `(T)`
  for `EL₃(B)` and `EL₄(B)` — the two instances of Ershov–Jaikin-Zapirain —
  the group `EL₄(B)` is not sofic.
* The specialization to `B = L_ℤ(1,2)`: a formalization of
  Ershov–Jaikin-Zapirain over `ℤ` would immediately make
  `EL₄(L_ℤ(1,2))` unconditionally nonsofic.

The two `(T)` hypotheses are stated for exactly the groups the criterion
consumes; nothing is hidden in them beyond the literature theorem named
above.
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
    simpa using H.one_mem
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

variable [Algebra.FiniteType ℤ A] [Countable A] [Nontrivial A]

include L in
/-- **The rank-four theorem over a finitely generated ring, conditional on
property `(T)` alone.**  Let `A` be a nontrivial countable ring of finite
type over `ℤ` carrying a binary Leavitt family, and suppose `EL₃(A)` and
`EL₄(A)` have Kazhdan's property `(T)` — the two relevant instances of
Ershov–Jaikin-Zapirain's theorem, which covers every finitely generated
ring and every rank at least three.  Then `EL₄(A)` is not sofic.

Every other ingredient — the comb compressor, the raw swap, generation,
the commuting corner witness, its finite non-LEF obstruction, finite
generation, and the criterion itself — is closed unconditionally in this
library. -/
theorem ambient_not_isSofic_of_propertyT
    (hTG : HasKazhdanPropertyT.{0, 0} (RankFour.Ambient A))
    (hTΓ : HasKazhdanPropertyT.{0, 0} (RankFour.Core A)) :
    ¬ IsSofic (RankFour.Ambient A) :=
  not_isSofic_of_not_isLEF (compressionSetup L) hTG hTΓ
    (FamilyRankFour.witness_not_isLEF L)

end

end IntegralRankFour

/-! ### The integral binary Leavitt algebra -/

namespace CommRingLeavitt

open IntegralRankFour

/-- `L_ℤ(1,2)` is of finite type over `ℤ` for the `ℤ`-algebra structure
`Ring.toIntAlgebra` puts on every ring.  That is the structure the statements
above use, since they quantify over an abstract `[Ring A]`, while
`LeavittOverCommRing` supplies finite type for the `RingQuot` algebra
structure.  The two agree: a ring carries at most one `ℤ`-algebra
structure. -/
noncomputable instance integralFiniteTypeInt :
    @Algebra.FiniteType ℤ IntegralLeavittAlgebra _ _
      (Ring.toIntAlgebra IntegralLeavittAlgebra) := by
  have h : (Ring.toIntAlgebra IntegralLeavittAlgebra) =
      (inferInstance : Algebra ℤ IntegralLeavittAlgebra) := Subsingleton.elim _ _
  rw [h]
  infer_instance

/-- **The integral case, conditional on Ershov–Jaikin-Zapirain.**  If
`EL₃(L_ℤ(1,2))` and `EL₄(L_ℤ(1,2))` have property `(T)` — which is the
literature's Ershov–Jaikin-Zapirain theorem at the finitely generated ring
`L_ℤ(1,2)`, not yet formalized here — then `EL₄(L_ℤ(1,2))` is not sofic.

The statement pins the integral problem to exactly its missing input: a
formalized `(T)` theorem over `ℤ` closes it with no further work. -/
noncomputable def integralLeavitt_compressionSetup :
    CompressionSetup (RankFour.Ambient IntegralLeavittAlgebra)
      (RankFour.Core IntegralLeavittAlgebra)
      (integralFamily).cornerWitnessSubgroup :=
  IntegralRankFour.compressionSetup integralFamily

theorem integralLeavitt_EL4_not_isSofic_of_propertyT
    (hTG : HasKazhdanPropertyT.{0, 0}
      (RankFour.Ambient IntegralLeavittAlgebra))
    (hTΓ : HasKazhdanPropertyT.{0, 0}
      (RankFour.Core IntegralLeavittAlgebra)) :
    ¬ IsSofic (RankFour.Ambient IntegralLeavittAlgebra) :=
  ambient_not_isSofic_of_propertyT integralFamily hTG hTΓ

end CommRingLeavitt

/-! ### The Leavitt-corner theorem at its printed hypotheses, ranks three
and four

The manuscript's corner theorem assumes a nontrivial unital ring carrying a
binary Leavitt family and property `(T)` at the two adjacent ranks, and
nothing else: finite generation is not a hypothesis, because Kazhdan groups
are finitely generated.  The statement below matches that hypothesis set at
the adjacent pair `(3, 4)`, with the compressor words `u` and `z·u` of
`RankFourCompressors` — the comb compressor and the sign-corrected
involution times it, both explicit products of elementary transvections.
The higher adjacent pairs of the printed theorem have no formalized
compressor words yet; they are the remaining generality gap, recorded in the
margin note of the manuscript. -/

namespace LeavittCornerTheorem

noncomputable section

variable {A : Type} [Ring A] (L : LeavittFamily A)

/-- The compression setup of the corner theorem, with the generating data of
the core produced by property `(T)` itself rather than assumed. -/
def compressionSetupOfKazhdan [Nontrivial A]
    (hTΓ : HasKazhdanPropertyT.{0, 0} (RankFour.Core A)) :
    CompressionSetup (RankFour.Ambient A) (RankFour.Core A)
      L.cornerWitnessSubgroup := by
  classical
  exact
    { embedΓ := RankFour.coreEmbedding
      embedΓ_injective := RankFour.coreEmbedding_injective
      embedJ := FamilyRankFour.witnessEmbedding L
      embedJ_injective := FamilyRankFour.witnessEmbedding_injective L
      generatorsΓ :=
        Classical.choose (KazhdanFiniteGeneration.exists_symmetric_generating_finset _ hTΓ)
      generatorsΓ_one :=
        (Classical.choose_spec (KazhdanFiniteGeneration.exists_symmetric_generating_finset _ hTΓ)).1
      generatorsΓ_symmetric :=
        (Classical.choose_spec (KazhdanFiniteGeneration.exists_symmetric_generating_finset _ hTΓ)).2.1
      generatorsΓ_generate :=
        (Classical.choose_spec (KazhdanFiniteGeneration.exists_symmetric_generating_finset _ hTΓ)).2.2
      generatorsJ := L.cornerWitnessGenerators
      generatorsJ_symmetric := L.cornerWitnessGenerators_symmetric
      generatorsJ_generate := L.cornerWitnessGenerators_generate
      infiniteΓ := FamilyRankFour.coreInfinite L
      compressors := RankFour.compressorSet L
      distinguished := RankFour.compressor L
      distinguished_mem := RankFour.compressor_mem L
      compressedEnd := fun _ _ => RankFour.compressionEnd L
      compressedEnd_spec := fun q hq g =>
        RankFour.compressorSet_conjugation L q hq g
      generates := RankFour.coreEmbedding_compressorSet_generate L
      centralizes := by
        intro g j
        rw [← RankFour.compressorSet_conjugation L (RankFour.compressor L)
          (RankFour.compressor_mem L) g]
        exact (FamilyRankFour.compressionEnd_commutes_witnessEmbedding L g j).map
          RankFour.coreEmbedding
      disjoint := by
        intro g j h
        have h' : RankFour.coreEmbedding (RankFour.compressionEnd L g) =
            RankFour.coreEmbedding (FamilyRankFour.witnessEmbedding L j) :=
          (RankFour.compressorSet_conjugation L (RankFour.compressor L)
            (RankFour.compressor_mem L) g).trans h
        exact (FamilyRankFour.compressionEnd_eq_witnessEmbedding_iff L g j).mp
          (RankFour.coreEmbedding_injective h') }

include L in
/-- **The Leavitt-corner theorem, ranks three and four.**  Let `A` be a
nontrivial countable unital ring carrying a binary Leavitt family, and
suppose `EL₃(A)` and `EL₄(A)` have Kazhdan's property `(T)`.  Then
`EL₄(A)` is not sofic.  No finite-generation or coefficient hypothesis is
made: finite generation follows from `(T)`, and the compressor words are
explicit products of elementary transvections over every ring. -/
theorem ambient_not_isSofic [Nontrivial A] [Countable A]
    (hTG : HasKazhdanPropertyT.{0, 0} (RankFour.Ambient A))
    (hTΓ : HasKazhdanPropertyT.{0, 0} (RankFour.Core A)) :
    ¬ IsSofic (RankFour.Ambient A) :=
  not_isSofic_of_not_isLEF (compressionSetupOfKazhdan L hTΓ) hTG hTΓ
    (FamilyRankFour.witness_not_isLEF L)

end

end LeavittCornerTheorem
end NonsoficGroupsExist
