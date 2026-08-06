import NonsoficGroupsExist.Criterion.CriterionAssembly
import NonsoficGroupsExist.Leavitt.DiagonalCornerCompression
import NonsoficGroupsExist.PropertyT.FiniteFieldElementaryPropertyT
import NonsoficGroupsExist.Leavitt.LeavittRankEquivalence
import NonsoficGroupsExist.Leavitt.RankFourCompressors
import NonsoficGroupsExist.Leavitt.ThompsonWitness
import NonsoficGroupsExist.Leavitt.PrefixCode

/-!
# The rank-four compression pipeline over any ring with a binary Leavitt family

`FiniteFieldLeavitt` instantiates the compression–centralizer criterion for
the presented algebra `L_k(1,2)`.  Every ingredient of that construction is in
fact uniform in the pair `(A, L)` of a coefficient ring and a binary Leavitt
family: the compressor words, the corner witness, the centralizer and
disjointness calculations, the finite generation, and both property-`(T)`
inputs (rank three by Ershov–Jaikin-Zapirain over a finite field, rank four by
the Leavitt rank equivalence).  This module states the pipeline at that
generality:

> Let `k` be a finite field and `A` a nontrivial countable finite-type
> `k`-algebra carrying a binary Leavitt family.  Then `EL₄(A)` is nonsofic,
> hence so are `EL_{m+1}(A)` for every `m ≥ 1`, the unit group `Aˣ`, and
> every `GL_{m+1}(A)`.

The point of the generality is the dossier's corner route: a `d`-ary Leavitt
family places a binary family in the corner ring of `AryCorner`, and this
module applied to that corner produces nonsofic subgroups inside the `d`-ary
unit group.  The subring hypotheses (finite type, countable, nontrivial) hold
there automatically.

Infiniteness of the elementary groups is derived, not assumed: `Leavitt`
already proves that a nontrivial ring carrying a binary family is infinite.
-/

namespace NonsoficGroupsExist

namespace FamilyRankFour

noncomputable section

variable {A : Type} [Ring A]

/-! ### Countability -/

private theorem countable_units {M : Type*} [Monoid M] [Countable M] :
    Countable Mˣ :=
  Function.Injective.countable
    (f := (Units.val : Mˣ → M)) fun _ _ h => Units.ext h

instance matrixCountable (m : ℕ) [Countable A] :
    Countable (Matrix (Fin m) (Fin m) A) :=
  inferInstanceAs (Countable (Fin m → Fin m → A))

instance unitsMatrixCountable (m : ℕ) [Countable A] :
    Countable ((Matrix (Fin m) (Fin m) A)ˣ) :=
  countable_units

instance coreCountable [Countable A] : Countable (RankFour.Core A) :=
  inferInstance

instance ambientCountable [Countable A] : Countable (RankFour.Ambient A) :=
  inferInstance

instance unitsCountable [Countable A] : Countable Aˣ :=
  countable_units

/-! ### The algebraic core of the compression setup, uniform in the family -/

variable (L : LeavittFamily A)

/-- The corner witness, embedded into `EL₃(A)` as a first-coordinate
diagonal unit. -/
def witnessEmbedding : L.cornerWitnessSubgroup →* RankFour.Core A :=
  ((DiagonalElementary.firstDiagonalUnitHom (R := A)).comp
      L.cornerWitnessSubgroup.subtype).codRestrict
    (elementaryGroup (Fin 3) A) (by
      intro j
      exact DiagonalElementary.firstDiagonalUnit_mem_of_mem_commutator
        (L.cornerWitnessSubgroup_le_commutator j.property))

theorem witnessEmbedding_injective :
    Function.Injective (witnessEmbedding L) := by
  intro x y hxy
  apply Subtype.ext
  apply DiagonalElementary.firstDiagonalUnitHom_injective
  exact congrArg (fun z : RankFour.Core A =>
    (z : (Matrix (Fin 3) (Fin 3) A)ˣ)) hxy

theorem compressionEnd_commutes_witnessEmbedding
    (g : RankFour.Core A) (j : L.cornerWitnessSubgroup) :
    Commute (RankFour.compressionEnd L g) (witnessEmbedding L j) := by
  obtain ⟨u, hu⟩ := L.cornerWitnessSubgroup_le_cornerSubgroup j.property
  have hj : (j : Aˣ) = L.cornerHom u := hu.symm
  apply (commute_iff_eq _ _).2
  apply Subtype.ext
  apply Units.ext
  change
    L.matrixCompression
          (↑(g : (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A) *
        (↑(DiagonalElementary.firstDiagonalUnitHom (j : Aˣ)) :
          Matrix (Fin 3) (Fin 3) A) =
      (↑(DiagonalElementary.firstDiagonalUnitHom (j : Aˣ)) :
          Matrix (Fin 3) (Fin 3) A) *
        L.matrixCompression
          (↑(g : (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A)
  rw [hj]
  exact L.matrixCompression_commutes_firstDiagonalCorner _ u

theorem compressionEnd_eq_witnessEmbedding_iff
    (g : RankFour.Core A) (j : L.cornerWitnessSubgroup) :
    RankFour.compressionEnd L g = witnessEmbedding L j ↔ g = 1 ∧ j = 1 := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := L.cornerWitnessSubgroup_le_cornerSubgroup j.property
    have hj : (j : Aˣ) = L.cornerHom u := hu.symm
    have hmatrix := congrArg
      (fun z : RankFour.Core A =>
        (↑(z : (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A)) h
    change
      L.matrixCompression
          (↑(g : (Matrix (Fin 3) (Fin 3) A)ˣ) : Matrix (Fin 3) (Fin 3) A) =
        (↑(DiagonalElementary.firstDiagonalUnitHom (j : Aˣ)) :
          Matrix (Fin 3) (Fin 3) A) at hmatrix
    rw [hj] at hmatrix
    obtain ⟨hg, hu'⟩ :=
      (L.matrixCompression_eq_firstDiagonalCorner_iff _ u).mp hmatrix
    constructor
    · apply Subtype.ext
      apply Units.ext
      exact hg
    · apply Subtype.ext
      change (j : Aˣ) = 1
      rw [hj, hu', map_one]
  · rintro ⟨rfl, rfl⟩
    exact (map_one (RankFour.compressionEnd L)).trans
      (map_one (witnessEmbedding L)).symm

theorem witness_not_isLEF [Nontrivial A] : ¬ IsLEF L.cornerWitnessSubgroup :=
  L.not_isLEF_cornerWitnessSubgroup

/-! ### Symmetric finite generating sets -/

private theorem exists_symmetric_generators (G : Type*) [Group G]
    [Group.FG G] :
    ∃ S : Finset G,
      1 ∈ S ∧ (∀ g ∈ S, g⁻¹ ∈ S) ∧ Subgroup.closure (S : Set G) = ⊤ := by
  classical
  obtain ⟨_, S, _, hS⟩ := Group.fg_iff'.mp (inferInstance : Group.FG G)
  let T : Finset G := insert 1 (S ∪ S.image fun g => g⁻¹)
  refine ⟨T, Finset.mem_insert_self 1 _, ?_, ?_⟩
  · intro g hg
    simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      at hg ⊢
    rcases hg with h | h | ⟨x, hx, rfl⟩
    · left
      simp [h]
    · exact Or.inr (Or.inr ⟨g, h, rfl⟩)
    · exact Or.inr (Or.inl (by simpa using hx))
  · apply top_unique
    rw [← hS]
    exact Subgroup.closure_mono (by intro g hg; simp [T, hg])

include L in
/-- The rank-three core is infinite over any nontrivial ring with a binary
family. -/
theorem coreInfinite [Nontrivial A] : Infinite (RankFour.Core A) := by
  haveI := L.infinite
  exact elementaryGroup_infinite (R := A) (0 : Fin 3) 1 (by decide)

/-! ### Finite generation and the assembled setup

These need the finite field: finite generation of the elementary groups uses
that `A` has finite type over a finite coefficient field. -/

section FiniteField

variable (k : Type) [Field k] [Finite k] [Algebra k A] [Algebra.FiniteType k A]

include k in
theorem coreFG : Group.FG (RankFour.Core A) :=
  elementaryGroup_finitelyGenerated_finiteField (k := k) (R := A) 3 (by omega)

include k in
theorem ambientFG : Group.FG (RankFour.Ambient A) :=
  elementaryGroup_finitelyGenerated_finiteField (k := k) (R := A) 4 (by omega)

include k in
theorem core_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (RankFour.Core A) :=
  finiteFieldElementaryThree_hasKazhdanPropertyT (k := k) (A := A)

include L k in
theorem ambient_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} (RankFour.Ambient A) :=
  L.rankFour_propertyT_of_rankThree (core_hasKazhdanPropertyT (A := A) k)

variable [Nontrivial A]

include k in
/-- The compression–centralizer setup of the manuscript, for an arbitrary
nontrivial finite-type algebra over a finite field carrying a binary Leavitt
family. -/
def compressionSetup :
    CompressionSetup (RankFour.Ambient A) (RankFour.Core A)
      L.cornerWitnessSubgroup := by
  classical
  haveI : Group.FG (RankFour.Core A) := coreFG k
  exact
    { embedΓ := RankFour.coreEmbedding
      embedΓ_injective := RankFour.coreEmbedding_injective
      embedJ := witnessEmbedding L
      embedJ_injective := witnessEmbedding_injective L
      generatorsΓ :=
        Classical.choose (exists_symmetric_generators (RankFour.Core A))
      generatorsΓ_one :=
        (Classical.choose_spec
          (exists_symmetric_generators (RankFour.Core A))).1
      generatorsΓ_symmetric :=
        (Classical.choose_spec
          (exists_symmetric_generators (RankFour.Core A))).2.1
      generatorsΓ_generate :=
        (Classical.choose_spec
          (exists_symmetric_generators (RankFour.Core A))).2.2
      generatorsJ := L.cornerWitnessGenerators
      generatorsJ_symmetric := L.cornerWitnessGenerators_symmetric
      generatorsJ_generate := L.cornerWitnessGenerators_generate
      infiniteΓ := coreInfinite L
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
        exact (compressionEnd_commutes_witnessEmbedding L g j).map
          RankFour.coreEmbedding
      disjoint := by
        intro g j h
        have h' : RankFour.coreEmbedding (RankFour.compressionEnd L g) =
            RankFour.coreEmbedding (witnessEmbedding L j) :=
          (RankFour.compressorSet_conjugation L (RankFour.compressor L)
            (RankFour.compressor_mem L) g).trans h
        exact (compressionEnd_eq_witnessEmbedding_iff L g j).mp
          (RankFour.coreEmbedding_injective h') }

variable [Countable A]

include L k in
/-- **The generic rank-four theorem.**  `EL₄(A)` is nonsofic for every
nontrivial countable finite-type algebra over a finite field carrying a
binary Leavitt family. -/
theorem ambient_not_isSofic : ¬ IsSofic (RankFour.Ambient A) :=
  not_isSofic_of_not_isLEF (compressionSetup L k)
    (ambient_hasKazhdanPropertyT L k) (core_hasKazhdanPropertyT (A := A) k)
    (witness_not_isLEF L)

include L k in
/-- Every elementary group of rank at least two over `A` is nonsofic: the
binary rank equivalence carries rank four to every positive successor
rank. -/
theorem elementary_not_isSofic (m : ℕ) (hm : 0 < m) :
    ¬ IsSofic (elementaryGroup (Fin (m + 1)) A) := by
  intro hS
  exact ambient_not_isSofic L k
    ((isSofic_mulEquiv_iff (L.rankSuccEquiv m 3 hm (by omega))).mp hS)

include L k in
/-- The unit group `Aˣ` is nonsofic: the four-leaf comb code identifies it
with `GL₄(A)`, which contains the nonsofic `EL₄(A)`. -/
theorem units_not_isSofic : ¬ IsSofic Aˣ := by
  intro hUnits
  have hGL : IsSofic ((Matrix (Fin 4) (Fin 4) A)ˣ) :=
    (isSofic_mulEquiv_iff
      (L.prefixUnitsEquiv (leftCombCode 3) (L.leftCombCode_complete 3))).mpr
      hUnits
  exact ambient_not_isSofic L k
    (isSofic_of_injective (elementaryGroup (Fin 4) A).subtype
      Subtype.val_injective hGL)

include L k in
/-- Every positive-rank general linear group over `A` is nonsofic. -/
theorem gl_not_isSofic (m : ℕ) :
    ¬ IsSofic ((Matrix (Fin (m + 1)) (Fin (m + 1)) A)ˣ) := by
  intro hGL
  exact units_not_isSofic L k
    ((isSofic_mulEquiv_iff
      (L.prefixUnitsEquiv (leftCombCode m) (L.leftCombCode_complete m))).mp
      hGL)

end FiniteField

end

end FamilyRankFour
end NonsoficGroupsExist
