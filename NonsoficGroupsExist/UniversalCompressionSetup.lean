import NonsoficGroupsExist.CompressionSetup
import NonsoficGroupsExist.UniversalRankFour

/-!
# The universal Leavitt rank-four compression setup

This module closes the algebraic specification consumed by the local matching
argument.  Every field is instantiated by the universal binary Leavitt
algebra, the explicit rank-four compressor words, and the cylinder witness.
-/

namespace NonsoficGroupsExist
namespace UniversalRankFour

private theorem exists_core_generators :
    ∃ S : Finset Core,
      1 ∈ S ∧ (∀ g ∈ S, g⁻¹ ∈ S) ∧
        Subgroup.closure (S : Set Core) = ⊤ := by
  classical
  obtain ⟨_, S, _, hS⟩ := Group.fg_iff'.mp (inferInstance : Group.FG Core)
  let T : Finset Core := insert 1 (S ∪ S.image fun g ↦ g⁻¹)
  refine ⟨T, Finset.mem_insert_self 1 _, ?_, ?_⟩
  · intro g hg
    simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hg ⊢
    rcases hg with h | h | ⟨x, hx, rfl⟩
    · left
      simp [h]
    · exact Or.inr (Or.inr ⟨g, h, rfl⟩)
    · exact Or.inr (Or.inl (by simpa using hx))
  · apply top_unique
    rw [← hS]
    exact Subgroup.closure_mono (by
      intro g hg
      simp [T, hg])

private noncomputable def coreGenerators : Finset Core :=
  Classical.choose exists_core_generators

private theorem coreGenerators_symmetric :
    ∀ g ∈ coreGenerators, g⁻¹ ∈ coreGenerators :=
  (Classical.choose_spec exists_core_generators).2.1

private theorem coreGenerators_one : 1 ∈ coreGenerators := by
  exact (Classical.choose_spec exists_core_generators).1

private theorem coreGenerators_generate :
    Subgroup.closure (coreGenerators : Set Core) = ⊤ :=
  (Classical.choose_spec exists_core_generators).2.2

/-- The complete universal-Leavitt algebraic setup required by the compression
criterion.  In particular, neither an embedding nor a centralizer or
intersection assertion is supplied by a caller. -/
noncomputable def compressionSetup : CompressionSetup Ambient Core Witness := by
  classical
  exact
    { embedΓ := coreEmbedding
      embedΓ_injective := coreEmbedding_injective
      embedJ := witnessEmbedding
      embedJ_injective := witnessEmbedding_injective
      generatorsΓ := coreGenerators
      generatorsΓ_one := coreGenerators_one
      generatorsΓ_symmetric := coreGenerators_symmetric
      generatorsΓ_generate := coreGenerators_generate
      generatorsJ := family.cornerWitnessGenerators
      generatorsJ_symmetric := family.cornerWitnessGenerators_symmetric
      generatorsJ_generate := family.cornerWitnessGenerators_generate
      infiniteΓ := inferInstance
      compressors := compressors
      distinguished := RankFour.compressor family
      distinguished_mem := RankFour.compressor_mem family
      compressedEnd := fun _ _ ↦ compressionEnd
      compressedEnd_spec := compressor_conjugation
      generates := core_compressors_generate
      centralizes := by
        intro g j
        rw [← compressor_conjugation (RankFour.compressor family)
          (RankFour.compressor_mem family) g]
        exact (compressionEnd_commutes_witnessEmbedding g j).map coreEmbedding
      disjoint := by
        intro g j h
        have h' : coreEmbedding (compressionEnd g) =
            coreEmbedding (witnessEmbedding j) :=
          (compressor_conjugation (RankFour.compressor family)
            (RankFour.compressor_mem family) g).trans h
        exact (compressionEnd_eq_witnessEmbedding_iff g j).mp
          (coreEmbedding_injective h') }

end UniversalRankFour
end NonsoficGroupsExist
