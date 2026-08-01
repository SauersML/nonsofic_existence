import NonsoficGroupsExist.BlockEnumeration

/-!
# Transporting component partitions

A compressor acts by a genuine permutation on every finite model.  The source
expander decomposition is therefore transported occurrence-by-occurrence,
including parallel edges, and its component partition is transported by the
same permutation.  This file records the exact finite-set identities.
-/

namespace NonsoficGroupsExist
namespace BlockStructure

variable {Y : FiniteModel} (P : BlockStructure Y)

/-- Transport a block partition by a permutation. -/
noncomputable def transport (q : Equiv.Perm Y) : BlockStructure Y where
  block y := (P.block (q.symm y)).image q
  self_mem y := by
    classical
    exact Finset.mem_image.mpr ⟨q.symm y, P.self_mem (q.symm y), q.apply_symm_apply y⟩
  eq_of_mem x y hy := by
    classical
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    have hzq : z = q.symm y := by
      rw [← hzy]
      simp
    rw [← hzq, P.eq_of_mem (q.symm x) z hz]

@[simp] theorem transport_block (q : Equiv.Perm Y) (y : Y) :
    (P.transport q).block (q y) = (P.block y).image q := by
  simp [transport]

@[simp] theorem transport_size (q : Equiv.Perm Y) (y : Y) :
    (P.transport q).size (q y) = P.size y := by
  classical
  change ((P.transport q).block (q y)).card = (P.block y).card
  rw [P.transport_block]
  exact Finset.card_image_of_injective _ q.injective

theorem transport_blocksFinset (q : Equiv.Perm Y) :
    (P.transport q).blocksFinset = P.blocksFinset.image (Finset.image q) := by
  classical
  ext C
  simp only [mem_blocksFinset, Finset.mem_image]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨P.block (q.symm y), ⟨q.symm y, rfl⟩, ?_⟩
    simp [transport]
  · rintro ⟨B, ⟨y, rfl⟩, rfl⟩
    exact ⟨q y, by simp⟩

theorem image_block_card (q : Equiv.Perm Y) (y : Y) :
    ((P.block y).image q).card = (P.block y).card :=
  Finset.card_image_of_injective _ q.injective

end BlockStructure
end NonsoficGroupsExist
