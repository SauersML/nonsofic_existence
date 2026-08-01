import NonsoficGroupsExist.Criterion

/-!
# Matched components

This file supplies the bookkeeping of Section `subsec:selection` of the
manuscript: once the compressor has been shown to match `Γ`-components almost
bijectively, the matched pairs must be turned into a single localized
approximation, and every error term must be transported from the source
partition to the target partition.

The three quantities are:

* `matchedRetainedSupport R` -- the union of the retained blocks;
* `matchedCore R D` -- the union of the parts of retained blocks that survive
  inside their matched targets;
* `wordCrossing P p` -- the set of vertices whose `p`-arc leaves its block.

The main estimate, `wordCrossing_card_le`, is the transfer inequality

  `|crossing P p| ≤ |crossing Q p| + 2 |Yₙ \ core|`,

which is what allows the manuscript to replace the ambient partition by the
matched one at a cost of `o(|Yₙ|)`.
-/

namespace NonsoficGroupsExist

open scoped BigOperators symmDiff

variable {Y : FiniteModel}

/-- Vertices whose `p`-arc crosses the partition. -/
def wordCrossing (P : BlockStructure Y) (p : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun y ↦ P.block (p y) ≠ P.block y

@[simp] theorem mem_wordCrossing (P : BlockStructure Y) (p : Equiv.Perm Y)
    (y : Y) : y ∈ wordCrossing P p ↔ P.block (p y) ≠ P.block y := by
  simp [wordCrossing]

/-- The union of the retained blocks. -/
def matchedRetainedSupport (R : Finset (Finset Y)) : Finset Y :=
  R.biUnion id

/-- The union of the retained blocks intersected with their matched targets. -/
def matchedCore (R : Finset (Finset Y)) (D : Finset Y → Finset Y) : Finset Y :=
  R.biUnion fun C ↦ C ∩ D C

theorem matchedCore_subset_retained (R : Finset (Finset Y))
    (D : Finset Y → Finset Y) :
    matchedCore R D ⊆ matchedRetainedSupport R := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_biUnion.mpr ⟨C, hC, by simpa using (Finset.mem_inter.mp hxC).1⟩

/-- Blocks of a `BlockStructure` are pairwise disjoint, so the cardinality of a
union of distinct blocks is the sum of their cardinalities. -/
theorem matchedRetainedSupport_card (P : BlockStructure Y)
    (R : Finset (Finset Y)) (hR : ∀ C ∈ R, ∃ y, C = P.block y) :
    (matchedRetainedSupport R).card = ∑ C ∈ R, C.card := by
  classical
  apply Finset.card_biUnion
  intro C hC C' hC' hne
  obtain ⟨y, rfl⟩ := hR C hC
  obtain ⟨y', rfl⟩ := hR C' hC'
  exact P.block_disjoint hne

theorem matchedCore_card (P : BlockStructure Y) (R : Finset (Finset Y))
    (hR : ∀ C ∈ R, ∃ y, C = P.block y) (D : Finset Y → Finset Y) :
    (matchedCore R D).card = ∑ C ∈ R, (C ∩ D C).card := by
  classical
  apply Finset.card_biUnion
  intro C hC C' hC' hne
  obtain ⟨y, rfl⟩ := hR C hC
  obtain ⟨y', rfl⟩ := hR C' hC'
  exact (P.block_disjoint hne).mono Finset.inter_subset_left
    Finset.inter_subset_left

/-- The mass missing from the matched core, split into discarded blocks and
matching defects. -/
theorem matchedCore_missing_card (P : BlockStructure Y) (R : Finset (Finset Y))
    (hR : ∀ C ∈ R, ∃ y, C = P.block y) (D : Finset Y → Finset Y) :
    ((Finset.univ : Finset Y) \ matchedCore R D).card =
      ((Finset.univ : Finset Y) \ matchedRetainedSupport R).card +
        ∑ C ∈ R, (C \ D C).card := by
  classical
  have hcore := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (matchedCore R D))
  have hret := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (matchedRetainedSupport R))
  have hsplit : (∑ C ∈ R, (C \ D C).card) + (matchedCore R D).card =
      (matchedRetainedSupport R).card := by
    rw [matchedCore_card P R hR D, matchedRetainedSupport_card P R hR,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun C _ ↦ Finset.card_sdiff_add_card_inter C (D C)
  omega

theorem matchedCore_missing_card_le_symmDiff (P : BlockStructure Y)
    (R : Finset (Finset Y)) (hR : ∀ C ∈ R, ∃ y, C = P.block y)
    (D : Finset Y → Finset Y) :
    ((Finset.univ : Finset Y) \ matchedCore R D).card ≤
      ((Finset.univ : Finset Y) \ matchedRetainedSupport R).card +
        ∑ C ∈ R, (C ∆ D C).card := by
  classical
  rw [matchedCore_missing_card P R hR D]
  refine Nat.add_le_add_left (Finset.sum_le_sum fun C _ ↦ ?_) _
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_symmDiff]
  exact Or.inl (Finset.mem_sdiff.mp hx)

/-- Distinct retained blocks receive distinct targets, provided each target is
dominated by its source.  This is Proposition `prop:match`(iii) in the form used
by the localization step. -/
theorem matching_injOn (P : BlockStructure Y) (R : Finset (Finset Y))
    (hR : ∀ C ∈ R, ∃ y, C = P.block y) (D : Finset Y → Finset Y)
    (hmajor : ∀ C ∈ R, (D C).card < 2 * (C ∩ D C).card) :
    Set.InjOn D (R : Set (Finset Y)) := by
  classical
  intro C hC C' hC' heq
  by_contra hne
  obtain ⟨y, rfl⟩ := hR C hC
  obtain ⟨y', rfl⟩ := hR C' hC'
  exact dominant_intersection_unique _ _ (D (P.block y))
    (P.block_disjoint hne) (hmajor _ hC) (by simpa [heq] using hmajor _ hC')

/-- Points of the core sent outside the core. -/
def matchedPreimageBad (R : Finset (Finset Y)) (D : Finset Y → Finset Y)
    (p : Equiv.Perm Y) : Finset Y :=
  Finset.univ.filter fun y ↦ p y ∈ (Finset.univ : Finset Y) \ matchedCore R D

theorem matchedPreimageBad_card_le (R : Finset (Finset Y))
    (D : Finset Y → Finset Y) (p : Equiv.Perm Y) :
    (matchedPreimageBad R D p).card ≤
      ((Finset.univ : Finset Y) \ matchedCore R D).card := by
  classical
  apply Finset.card_le_card_of_injOn p
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy
    exact p.injective hxy

/-- **The transfer inequality.**  Off the matched core, crossings of the source
partition are controlled by crossings of the target partition. -/
theorem wordCrossing_subset (P Q : BlockStructure Y) (R : Finset (Finset Y))
    (hR : ∀ C ∈ R, ∃ y, C = P.block y) (D : Finset Y → Finset Y)
    (hD : ∀ C ∈ R, ∃ y, D C = Q.block y)
    (hinj : Set.InjOn D (R : Set (Finset Y))) (p : Equiv.Perm Y) :
    wordCrossing P p ⊆
      wordCrossing Q p ∪ ((Finset.univ : Finset Y) \ matchedCore R D) ∪
        matchedPreimageBad R D p := by
  classical
  intro x hx
  have hxP : P.block (p x) ≠ P.block x := (mem_wordCrossing P p x).mp hx
  by_cases hxcore : x ∈ matchedCore R D
  · by_cases hxQ : Q.block (p x) = Q.block x
    · by_cases hpcore : p x ∈ matchedCore R D
      · exfalso
        obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hxcore
        obtain ⟨C', hC', hpC'⟩ := Finset.mem_biUnion.mp hpcore
        obtain ⟨hxC₁, hxC₂⟩ := Finset.mem_inter.mp hxC
        obtain ⟨hpC₁, hpC₂⟩ := Finset.mem_inter.mp hpC'
        obtain ⟨y, hy⟩ := hD C hC
        obtain ⟨y', hy'⟩ := hD C' hC'
        have hQx : Q.block x = D C := by
          rw [hy]
          exact (Q.eq_of_mem y x (by rw [← hy]; exact hxC₂))
        have hQp : Q.block (p x) = D C' := by
          rw [hy']
          exact (Q.eq_of_mem y' (p x) (by rw [← hy']; exact hpC₂))
        have hCC' : D C = D C' := by rw [← hQx, ← hQp, hxQ]
        have hCeq : C = C' := hinj hC hC' hCC'
        subst hCeq
        obtain ⟨z, hz⟩ := hR C hC
        apply hxP
        rw [show P.block x = C from by
              rw [hz]; exact P.eq_of_mem z x (by rw [← hz]; exact hxC₁),
          show P.block (p x) = C from by
              rw [hz]; exact P.eq_of_mem z (p x) (by rw [← hz]; exact hpC₁)]
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpcore⟩⟩
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ ((mem_wordCrossing Q p x).mpr hxQ))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxcore⟩))

theorem wordCrossing_card_le (P Q : BlockStructure Y) (R : Finset (Finset Y))
    (hR : ∀ C ∈ R, ∃ y, C = P.block y) (D : Finset Y → Finset Y)
    (hD : ∀ C ∈ R, ∃ y, D C = Q.block y)
    (hinj : Set.InjOn D (R : Set (Finset Y))) (p : Equiv.Perm Y) :
    (wordCrossing P p).card ≤
      (wordCrossing Q p).card +
        2 * ((Finset.univ : Finset Y) \ matchedCore R D).card := by
  classical
  have hsub := Finset.card_le_card
    (wordCrossing_subset P Q R hR D hD hinj p)
  have hfirst := Finset.card_union_le (wordCrossing Q p)
    ((Finset.univ : Finset Y) \ matchedCore R D)
  have hsecond := Finset.card_union_le
    (wordCrossing Q p ∪ ((Finset.univ : Finset Y) \ matchedCore R D))
    (matchedPreimageBad R D p)
  have hpre := matchedPreimageBad_card_le R D p
  omega

/-! ### Densities -/

variable {model : ℕ → FiniteModel}

/-- The missing mass of the matched core is negligible as soon as the discarded
mass and the total matching defect are. -/
theorem matchedCore_missing_negligible
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (P : ∀ n, BlockStructure (model n)) (R : ∀ n, Finset (Finset (model n)))
    (hR : ∀ n, ∀ C ∈ R n, ∃ y, C = (P n).block y)
    (D : ∀ n, Finset (model n) → Finset (model n))
    (hdiscard : Negligible N fun n ↦
      (((Finset.univ : Finset (model n)) \ matchedRetainedSupport (R n)).card : ℝ))
    (hdefect : Negligible N fun n ↦
      ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ)) :
    Negligible N fun n ↦
      (((Finset.univ : Finset (model n)) \ matchedCore (R n) (D n)).card : ℝ) := by
  refine Negligible.mono hN (fun n ↦ by positivity) (fun n ↦ ?_)
    (Negligible.add hdiscard hdefect)
  exact_mod_cast matchedCore_missing_card_le_symmDiff (P n) (R n) (hR n) (D n)

/-- Crossings transfer from the target partition to the source partition at a
negligible cost. -/
theorem wordCrossing_negligible
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (P Q : ∀ n, BlockStructure (model n)) (R : ∀ n, Finset (Finset (model n)))
    (hR : ∀ n, ∀ C ∈ R n, ∃ y, C = (P n).block y)
    (D : ∀ n, Finset (model n) → Finset (model n))
    (hD : ∀ n, ∀ C ∈ R n, ∃ y, D n C = (Q n).block y)
    (hinj : ∀ n, Set.InjOn (D n) (R n : Set (Finset (model n))))
    (p : ∀ n, Equiv.Perm (model n))
    (hmissing : Negligible N fun n ↦
      (((Finset.univ : Finset (model n)) \ matchedCore (R n) (D n)).card : ℝ))
    (htarget : Negligible N fun n ↦ ((wordCrossing (Q n) (p n)).card : ℝ)) :
    Negligible N fun n ↦ ((wordCrossing (P n) (p n)).card : ℝ) := by
  refine Negligible.mono hN (fun n ↦ by positivity) (fun n ↦ ?_)
    (Negligible.add htarget (Negligible.const_mul 2 hmissing))
  have := wordCrossing_card_le (P n) (Q n) (R n) (hR n) (D n) (hD n) (hinj n) (p n)
  exact_mod_cast this

end NonsoficGroupsExist
