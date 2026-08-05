import NonsoficGroupsExist.PrefixCode

/-!
# Thompson's group `V` as prefix substitutions

The manuscript presents Thompson's group `V` as the group of
homeomorphisms of the boundary `{0,1}^ℕ` given by tree tables: a pair of
ordered complete leaf sets `(β_i)`, `(α_i)` acting by the prefix
substitutions `β_i x ↦ α_i x`.  This module defines the boundary, the
covering property of a prefix code, the bijection determined by a table,
and the group `V` itself (checkpoint `D1`).
-/

namespace NonsoficGroupsExist
namespace ThompsonV

/-- The boundary of the rooted binary tree: infinite binary streams. -/
abbrev Boundary := ℕ → Fin 2

/-- A finite word is an initial segment of a stream. -/
def IsStreamPrefix (w : List (Fin 2)) (x : Boundary) : Prop :=
  ∀ k : ℕ, ∀ h : k < w.length, x k = w[k]

instance (w : List (Fin 2)) (x : Boundary) :
    Decidable (IsStreamPrefix w x) :=
  Nat.decidableBallLT w.length fun k h ↦ x k = w[k]

/-- Prepend a finite word to a stream. -/
def prepend (w : List (Fin 2)) (x : Boundary) : Boundary := fun n ↦
  if h : n < w.length then w[n] else x (n - w.length)

/-- Delete the first `m` letters of a stream. -/
def drop (m : ℕ) (x : Boundary) : Boundary := fun n ↦ x (n + m)

theorem isStreamPrefix_prepend (w : List (Fin 2)) (x : Boundary) :
    IsStreamPrefix w (prepend w x) := by
  intro k h
  simp [prepend, h]

theorem drop_prepend (w : List (Fin 2)) (x : Boundary) :
    drop w.length (prepend w x) = x := by
  funext n
  simp [drop, prepend]

theorem prepend_drop_of_isStreamPrefix (w : List (Fin 2)) (x : Boundary)
    (h : IsStreamPrefix w x) : prepend w (drop w.length x) = x := by
  funext n
  by_cases hn : n < w.length
  · rw [prepend]
    rw [dif_pos hn]
    exact (h n hn).symm
  · rw [prepend]
    rw [dif_neg hn]
    rw [drop]
    congr 1
    omega

/-- A code covers the boundary when every stream extends one of its
words. -/
def Covers {ι : Type*} (E : BinaryPrefixCode ι) : Prop :=
  ∀ x : Boundary, ∃ i, IsStreamPrefix (E.word i) x

/-- Two comparable stream prefixes at the same point are prefix-comparable
words. -/
theorem prefix_or_prefix_of_isStreamPrefix {v w : List (Fin 2)}
    {x : Boundary} (hv : IsStreamPrefix v x) (hw : IsStreamPrefix w x) :
    v <+: w ∨ w <+: v := by
  rcases le_total v.length w.length with hle | hle
  · left
    refine List.prefix_iff_getElem.mpr ⟨hle, fun k hk ↦ ?_⟩
    rw [← hv k hk, hw k (lt_of_lt_of_le hk hle)]
  · right
    refine List.prefix_iff_getElem.mpr ⟨hle, fun k hk ↦ ?_⟩
    rw [← hw k hk, hv k (lt_of_lt_of_le hk hle)]

/-- The covering index of a stream is unique for a prefix code. -/
theorem covering_index_unique {ι : Type*} (E : BinaryPrefixCode ι)
    {x : Boundary} {i j : ι} (hi : IsStreamPrefix (E.word i) x)
    (hj : IsStreamPrefix (E.word j) x) : i = j := by
  by_contra hne
  rcases prefix_or_prefix_of_isStreamPrefix hi hj with h | h
  · exact E.prefix_free hne h
  · exact E.prefix_free (Ne.symm hne) h

open Classical in
/-- The index of the unique code word heading a stream. -/
noncomputable def coveringIndex {ι : Type*} (E : BinaryPrefixCode ι)
    (hE : Covers E) (x : Boundary) : ι :=
  (hE x).choose

theorem coveringIndex_spec {ι : Type*} (E : BinaryPrefixCode ι)
    (hE : Covers E) (x : Boundary) :
    IsStreamPrefix (E.word (coveringIndex E hE x)) x :=
  (hE x).choose_spec

theorem coveringIndex_eq {ι : Type*} (E : BinaryPrefixCode ι)
    (hE : Covers E) {x : Boundary} {i : ι}
    (hi : IsStreamPrefix (E.word i) x) :
    coveringIndex E hE x = i :=
  covering_index_unique E (coveringIndex_spec E hE x) hi

theorem coveringIndex_prepend {ι : Type*} (E : BinaryPrefixCode ι)
    (hE : Covers E) (i : ι) (x : Boundary) :
    coveringIndex E hE (prepend (E.word i) x) = i :=
  coveringIndex_eq E hE (isStreamPrefix_prepend (E.word i) x)

/-- The raw prefix-substitution map of a tree table: delete the covering
`E`-word and prepend the matching `B`-word. -/
noncomputable def tableMap {ι : Type*} (E B : BinaryPrefixCode ι)
    (hE : Covers E) (x : Boundary) : Boundary :=
  prepend (B.word (coveringIndex E hE x))
    (drop (E.word (coveringIndex E hE x)).length x)

theorem tableMap_prepend {ι : Type*} (E B : BinaryPrefixCode ι)
    (hE : Covers E) (i : ι) (x : Boundary) :
    tableMap E B hE (prepend (E.word i) x) = prepend (B.word i) x := by
  rw [tableMap, coveringIndex_prepend E hE i x, drop_prepend]

theorem tableMap_leftInverse {ι : Type*} (E B : BinaryPrefixCode ι)
    (hE : Covers E) (hB : Covers B) (x : Boundary) :
    tableMap B E hB (tableMap E B hE x) = x := by
  set i := coveringIndex E hE x with hi
  have hx : x = prepend (E.word i)
      (drop (E.word i).length x) :=
    (prepend_drop_of_isStreamPrefix _ x
      (coveringIndex_spec E hE x)).symm
  calc
    tableMap B E hB (tableMap E B hE x) =
        tableMap B E hB (tableMap E B hE (prepend (E.word i)
          (drop (E.word i).length x))) := by rw [← hx]
    _ = tableMap B E hB (prepend (B.word i)
        (drop (E.word i).length x)) := by
      rw [tableMap_prepend E B hE i]
    _ = prepend (E.word i) (drop (E.word i).length x) := by
      rw [tableMap_prepend B E hB i]
    _ = x := by rw [← hx]

/-- The bijection of the boundary determined by a tree table. -/
noncomputable def tableEquiv {ι : Type*} (E B : BinaryPrefixCode ι)
    (hE : Covers E) (hB : Covers B) : Equiv.Perm Boundary where
  toFun := tableMap E B hE
  invFun := tableMap B E hB
  left_inv := tableMap_leftInverse E B hE hB
  right_inv := tableMap_leftInverse B E hB hE

/-- **Thompson's group `V`** (checkpoint `D1`): the group of permutations
of the boundary generated by the tree tables over all finite index
types.  Since composites and inverses of tables are again tables after a
common refinement, this closure is exactly the set of table maps of the
manuscript. -/
noncomputable def thompsonV : Subgroup (Equiv.Perm Boundary) :=
  Subgroup.closure
    {f | ∃ (m : ℕ) (E B : BinaryPrefixCode (Fin m))
      (hE : Covers E) (hB : Covers B), f = tableEquiv E B hE hB}

theorem tableEquiv_mem_thompsonV {m : ℕ}
    (E B : BinaryPrefixCode (Fin m)) (hE : Covers E) (hB : Covers B) :
    tableEquiv E B hE hB ∈ thompsonV :=
  Subgroup.subset_closure ⟨m, E, B, hE, hB, rfl⟩

end ThompsonV
end NonsoficGroupsExist
