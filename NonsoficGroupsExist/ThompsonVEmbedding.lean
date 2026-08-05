import NonsoficGroupsExist.ThompsonV
import NonsoficGroupsExist.LeavittSimplicity
import NonsoficGroupsExist.PrefixCode

/-!
# Covering codes are complete

A binary prefix code that covers the boundary is complete in every ring
carrying a binary Leavitt family: extending each code word to a common
depth `N` enumerates the depth-`N` words exactly once, so the cylinder
sum telescopes to the depth-`N` partition of unity.  This is the bridge
between the combinatorial tree tables of Thompson's group `V` and the
Leavitt tree-table units (first half of checkpoint `D2`).
-/

namespace NonsoficGroupsExist

namespace LeavittFamily

variable {A : Type*} [Ring A] (L : LeavittFamily A)

private theorem ofFn_cons_eq (r : ℕ) (i : Fin 2) (f : Fin r → Fin 2) :
    List.ofFn (Fin.cons i f : Fin (r + 1) → Fin 2) = i :: List.ofFn f := by
  simp [List.ofFn_succ]

/-- Every cylinder splits into its depth-`r` refinements. -/
theorem cylinder_eq_sum_extensions (w : List (Fin 2)) (r : ℕ) :
    L.cylinder w =
      ∑ f : Fin r → Fin 2, L.cylinder (w ++ List.ofFn f) := by
  induction r generalizing w with
  | zero =>
      simp
  | succ r ih =>
      rw [cylinder_split]
      rw [ih (w ++ [0]), ih (w ++ [1])]
      calc
        (∑ f : Fin r → Fin 2, L.cylinder ((w ++ [0]) ++ List.ofFn f)) +
            ∑ f : Fin r → Fin 2, L.cylinder ((w ++ [1]) ++ List.ofFn f) =
            ∑ p : Fin 2 × (Fin r → Fin 2),
              L.cylinder (w ++ List.ofFn
                (Fin.cons p.1 p.2 : Fin (r + 1) → Fin 2)) := by
          rw [Fintype.sum_prod_type, Fin.sum_univ_two]
          congr 1 <;>
            exact Finset.sum_congr rfl fun f _ ↦ by
              rw [List.append_assoc, ofFn_cons_eq]
              simp
        _ = ∑ g : Fin (r + 1) → Fin 2, L.cylinder (w ++ List.ofFn g) :=
          Fintype.sum_equiv (Fin.consEquiv (fun _ ↦ Fin 2))
            (fun p ↦ L.cylinder (w ++ List.ofFn
              (Fin.cons p.1 p.2 : Fin (r + 1) → Fin 2)))
            (fun g ↦ L.cylinder (w ++ List.ofFn g))
            (fun p ↦ rfl)

open Classical in
/-- **Covering codes are complete**: a prefix code covering the boundary
has cylinder sum `1` in every ring carrying a binary Leavitt family. -/
theorem isComplete_of_covers {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : BinaryPrefixCode ι) (hE : ThompsonV.Covers E) :
    L.IsComplete E := by
  unfold IsComplete
  set N := Finset.univ.sup (fun i : ι ↦ (E.word i).length) with hN
  have hlen : ∀ i : ι, (E.word i).length ≤ N := fun i ↦
    Finset.le_sup (f := fun i : ι ↦ (E.word i).length)
      (Finset.mem_univ i)
  -- extension sets at depth N
  set ext : ι → Finset (List (Fin 2)) := fun i ↦
    (Finset.univ : Finset (Fin (N - (E.word i).length) → Fin 2)).image
      (fun f ↦ E.word i ++ List.ofFn f) with hext
  have hsum_ext : ∀ i : ι,
      L.cylinder (E.word i) = ∑ l ∈ ext i, L.cylinder l := by
    intro i
    rw [hext]
    beta_reduce
    rw [Finset.sum_image (fun f _ g _ h ↦ by
      have := List.append_cancel_left h
      exact List.ofFn_injective this)]
    exact cylinder_eq_sum_extensions L (E.word i) _
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint ext := by
    intro i _ j _ hij
    refine Finset.disjoint_left.2 fun l hli hlj ↦ ?_
    rw [hext] at hli hlj
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.1 hli
    obtain ⟨g, -, hg⟩ := Finset.mem_image.1 hlj
    have hpre : E.word j <+: E.word i ++ List.ofFn f :=
      ⟨List.ofFn g, hg⟩
    rcases List.prefix_or_prefix_of_prefix hpre
      (List.prefix_append (E.word i) (List.ofFn f)) with h | h
    · exact E.prefix_free (Ne.symm hij) h
    · exact E.prefix_free hij h
  have hcover : Finset.univ.biUnion ext =
      (Finset.univ : Finset (Fin N → Fin 2)).image List.ofFn := by
    ext l
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
      true_and, hext]
    constructor
    · rintro ⟨i, f, rfl⟩
      refine ⟨fun n ↦ (E.word i ++ List.ofFn f)[n]'(by
        simp only [List.length_append, List.length_ofFn]
        have := hlen i
        omega), ?_⟩
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_append]
        have := hlen i
        omega
      · intro n h1 h2
        simp
    · rintro ⟨g, rfl⟩
      set x : ThompsonV.Boundary :=
        ThompsonV.prepend (List.ofFn g) (fun _ ↦ 0) with hx
      obtain ⟨i, hi⟩ := hE x
      have hgpre : ThompsonV.IsStreamPrefix (List.ofFn g) x :=
        ThompsonV.isStreamPrefix_prepend _ _
      have hilen : (E.word i).length ≤ (List.ofFn g).length := by
        rw [List.length_ofFn]
        exact hlen i
      have hpre : E.word i <+: List.ofFn g := by
        rcases ThompsonV.prefix_or_prefix_of_isStreamPrefix hi hgpre
          with h | h
        · exact h
        · have heq : List.ofFn g = E.word i :=
            List.IsPrefix.eq_of_length h
              (le_antisymm h.length_le hilen)
          rw [heq]
      obtain ⟨e, he⟩ := hpre
      have helen : e.length = N - (E.word i).length := by
        have := congrArg List.length he
        simp only [List.length_append, List.length_ofFn] at this
        omega
      set ef : Fin (N - (E.word i).length) → Fin 2 :=
        fun m ↦ e[m]'(by omega) with hef
      refine ⟨i, ef, ?_⟩
      have hofe : List.ofFn ef = e := by
        apply List.ext_getElem
        · simp [helen]
        · intro n h1 h2
          simp [hef]
      rw [hofe]
      exact he
  calc
    (∑ i, L.cylinder (E.word i)) =
        ∑ i, ∑ l ∈ ext i, L.cylinder l :=
      Finset.sum_congr rfl fun i _ ↦ hsum_ext i
    _ = ∑ l ∈ Finset.univ.biUnion ext, L.cylinder l :=
      (Finset.sum_biUnion hdisj).symm
    _ = ∑ l ∈ (Finset.univ : Finset (Fin N → Fin 2)).image List.ofFn,
        L.cylinder l := by rw [hcover]
    _ = ∑ g : Fin N → Fin 2, L.cylinder (List.ofFn g) :=
      Finset.sum_image fun f _ g _ h ↦ List.ofFn_injective h
    _ = 1 := L.sum_cylinder_ofFn N

end LeavittFamily

end NonsoficGroupsExist
