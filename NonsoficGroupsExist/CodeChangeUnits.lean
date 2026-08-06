import NonsoficGroupsExist.CodeChangeSwap

/-!
# Code-change units lie in the diagonal class group

The generation theorem for the Higman–Thompson groupoid: for any two
complete prefix codes of equal size, the code-change unit
`Ω = Σᵢ s_{dᵢ} t_{cᵢ}` lies in the diagonal class group.  Induction
on the size: extract a source sibling pair, align the target pairing
by at most two honest transpositions (compiled certificates), merge
the sibling terms through the completeness relation, and recurse.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- Complete codes are duplicate-free. -/
theorem IsCompleteCode.nodup {c : List (List (Fin 2))}
    (hc : L.IsCompleteCode c) : c.Nodup := by
  refine hc.pairwise_incomp.imp ?_
  intro a b h heq
  exact h.1 (heq ▸ List.prefix_refl a)

/-- Completeness transports along permutations. -/
theorem IsCompleteCode.perm {c c' : List (List (Fin 2))}
    (hc : L.IsCompleteCode c) (h : c.Perm c') :
    L.IsCompleteCode c' := by
  refine ⟨?_, ?_⟩
    -- `Perm.pairwise_iff` wants `∀ {x y}, R x y → R y x` (implicit binders);
    -- `Symmetric` is both deprecated and strict-implicit (`∀ ⦃x y⦄`), so it
    -- does not match.  Pass the symmetry witness inline.
  · exact (h.pairwise_iff (fun hab ↦ ⟨hab.2, hab.1⟩)).mp hc.pairwise_incomp
  · rw [← (h.map (fun w ↦ L.cylinder w)).sum_eq]
    exact hc.complete

/-- `swapWord x x` is the identity. -/
theorem swapWord_self (x w : List (Fin 2)) : swapWord x x w = w := by
  unfold swapWord
  -- With `y := x` both branches test the same condition `w = x`, so
  -- `split_ifs` yields two goals, not three.
  split_ifs with h1
  · rw [h1]
  · rfl

theorem swapWord_left (x y : List (Fin 2)) : swapWord x y x = y := by
  unfold swapWord
  rw [if_pos rfl]

theorem swapWord_right {x y : List (Fin 2)} (hxy : x ≠ y) :
    swapWord x y y = x := by
  unfold swapWord
  rw [if_neg (Ne.symm hxy), if_pos rfl]

theorem swapWord_other {x y w : List (Fin 2)} (hwx : w ≠ x)
    (hwy : w ≠ y) : swapWord x y w = w := by
  unfold swapWord
  rw [if_neg hwx, if_neg hwy]

/-- Swapping two present values of a duplicate-free list permutes
it. -/
theorem map_swapWord_perm {l : List (List (Fin 2))}
    (hnd : l.Nodup) {x y : List (Fin 2)} (hx : x ∈ l) (hy : y ∈ l) :
    (l.map (swapWord x y)).Perm l := by
  classical
  rcases eq_or_ne x y with rfl | hxy
  · rw [show l.map (swapWord x x) = l.map id from
      List.map_congr_left fun w _ ↦ swapWord_self x w, List.map_id]
  · have hyx : y ∈ l.erase x :=
      (List.mem_erase_of_ne (Ne.symm hxy)).mpr hy
    have h1 : l.Perm (x :: l.erase x) := List.perm_cons_erase hx
    have h2 : (l.erase x).Perm (y :: (l.erase x).erase y) :=
      List.perm_cons_erase hyx
    set l' : List (List (Fin 2)) := (l.erase x).erase y with hl'
    have hperm : l.Perm (x :: y :: l') :=
      h1.trans (List.Perm.cons x h2)
    have hxl' : x ∉ l' := by
      intro hmem
      exact hnd.not_mem_erase (List.mem_of_mem_erase hmem)
    have hyl' : y ∉ l' := by
      intro hmem
      exact (hnd.erase x).not_mem_erase hmem
    have hmap : (x :: y :: l').map (swapWord x y) =
        y :: x :: l' := by
      rw [List.map_cons, List.map_cons, swapWord_left,
        swapWord_right hxy,
        show l'.map (swapWord x y) = l' from by
          rw [show l'.map (swapWord x y) = l'.map id from
            List.map_congr_left fun w hw ↦ swapWord_other
              (fun h ↦ hxl' (h ▸ hw)) (fun h ↦ hyl' (h ▸ hw)),
            List.map_id]]
    have hchain : (l.map (swapWord x y)).Perm (y :: x :: l') := by
      rw [← hmap]
      exact hperm.map _
    exact hchain.trans ((List.Perm.swap x y l').trans hperm.symm)

/-- A word whose cylinder is the identity is empty. -/
theorem eq_nil_of_cylinder_eq_one [Nontrivial A]
    {w : List (Fin 2)} (h : L.cylinder w = 1) : w = [] := by
  cases w with
  | nil => rfl
  | cons i rest =>
      exfalso
      set j : Fin 2 := if i = 0 then 1 else 0 with hj
      have hij : i ≠ j := by
        rw [hj]
        fin_cases i <;> decide
      have hinc₁ : ¬(i :: rest) <+: [j] := by
        intro hp
        rw [List.cons_prefix_cons] at hp
        exact hij hp.1
      have hinc₂ : ¬[j] <+: (i :: rest) := by
        intro hp
        rw [List.cons_prefix_cons] at hp
        exact hij hp.1.symm
      have hzero : L.wordS [j] = 0 := by
        have h1 : L.cylinder (i :: rest) * L.wordS [j] =
            L.wordS [j] := by
          rw [h, one_mul]
        rw [cylinder, mul_assoc,
          L.wordT_mul_wordS_of_incomparable _ _ hinc₁ hinc₂,
          mul_zero] at h1
        exact h1.symm
      exact L.wordS_ne_zero [j] hzero

/-- The alignment step: the identity when the words agree, the honest
transposition otherwise. -/
noncomputable def alignStep (x y : List (Fin 2))
    (h : x = y ∨ (¬x <+: y ∧ ¬y <+: x)) : Aˣ :=
  if hxy : x = y then 1 else
    L.cylTransposition (h.resolve_left hxy).1 (h.resolve_left hxy).2

-- `k` is named only in the proof (`cylTransposition_mem (k := k)`), so it
-- is not auto-included from the `variable` block.
include k in
theorem alignStep_mem [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (x y : List (Fin 2)) (h : x = y ∨ (¬x <+: y ∧ ¬y <+: x)) :
    L.alignStep x y h ∈ stableUnits A := by
  unfold alignStep
  split_ifs with hxy
  · exact one_mem _
  · exact L.cylTransposition_mem (k := k) hdiv _ _

theorem alignStep_mul_pairValue (x y : List (Fin 2))
    (h : x = y ∨ (¬x <+: y ∧ ¬y <+: x))
    (P : List (List (Fin 2) × List (Fin 2)))
    (hP : ∀ p ∈ P,
      (p.1 = x ∨ (¬p.1 <+: x ∧ ¬x <+: p.1)) ∧
      (p.1 = y ∨ (¬p.1 <+: y ∧ ¬y <+: p.1))) :
    ((L.alignStep x y h : Aˣ) : A) * L.pairValue P =
      L.pairValue (P.map (fun p ↦ (swapWord x y p.1, p.2))) := by
  unfold alignStep
  split_ifs with hxy
  · subst hxy
    rw [show P.map (fun p ↦ (swapWord x x p.1, p.2)) = P.map id from
      List.map_congr_left fun p _ ↦ by
        rw [swapWord_self]; rfl, List.map_id]
    show (1 : A) * _ = _
    rw [one_mul]
  · exact L.cylTransposition_mul_pairValue _ _ P hP

/-- Merging a sibling pair at the head of a complete code keeps it
complete. -/
theorem IsCompleteCode.merge {w : List (Fin 2)}
    {r : List (List (Fin 2))}
    (hc : L.IsCompleteCode ((w ++ [0]) :: (w ++ [1]) :: r)) :
    L.IsCompleteCode (w :: r) := by
  have hpair := hc.pairwise_incomp
  rw [List.pairwise_cons] at hpair
  obtain ⟨h0, hpair1⟩ := hpair
  rw [List.pairwise_cons] at hpair1
  obtain ⟨h1, hrest⟩ := hpair1
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_cons]
    refine ⟨?_, hrest⟩
    intro q hq
    constructor
    · rintro ⟨e, rfl⟩
      cases e with
      | nil =>
          rw [List.append_nil] at hq
          refine (h0 w (List.mem_cons_of_mem _ hq)).2 ?_
          exact ⟨[0], rfl⟩
      | cons a e' =>
          have hsib : (w ++ [a]) <+: (w ++ a :: e') :=
            ⟨e', by rw [List.append_assoc]; rfl⟩
          fin_cases a
          · exact (h0 (w ++ 0 :: e')
              (List.mem_cons_of_mem _ hq)).1 hsib
          · exact (h1 (w ++ 1 :: e') hq).1 hsib
    · intro hpre
      refine (h0 q (List.mem_cons_of_mem _ hq)).2 ?_
      exact hpre.trans ⟨[0], rfl⟩
  · have hmerge : L.cylinder (w ++ [0]) + L.cylinder (w ++ [1]) =
        L.cylinder w := by
      show L.wordS (w ++ [0]) * L.wordT (w ++ [0]) +
        L.wordS (w ++ [1]) * L.wordT (w ++ [1]) =
        L.wordS w * L.wordT w
      exact L.merge_identity_one w w
    have hsum := hc.complete
    rw [List.map_cons, List.map_cons, List.sum_cons,
      List.sum_cons] at hsum
    rw [List.map_cons, List.sum_cons, ← hmerge, add_assoc]
    exact hsum

-- `k` is named only in the proof (`alignStep_mem (k := k)`), never in the
-- statement, so it needs pulling in explicitly.  `include ... in` has to
-- precede the docstring, or the doc comment is orphaned from its theorem.
include k in
/-- **Code-change units lie in the diagonal class group.** -/
theorem codeChange_mem_stableUnits [Nontrivial A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) :
    ∀ (n : ℕ) (P : List (List (Fin 2) × List (Fin 2))),
      P.length = n →
      L.IsCompleteCode (P.map Prod.snd) →
      L.IsCompleteCode (P.map Prod.fst) →
      ∀ u : Aˣ, (u : A) = L.pairValue P →
      u ∈ stableUnits A := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro P hlen hsrc htgt u hu
  match n, hlen with
  | 0, hlen =>
      exfalso
      rw [List.length_eq_zero_iff] at hlen
      subst hlen
      have := hsrc.complete
      simp only [List.map_nil, List.sum_nil] at this
      exact zero_ne_one this
  | 1, hlen =>
      obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hlen
      have hs := hsrc.complete
      have ht := htgt.complete
      simp only [List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero] at hs ht
      have hs2 : p.2 = [] := L.eq_nil_of_cylinder_eq_one hs
      have ht2 : p.1 = [] := L.eq_nil_of_cylinder_eq_one ht
      have hval : (u : A) = 1 := by
        rw [hu, pairValue_cons, pairValue_nil, add_zero, hs2, ht2]
        simp [wordS, wordT]
      have hone : u = 1 := Units.ext hval
      rw [hone]
      exact one_mem _
  | (m + 2), hlen =>
      -- source sibling pair
      obtain ⟨w, hw0, hw1⟩ := L.exists_sibling_pair hsrc (by
        rw [List.length_map, hlen]
        omega)
      obtain ⟨p₀, hp₀mem, hp₀⟩ := List.mem_map.mp hw0
      obtain ⟨p₁, hp₁mem, hp₁⟩ := List.mem_map.mp hw1
      have hp₀₁ : p₀ ≠ p₁ := by
        intro h
        rw [h, hp₁] at hp₀
        simp at hp₀
      -- extract the pair to the head
      have hp₁e : p₁ ∈ P.erase p₀ :=
        (List.mem_erase_of_ne hp₀₁.symm).mpr hp₁mem
      set Q : List (List (Fin 2) × List (Fin 2)) :=
        (P.erase p₀).erase p₁ with hQ
      have hperm : P.Perm (p₀ :: p₁ :: Q) :=
        (List.perm_cons_erase hp₀mem).trans
          (List.Perm.cons p₀ (List.perm_cons_erase hp₁e))
      have hQlen : Q.length = m := by
        have := hperm.length_eq
        rw [hlen] at this
        simp only [List.length_cons] at this
        omega
      -- transported data
      -- `L` is an explicit argument of `perm` and sits *before* the
      -- `IsCompleteCode` one, so dot notation would feed the permutation
      -- into `L`'s slot.  Name the argument instead.
      have hsrc' : L.IsCompleteCode ((p₀ :: p₁ :: Q).map Prod.snd) :=
        hsrc.perm (L := L) (hperm.map _)
      have htgt' : L.IsCompleteCode ((p₀ :: p₁ :: Q).map Prod.fst) :=
        htgt.perm (L := L) (hperm.map _)
      have hu' : (u : A) = L.pairValue (p₀ :: p₁ :: Q) := by
        rw [hu]
        exact L.pairValue_perm hperm
      -- target sibling pair
      obtain ⟨v, hv0, hv1⟩ := L.exists_sibling_pair htgt' (by
        simp only [List.length_map, List.length_cons]
        omega)
      set x : List (Fin 2) := p₀.1 with hx
      set y : List (Fin 2) := p₁.1 with hy
      set T : List (List (Fin 2)) := (p₀ :: p₁ :: Q).map Prod.fst
        with hT
      have hxT : x ∈ T := by
        rw [hT]
        exact List.mem_map.mpr ⟨p₀, List.mem_cons_self, rfl⟩
      have hyT : y ∈ T := by
        rw [hT]
        exact List.mem_map.mpr ⟨p₁,
          List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
      have hTnodup : T.Nodup := htgt'.nodup
      -- equal-or-incomparable helper for the target code
      have hcode : ∀ a ∈ T, ∀ b ∈ T,
          a = b ∨ (¬a <+: b ∧ ¬b <+: a) := by
        intro a ha b hb
        rcases eq_or_ne a b with rfl | hab
        · exact Or.inl rfl
        · exact Or.inr (htgt'.incomp (L := L) ha hb hab)
      -- first alignment: send x to v0
      have hxv0 := hcode x hxT (v ++ [0]) hv0
      set A₁ : Aˣ := L.alignStep x (v ++ [0]) hxv0 with hA₁
      have hA₁act : ((A₁ : Aˣ) : A) * L.pairValue (p₀ :: p₁ :: Q) =
          L.pairValue ((p₀ :: p₁ :: Q).map
            (fun p ↦ (swapWord x (v ++ [0]) p.1, p.2))) := by
        rw [hA₁]
        refine L.alignStep_mul_pairValue _ _ _ _ ?_
        intro p hp
        have hpT : p.1 ∈ T := by
          rw [hT]
          exact List.mem_map.mpr ⟨p, hp, rfl⟩
        exact ⟨hcode p.1 hpT x hxT, hcode p.1 hpT (v ++ [0]) hv0⟩
      set f₁ : List (Fin 2) → List (Fin 2) :=
        swapWord x (v ++ [0]) with hf₁
      set P₁ : List (List (Fin 2) × List (Fin 2)) :=
        (p₀ :: p₁ :: Q).map (fun p ↦ (f₁ p.1, p.2)) with hP₁
      -- P₁-targets permute T
      have hP₁tgtEq : P₁.map Prod.fst =
          T.map (swapWord x (v ++ [0])) := by
        rw [hP₁, hT, List.map_map, List.map_map]
        rfl
      have hP₁perm : (P₁.map Prod.fst).Perm T := by
        rw [hP₁tgtEq]
        exact map_swapWord_perm hTnodup hxT hv0
      have htgt₁ : L.IsCompleteCode (P₁.map Prod.fst) :=
        htgt'.perm (L := L) hP₁perm.symm
      -- basic distinctness facts
      have hxy : x ≠ y := by
        have h := hTnodup
        rw [hT, List.map_cons, List.map_cons, List.nodup_cons] at h
        -- `▸` cannot place the cast here; state the membership goal up
        -- front (defeq folds `p₀.1`/`p₁.1` back to `x`/`y`) and rewrite.
        intro heq
        apply h.1
        show x ∈ y :: (Q.map Prod.fst)
        rw [heq]
        exact List.mem_cons_self
      have hv01 : (v ++ [0] : List (Fin 2)) ≠ v ++ [1] := by
        intro h
        simp at h
      -- the second head target after the first swap
      set y₁ : List (Fin 2) := swapWord x (v ++ [0]) y with hy₁
      have hv0y₁ : (v ++ [0] : List (Fin 2)) ≠ y₁ := by
        rw [hy₁]
        by_cases hxv : x = v ++ [0]
        · rw [hxv, swapWord_self]
          intro h
          rw [← hxv] at h
          exact hxy h
        · by_cases hyv : y = v ++ [0]
          · rw [hyv, swapWord_right hxv]
            intro h
            exact hxv h.symm
          · rw [swapWord_other (fun h ↦ hxy h.symm) hyv]
            intro h
            exact hyv h.symm
      -- memberships in the new target code
      have hy₁P₁ : y₁ ∈ P₁.map Prod.fst := by
        rw [hP₁tgtEq]
        refine List.mem_map.mpr ⟨y, hyT, ?_⟩
        rw [hy₁]
      have hv1P₁ : (v ++ [1]) ∈ P₁.map Prod.fst :=
        (hP₁perm.mem_iff).mpr hv1
      have hv0P₁ : (v ++ [0]) ∈ P₁.map Prod.fst :=
        (hP₁perm.mem_iff).mpr hv0
      have hcode₁ : ∀ a ∈ P₁.map Prod.fst, ∀ b ∈ P₁.map Prod.fst,
          a = b ∨ (¬a <+: b ∧ ¬b <+: a) := by
        intro a ha b hb
        rcases eq_or_ne a b with rfl | hab
        · exact Or.inl rfl
        · exact Or.inr (htgt₁.incomp (L := L) ha hb hab)
      -- second alignment: send y₁ to v1
      have hyv1 := hcode₁ y₁ hy₁P₁ (v ++ [1]) hv1P₁
      set A₂ : Aˣ := L.alignStep y₁ (v ++ [1]) hyv1 with hA₂
      have hA₂act : ((A₂ : Aˣ) : A) * L.pairValue P₁ =
          L.pairValue (P₁.map
            (fun p ↦ (swapWord y₁ (v ++ [1]) p.1, p.2))) := by
        rw [hA₂]
        refine L.alignStep_mul_pairValue _ _ _ _ ?_
        intro p hp
        have hpT : p.1 ∈ P₁.map Prod.fst :=
          List.mem_map.mpr ⟨p, hp, rfl⟩
        exact ⟨hcode₁ p.1 hpT y₁ hy₁P₁,
          hcode₁ p.1 hpT (v ++ [1]) hv1P₁⟩
      set P₂ : List (List (Fin 2) × List (Fin 2)) :=
        P₁.map (fun p ↦ (swapWord y₁ (v ++ [1]) p.1, p.2)) with hP₂
      -- P₂-targets permute T
      have hP₂tgtEq : P₂.map Prod.fst =
          (P₁.map Prod.fst).map (swapWord y₁ (v ++ [1])) := by
        rw [hP₂, List.map_map, List.map_map]
        rfl
      have hP₂perm : (P₂.map Prod.fst).Perm (P₁.map Prod.fst) := by
        rw [hP₂tgtEq]
        exact map_swapWord_perm (hP₁perm.nodup_iff.mpr hTnodup)
          hy₁P₁ hv1P₁
      -- explicit head structure of P₂
      have hP₂struct : P₂ =
          (v ++ [0], w ++ [0]) :: (v ++ [1], w ++ [1]) ::
            (Q.map (fun p ↦
              (swapWord y₁ (v ++ [1]) (swapWord x (v ++ [0]) p.1),
                p.2))) := by
        rw [hP₂, hP₁, List.map_cons, List.map_cons, List.map_cons,
          List.map_cons, List.map_map]
        have h1 : swapWord y₁ (v ++ [1])
            (swapWord x (v ++ [0]) p₀.1) = v ++ [0] := by
          rw [← hx, swapWord_left, swapWord_other hv0y₁.symm hv01]
        have h2 : swapWord y₁ (v ++ [1])
            (swapWord x (v ++ [0]) p₁.1) = v ++ [1] := by
          rw [← hy, ← hy₁, swapWord_left]
        rw [h1, h2, hp₀, hp₁]
        rfl
      -- merge the sibling pair
      have hmergeval : L.pairValue P₂ = L.pairValue
          ((v, w) :: Q.map (fun p ↦
            (swapWord y₁ (v ++ [1]) (swapWord x (v ++ [0]) p.1),
              p.2))) := by
        rw [hP₂struct, pairValue_cons, pairValue_cons, pairValue_cons,
          ← add_assoc, L.merge_identity_one v w]
      set Q₂ : List (List (Fin 2) × List (Fin 2)) :=
        Q.map (fun p ↦
          (swapWord y₁ (v ++ [1]) (swapWord x (v ++ [0]) p.1), p.2))
        with hQ₂
      -- source code of the merged list
      have hsrcQ₂ : Q₂.map Prod.snd = Q.map Prod.snd := by
        rw [hQ₂, List.map_map]
        rfl
      have hsrcmerged : L.IsCompleteCode
          ((w :: (Q₂.map Prod.snd))) := by
        rw [hsrcQ₂]
        refine IsCompleteCode.merge (L := L) ?_
        have h1 : (p₀ :: p₁ :: Q).map Prod.snd =
            (w ++ [0]) :: (w ++ [1]) :: Q.map Prod.snd := by
          rw [List.map_cons, List.map_cons, hp₀, hp₁]
        rw [← h1]
        exact hsrc'
      -- target code of the merged list
      have htgtmerged : L.IsCompleteCode (v :: (Q₂.map Prod.fst)) := by
        refine IsCompleteCode.merge (L := L) ?_
        have h1 : P₂.map Prod.fst =
            (v ++ [0]) :: (v ++ [1]) :: Q₂.map Prod.fst := by
          rw [hP₂struct, List.map_cons, List.map_cons, hQ₂]
        rw [← h1]
        exact htgt₁.perm (L := L) hP₂perm.symm
      -- run the induction hypothesis on the merged list
      set u₂ : Aˣ := A₂ * (A₁ * u) with hu₂
      have hu₂val : (u₂ : A) = L.pairValue ((v, w) :: Q₂) := by
        rw [hu₂]
        show ((A₂ : Aˣ) : A) * (((A₁ : Aˣ) : A) * (u : A)) = _
        rw [hu', hA₁act, ← hP₁, hA₂act, ← hP₂, hmergeval, hQ₂]
      have hQ₂len : ((v, w) :: Q₂).length = m + 1 := by
        rw [List.length_cons, hQ₂, List.length_map, hQlen]
      have hu₂mem : u₂ ∈ stableUnits A := by
        refine ihn (m + 1) (by omega) ((v, w) :: Q₂) hQ₂len ?_ ?_
          u₂ hu₂val
        · rw [List.map_cons]
          exact hsrcmerged
        · rw [List.map_cons]
          exact htgtmerged
      -- unwind the alignment units
      have hA₁mem : A₁ ∈ stableUnits A := by
        rw [hA₁]
        exact L.alignStep_mem (k := k) hdiv _ _ _
      have hA₂mem : A₂ ∈ stableUnits A := by
        rw [hA₂]
        exact L.alignStep_mem (k := k) hdiv _ _ _
      have hassemble : u = A₁⁻¹ * (A₂⁻¹ * u₂) := by
        rw [hu₂]
        group
      rw [hassemble]
      exact mul_mem (inv_mem hA₁mem)
        (mul_mem (inv_mem hA₂mem) hu₂mem)

end LeavittFamily
end NonsoficGroupsExist
