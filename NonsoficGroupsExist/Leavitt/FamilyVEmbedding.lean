import NonsoficGroupsExist.Leavitt.ThompsonVEmbedding

/-!
# The tree-table embedding over an arbitrary binary-family ring

Proposition `prop:vembed` of the manuscript: for every nontrivial unital ring
`A` carrying a binary Leavitt family, the assignment

  `U_g = ∑ α_i β_i^*`   (`eq:Ug`)

attached to a tree table of `g ∈ V` is independent of the table, multiplicative,
unital, and injective, hence an embedding `V ↪ Aˣ`.

The three parts are separated as follows.

*Well-definedness* is `LeavittFamily.tableSum_eq_of_mapsCylinder`: two complete
tables inducing the same prefix substitution have the same table element.  No
common refinement is constructed; instead both elements are expanded against the
other's partition of unity and compared summand by summand, the comparable pairs
matching because a table is determined on every refinement of its source leaves.

*Existence and multiplicativity* run through the canonical depth-`N` tables.
`ThompsonV.HasDepth f N` says that `f` acts as a prefix substitution on every
cylinder of depth `N`; these `f` form the subgroup `ThompsonV.tableGroup`
containing every tree table, and hence all of `V`.  The depth-`N` element
`LeavittFamily.depthSum` is independent of `N` by well-definedness, and the
product formula `LeavittFamily.tableSum_mul` computes `U_f U_g = U_{fg}` at a
common depth.

*Faithfulness* is the word calculus of Lemma `lem:leaf`: `LeavittFamily`
`.wordS_injective` shows that `s_α = s_β` forces `α = β` in every nontrivial
ring carrying a binary family, and multiplying `U_f = 1` by the depth-`N`
prefixes on the right returns exactly those equations.
-/

namespace NonsoficGroupsExist

namespace ThompsonV

/-! ### Prefixing a finite word -/

theorem prepend_getElem (w : List (Fin 2)) (x : Boundary) {n : ℕ}
    (hn : n < w.length) : prepend w x n = w[n] := by
  rw [prepend, dif_pos hn]

theorem prepend_of_length_le (w : List (Fin 2)) (x : Boundary) {n : ℕ}
    (hn : ¬ n < w.length) : prepend w x n = x (n - w.length) := by
  rw [prepend, dif_neg hn]

theorem prepend_append (a b : List (Fin 2)) (x : Boundary) :
    prepend (a ++ b) x = prepend a (prepend b x) := by
  funext n
  by_cases hn : n < a.length
  · have h1 : n < (a ++ b).length := by
      simp only [List.length_append]; omega
    rw [prepend_getElem _ _ h1, prepend_getElem _ _ hn]
    exact List.getElem_append_left hn
  · rw [prepend_of_length_le _ _ hn]
    by_cases hm : n - a.length < b.length
    · have h1 : n < (a ++ b).length := by
        simp only [List.length_append]; omega
      rw [prepend_getElem _ _ h1, prepend_getElem _ _ hm]
      exact List.getElem_append_right (by omega)
    · have h1 : ¬ n < (a ++ b).length := by
        simp only [List.length_append]; omega
      rw [prepend_of_length_le _ _ h1, prepend_of_length_le _ _ hm]
      congr 1
      simp only [List.length_append]
      omega

/-- A word is determined by the substitution it performs. -/
theorem prepend_injective_word {v w : List (Fin 2)}
    (h : ∀ x : Boundary, prepend v x = prepend w x) : v = w := by
  have key : ∀ v w : List (Fin 2),
      (∀ x : Boundary, prepend v x = prepend w x) → v.length ≤ w.length := by
    intro v w h
    by_contra hle
    have hlt : w.length < v.length := Nat.lt_of_not_le hle
    have h0 := congrFun (h fun _ ↦ 0) w.length
    have h1 := congrFun (h fun _ ↦ 1) w.length
    rw [prepend_getElem _ _ hlt, prepend_of_length_le _ _ (lt_irrefl _)] at h0 h1
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hlen : v.length = w.length :=
    le_antisymm (key v w h) (key w v fun x ↦ (h x).symm)
  apply List.ext_getElem hlen
  intro n h1 h2
  have := congrFun (h fun _ ↦ 0) n
  rwa [prepend_getElem _ _ h1, prepend_getElem _ _ h2] at this

/-- Every stream is its first `N` letters followed by its tail. -/
def firstWord (N : ℕ) (y : Boundary) : List (Fin 2) := List.ofFn fun i : Fin N ↦ y i

@[simp] theorem length_firstWord (N : ℕ) (y : Boundary) :
    (firstWord N y).length = N := by simp [firstWord]

theorem prepend_firstWord (N : ℕ) (y : Boundary) :
    prepend (firstWord N y) (drop N y) = y := by
  funext n
  by_cases hn : n < N
  · rw [prepend_getElem _ _ (by simpa using hn)]
    simp [firstWord]
  · rw [prepend_of_length_le _ _ (by simpa using hn), length_firstWord]
    show y (n - N + N) = y n
    congr 1
    omega

/-! ### Prefix substitutions of the boundary -/

/-- `f` carries the cylinder of `w` onto the cylinder of `v` by substituting the
prefix `w` by the prefix `v`. -/
def MapsCylinder (f : Equiv.Perm Boundary) (w v : List (Fin 2)) : Prop :=
  ∀ x : Boundary, f (prepend w x) = prepend v x

theorem MapsCylinder.unique {f : Equiv.Perm Boundary} {w v v' : List (Fin 2)}
    (h : MapsCylinder f w v) (h' : MapsCylinder f w v') : v = v' :=
  prepend_injective_word fun x ↦ (h x).symm.trans (h' x)

theorem MapsCylinder.append {f : Equiv.Perm Boundary} {w v : List (Fin 2)}
    (h : MapsCylinder f w v) (c : List (Fin 2)) :
    MapsCylinder f (w ++ c) (v ++ c) := by
  intro x
  rw [prepend_append, h, prepend_append]

theorem MapsCylinder.inv {f : Equiv.Perm Boundary} {w v : List (Fin 2)}
    (h : MapsCylinder f w v) : MapsCylinder f⁻¹ v w := by
  intro x
  conv_lhs => rw [← h x]
  simp

theorem MapsCylinder.comp {f g : Equiv.Perm Boundary} {u v z : List (Fin 2)}
    (hg : MapsCylinder g u v) (hf : MapsCylinder f v z) :
    MapsCylinder (f * g) u z := by
  intro x
  rw [Equiv.Perm.mul_apply, hg, hf]

@[simp] theorem mapsCylinder_one (w : List (Fin 2)) :
    MapsCylinder 1 w w := fun _ ↦ rfl

/-- `f` acts as a prefix substitution on every cylinder of depth `N`. -/
def HasDepth (f : Equiv.Perm Boundary) (N : ℕ) : Prop :=
  ∀ w : List (Fin 2), w.length = N → ∃ v, MapsCylinder f w v

/-- The identity has every depth: the satisfiability witness for `HasDepth`,
so the predicate is established and not only ever assumed. -/
theorem hasDepth_one (N : ℕ) : HasDepth 1 N :=
  fun w _ ↦ ⟨w, mapsCylinder_one w⟩

open Classical in
/-- The image word of a cylinder under a prefix substitution. -/
noncomputable def tgt (f : Equiv.Perm Boundary) (w : List (Fin 2)) :
    List (Fin 2) :=
  if h : ∃ v, MapsCylinder f w v then h.choose else []

theorem mapsCylinder_tgt {f : Equiv.Perm Boundary} {w : List (Fin 2)}
    (h : ∃ v, MapsCylinder f w v) : MapsCylinder f w (tgt f w) := by
  rw [tgt, dif_pos h]
  exact h.choose_spec

theorem tgt_eq {f : Equiv.Perm Boundary} {w v : List (Fin 2)}
    (h : MapsCylinder f w v) : tgt f w = v :=
  (mapsCylinder_tgt ⟨v, h⟩).unique h

/-- A depth-`N` table refines to a depth-`M` table for every `M ≥ N`. -/
theorem HasDepth.mono {f : Equiv.Perm Boundary} {N M : ℕ} (h : HasDepth f N)
    (hNM : N ≤ M) : HasDepth f M := by
  intro w hw
  obtain ⟨v, hv⟩ := h (w.take N) (by simp only [List.length_take, hw]; omega)
  refine ⟨v ++ w.drop N, ?_⟩
  have := hv.append (w.drop N)
  rwa [List.take_append_drop] at this

theorem HasDepth.mul {f g : Equiv.Perm Boundary} {N M : ℕ}
    (hf : HasDepth f N) (hg : HasDepth g M) : HasDepth (f * g) (M + N) := by
  intro u hu
  obtain ⟨v, hv⟩ := hg (u.take M) (by simp only [List.length_take, hu]; omega)
  have hgu : MapsCylinder g u (v ++ u.drop M) := by
    have := hv.append (u.drop M)
    rwa [List.take_append_drop] at this
  have hzlen : N ≤ (v ++ u.drop M).length := by
    simp only [List.length_append, List.length_drop, hu]
    omega
  obtain ⟨y, hy⟩ := hf ((v ++ u.drop M).take N)
    (by simp only [List.length_take]; omega)
  have hfz : MapsCylinder f (v ++ u.drop M) (y ++ (v ++ u.drop M).drop N) := by
    have := hy.append ((v ++ u.drop M).drop N)
    rwa [List.take_append_drop] at this
  exact ⟨_, hgu.comp hfz⟩

/-- Comparable prefixes of a common stream. -/
theorem prefix_of_prepend_eq {p q : List (Fin 2)} {a b : Boundary}
    (h : prepend p a = prepend q b) (hlen : p.length ≤ q.length) : p <+: q := by
  refine List.prefix_iff_getElem.mpr ⟨hlen, fun n hn ↦ ?_⟩
  have hc := congrFun h n
  rwa [prepend_getElem _ _ hn, prepend_getElem _ _ (lt_of_lt_of_le hn hlen)] at hc

theorem HasDepth.exists_inv {f : Equiv.Perm Boundary} {N : ℕ} (h : HasDepth f N) :
    ∃ M, HasDepth f⁻¹ M := by
  classical
  refine ⟨Finset.univ.sup fun p : Fin N → Fin 2 ↦ (tgt f (List.ofFn p)).length, ?_⟩
  intro u hu
  set x : Boundary := prepend u (fun _ ↦ 0) with hx
  set w : List (Fin 2) := firstWord N (f⁻¹ x) with hw
  have hwlen : w.length = N := length_firstWord N _
  have hmap : MapsCylinder f w (tgt f w) := mapsCylinder_tgt (h w hwlen)
  have hfx : prepend (tgt f w) (drop N (f⁻¹ x)) = x := by
    have hsplit : prepend w (drop N (f⁻¹ x)) = f⁻¹ x := by
      rw [hw]
      exact prepend_firstWord N (f⁻¹ x)
    have := hmap (drop N (f⁻¹ x))
    rw [hsplit] at this
    simpa using this.symm
  have hlen : (tgt f w).length ≤ u.length := by
    have hmem : (tgt f w).length ≤
        Finset.univ.sup fun p : Fin N → Fin 2 ↦ (tgt f (List.ofFn p)).length := by
      have hofFn : List.ofFn (fun i : Fin N ↦ (f⁻¹ x) i) = w := rfl
      exact Finset.le_sup (f := fun p : Fin N → Fin 2 ↦ (tgt f (List.ofFn p)).length)
        (Finset.mem_univ fun i : Fin N ↦ (f⁻¹ x) i)
    rw [hu]
    exact hmem
  have hpre : tgt f w <+: u :=
    prefix_of_prepend_eq (a := drop N (f⁻¹ x)) (b := fun _ ↦ 0) (by rw [hfx, hx]) hlen
  obtain ⟨c, hc⟩ := hpre
  refine ⟨w ++ c, ?_⟩
  have := hmap.inv.append c
  rwa [hc] at this

/-- The group of prefix-substitution homeomorphisms of the boundary. -/
def tableGroup : Subgroup (Equiv.Perm Boundary) where
  carrier := {f | ∃ N, HasDepth f N}
  one_mem' := ⟨0, fun w _ ↦ ⟨w, mapsCylinder_one w⟩⟩
  mul_mem' := by
    rintro a b ⟨N, hN⟩ ⟨M, hM⟩
    exact ⟨M + N, hN.mul hM⟩
  inv_mem' := by
    rintro a ⟨N, hN⟩
    exact hN.exists_inv

theorem mem_tableGroup {f : Equiv.Perm Boundary} :
    f ∈ tableGroup ↔ ∃ N, HasDepth f N := Iff.rfl

/-- A tree table acts as a prefix substitution on every cylinder deeper than all
of its source leaves. -/
theorem hasDepth_tableEquiv {m : ℕ} (E B : BinaryPrefixCode (Fin m))
    (hE : Covers E) (hB : Covers B) :
    ∃ N, HasDepth (tableEquiv E B hE hB) N := by
  classical
  refine ⟨Finset.univ.sup fun i : Fin m ↦ (E.word i).length, ?_⟩
  intro u hu
  obtain ⟨i, hi⟩ := hE (prepend u fun _ ↦ 0)
  have hlen : (E.word i).length ≤ u.length := by
    rw [hu]
    exact Finset.le_sup (f := fun i : Fin m ↦ (E.word i).length) (Finset.mem_univ i)
  have hpre : E.word i <+: u := by
    rcases prefix_or_prefix_of_isStreamPrefix hi
      (isStreamPrefix_prepend u fun _ ↦ 0) with hp | hp
    · exact hp
    · have : u = E.word i := hp.eq_of_length (le_antisymm hp.length_le hlen)
      rw [this]
  obtain ⟨c, hc⟩ := hpre
  refine ⟨B.word i ++ c, ?_⟩
  have hcyl : MapsCylinder (tableEquiv E B hE hB) (E.word i) (B.word i) :=
    fun x ↦ tableMap_prepend E B hE i x
  have := hcyl.append c
  rwa [hc] at this

theorem thompsonV_le_tableGroup : thompsonV ≤ tableGroup := by
  rw [thompsonV, Subgroup.closure_le]
  rintro f ⟨m, E, B, hE, hB, rfl⟩
  exact hasDepth_tableEquiv E B hE hB

end ThompsonV

/-! ### The complete code of all words of a fixed length -/

/-- Distinct words of the same length are incomparable. -/
theorem ofFn_not_prefix {N : ℕ} {p q : Fin N → Fin 2} (h : p ≠ q) :
    ¬ List.ofFn p <+: List.ofFn q := fun hp ↦
  h (List.ofFn_injective (hp.eq_of_length (by simp)))

/-- The prefix code of all binary words of length `N`. -/
def fullCode (N : ℕ) : BinaryPrefixCode (Fin N → Fin 2) where
  word p := List.ofFn p
  prefix_free _ _ h := ofFn_not_prefix h

@[simp] theorem fullCode_word {N : ℕ} (p : Fin N → Fin 2) :
    (fullCode N).word p = List.ofFn p := rfl

namespace LeavittFamily

open ThompsonV

variable {A : Type*} [Ring A] (L : LeavittFamily A)

/-! ### Table elements -/

/-- The table element `∑ α_i β_i^*` of equation `eq:Ug`, for an indexed pair of
source and target leaf families. -/
def tableSum {ι : Type*} [Fintype ι] (E B : ι → List (Fin 2)) : A :=
  ∑ i, L.wordS (B i) * L.wordT (E i)

/-- **Well-definedness of `U_g`**: two complete tables inducing the same prefix
substitution of the boundary have the same table element.  Comparable source
leaves contribute equal summands because a table already determines the image of
every refinement of a source leaf; incomparable ones contribute zero. -/
theorem tableSum_eq_of_mapsCylinder {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : Equiv.Perm Boundary) (E B : ι → List (Fin 2)) (E' B' : κ → List (Fin 2))
    (hE : ∑ i, L.wordS (E i) * L.wordT (E i) = 1)
    (hE' : ∑ j, L.wordS (E' j) * L.wordT (E' j) = 1)
    (hB : ∀ i, MapsCylinder f (E i) (B i))
    (hB' : ∀ j, MapsCylinder f (E' j) (B' j)) :
    L.tableSum E B = L.tableSum E' B' := by
  have hpair : ∀ (b e c : List (Fin 2)),
      (L.wordS b * L.wordT e) * (L.wordS (e ++ c) * L.wordT (e ++ c)) =
        L.wordS (b ++ c) * L.wordT (e ++ c) := by
    intro b e c
    calc (L.wordS b * L.wordT e) * (L.wordS (e ++ c) * L.wordT (e ++ c))
        = L.wordS b * (L.wordT e * L.wordS (e ++ c)) * L.wordT (e ++ c) := by
          noncomm_ring
      _ = L.wordS b * L.wordS c * L.wordT (e ++ c) := by
          rw [L.wordT_mul_wordS_append_left]
      _ = L.wordS (b ++ c) * L.wordT (e ++ c) := by rw [L.wordS_append]
  have hpair' : ∀ (b e c : List (Fin 2)),
      (L.wordS (b ++ c) * L.wordT (e ++ c)) * (L.wordS e * L.wordT e) =
        L.wordS (b ++ c) * L.wordT (e ++ c) := by
    intro b e c
    calc (L.wordS (b ++ c) * L.wordT (e ++ c)) * (L.wordS e * L.wordT e)
        = L.wordS (b ++ c) * (L.wordT (e ++ c) * L.wordS e) * L.wordT e := by
          noncomm_ring
      _ = L.wordS (b ++ c) * L.wordT c * L.wordT e := by
          rw [L.wordT_append_mul_wordS]
      _ = L.wordS (b ++ c) * L.wordT (e ++ c) := by
          rw [L.wordT_append, mul_assoc]
  have key : ∀ (i : ι) (j : κ),
      (L.wordS (B i) * L.wordT (E i)) * (L.wordS (E' j) * L.wordT (E' j)) =
        (L.wordS (B' j) * L.wordT (E' j)) * (L.wordS (E i) * L.wordT (E i)) := by
    intro i j
    by_cases h1 : E i <+: E' j
    · obtain ⟨c, hc⟩ := h1
      have hBc : B i ++ c = B' j := by
        refine MapsCylinder.unique ?_ (hB' j)
        rw [← hc]
        exact (hB i).append c
      rw [← hc, ← hBc, hpair, hpair']
    · by_cases h2 : E' j <+: E i
      · obtain ⟨c, hc⟩ := h2
        have hBc : B' j ++ c = B i := by
          refine MapsCylinder.unique ?_ (hB i)
          rw [← hc]
          exact (hB' j).append c
        rw [← hc, ← hBc, hpair, hpair']
      · have hz : L.wordT (E i) * L.wordS (E' j) = 0 :=
          L.wordT_mul_wordS_of_incomparable _ _ h1 h2
        have hz' : L.wordT (E' j) * L.wordS (E i) = 0 :=
          L.wordT_mul_wordS_of_incomparable _ _ h2 h1
        calc (L.wordS (B i) * L.wordT (E i)) * (L.wordS (E' j) * L.wordT (E' j))
            = L.wordS (B i) * (L.wordT (E i) * L.wordS (E' j)) *
                L.wordT (E' j) := by noncomm_ring
          _ = 0 := by rw [hz]; simp
          _ = L.wordS (B' j) * (L.wordT (E' j) * L.wordS (E i)) *
                L.wordT (E i) := by rw [hz']; simp
          _ = (L.wordS (B' j) * L.wordT (E' j)) *
                (L.wordS (E i) * L.wordT (E i)) := by noncomm_ring
  calc L.tableSum E B
      = ∑ i, ∑ j, (L.wordS (B i) * L.wordT (E i)) *
          (L.wordS (E' j) * L.wordT (E' j)) := by
        unfold tableSum
        rw [← Finset.sum_mul_sum, hE', mul_one]
    _ = ∑ i, ∑ j, (L.wordS (B' j) * L.wordT (E' j)) *
          (L.wordS (E i) * L.wordT (E i)) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ key i j
    _ = ∑ j, ∑ i, (L.wordS (B' j) * L.wordT (E' j)) *
          (L.wordS (E i) * L.wordT (E i)) := Finset.sum_comm
    _ = L.tableSum E' B' := by
        unfold tableSum
        rw [← Finset.sum_mul_sum, hE, mul_one]

/-- **Composition of tables**: if every target leaf of the second table refines a
source leaf of the first, the product of the two table elements is the table
element of the composite. -/
theorem tableSum_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E B : ι → List (Fin 2)) (E' B' : κ → List (Fin 2))
    (idx : κ → ι) (suf : κ → List (Fin 2))
    (hfree : ∀ i i', i ≠ i' → ¬ E i <+: E i')
    (hB' : ∀ j, B' j = E (idx j) ++ suf j) :
    L.tableSum E B * L.tableSum E' B' =
      L.tableSum E' (fun j ↦ B (idx j) ++ suf j) := by
  classical
  unfold tableSum
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_eq_single (idx j)]
  · rw [hB' j]
    calc (L.wordS (B (idx j)) * L.wordT (E (idx j))) *
          (L.wordS (E (idx j) ++ suf j) * L.wordT (E' j))
        = L.wordS (B (idx j)) *
            (L.wordT (E (idx j)) * L.wordS (E (idx j) ++ suf j)) *
              L.wordT (E' j) := by noncomm_ring
      _ = L.wordS (B (idx j)) * L.wordS (suf j) * L.wordT (E' j) := by
          rw [L.wordT_mul_wordS_append_left]
      _ = L.wordS (B (idx j) ++ suf j) * L.wordT (E' j) := by rw [L.wordS_append]
  · intro i _ hne
    rw [hB' j]
    have h1 : ¬ E i <+: E (idx j) ++ suf j := by
      have hnp := not_prefix_append_right (E i) (E (idx j)) [] (suf j)
        (hfree i (idx j) hne) (hfree (idx j) i (Ne.symm hne))
      simpa using hnp
    have h2 : ¬ (E (idx j) ++ suf j) <+: E i := fun hcon ↦
      hfree (idx j) i (Ne.symm hne) ((List.prefix_append _ _).trans hcon)
    calc (L.wordS (B i) * L.wordT (E i)) *
          (L.wordS (E (idx j) ++ suf j) * L.wordT (E' j))
        = L.wordS (B i) * (L.wordT (E i) * L.wordS (E (idx j) ++ suf j)) *
            L.wordT (E' j) := by noncomm_ring
      _ = 0 := by rw [L.wordT_mul_wordS_of_incomparable _ _ h1 h2]; simp
  · intro hnot
    exact absurd (Finset.mem_univ (idx j)) hnot

/-! ### The unit attached to a prefix substitution -/

/-- The table element of the canonical depth-`N` table of `f`. -/
noncomputable def depthSum (f : Equiv.Perm Boundary) (N : ℕ) : A :=
  L.tableSum (fun p : Fin N → Fin 2 ↦ List.ofFn p) fun p ↦ tgt f (List.ofFn p)

theorem sum_full_cylinder (N : ℕ) :
    ∑ p : Fin N → Fin 2, L.wordS (List.ofFn p) * L.wordT (List.ofFn p) = 1 := by
  simpa [cylinder] using L.sum_cylinder_ofFn N

/-- The depth-`N` table element does not depend on `N`. -/
theorem depthSum_eq {f : Equiv.Perm Boundary} {N M : ℕ}
    (hN : HasDepth f N) (hM : HasDepth f M) : L.depthSum f N = L.depthSum f M := by
  refine tableSum_eq_of_mapsCylinder L f _ _ _ _
    (L.sum_full_cylinder N) (L.sum_full_cylinder M) ?_ ?_
  · exact fun p ↦ mapsCylinder_tgt (hN _ (by simp))
  · exact fun p ↦ mapsCylinder_tgt (hM _ (by simp))

open Classical in
/-- The element `U_f` of equation `eq:Ug`, for any prefix substitution `f`. -/
noncomputable def tableVal (f : Equiv.Perm Boundary) : A :=
  if h : ∃ N, HasDepth f N then L.depthSum f (Nat.find h) else 1

theorem tableVal_eq {f : Equiv.Perm Boundary} {N : ℕ} (h : HasDepth f N) :
    L.tableVal f = L.depthSum f N := by
  classical
  have hex : ∃ N, HasDepth f N := ⟨N, h⟩
  rw [tableVal, dif_pos hex]
  exact depthSum_eq L (Nat.find_spec hex) h

theorem tableVal_one : L.tableVal (1 : Equiv.Perm Boundary) = 1 := by
  rw [tableVal_eq L (N := 0) fun w _ ↦ ⟨w, mapsCylinder_one w⟩]
  unfold depthSum tableSum
  refine Eq.trans (Finset.sum_congr rfl fun p _ ↦ ?_) (L.sum_full_cylinder 0)
  show L.wordS (tgt 1 (List.ofFn p)) * L.wordT (List.ofFn p) =
    L.wordS (List.ofFn p) * L.wordT (List.ofFn p)
  rw [tgt_eq (mapsCylinder_one (List.ofFn p))]

/-- A depth-`N` word of a stream, as a function on `Fin N`. -/
def wordFn (N : ℕ) (w : List (Fin 2)) : Fin N → Fin 2 :=
  fun i ↦ if h : i.val < w.length then w[i.val] else 0

theorem ofFn_wordFn {N : ℕ} {w : List (Fin 2)} (h : w.length = N) :
    List.ofFn (wordFn N w) = w := by
  refine List.ext_getElem (by simp [h]) fun n h1 h2 ↦ ?_
  simp [wordFn, h2]

theorem depthSum_mul {f g : Equiv.Perm Boundary} {N M : ℕ}
    (hf : HasDepth f N) (hg : HasDepth g M) :
    L.depthSum f N * L.depthSum g (M + N) = L.depthSum (f * g) (M + N) := by
  classical
  set D := M + N with hD
  -- every depth-`D` cylinder is carried by `g` to a cylinder of depth at least `N`
  have hgt : ∀ q : Fin D → Fin 2,
      MapsCylinder g (List.ofFn q) (tgt g (List.ofFn q)) := by
    intro q
    exact mapsCylinder_tgt (hg.mono (Nat.le_add_right M N) _ (by simp [hD]))
  have hlen : ∀ q : Fin D → Fin 2, N ≤ (tgt g (List.ofFn q)).length := by
    intro q
    obtain ⟨v, hv⟩ := hg ((List.ofFn q).take M)
      (by simp only [List.length_take, List.length_ofFn]; omega)
    have hcyl : MapsCylinder g (List.ofFn q) (v ++ (List.ofFn q).drop M) := by
      have := hv.append ((List.ofFn q).drop M)
      rwa [List.take_append_drop] at this
    rw [tgt_eq hcyl]
    simp only [List.length_append, List.length_drop, List.length_ofFn, hD]
    omega
  set idx : (Fin D → Fin 2) → (Fin N → Fin 2) :=
    fun q ↦ wordFn N ((tgt g (List.ofFn q)).take N) with hidx
  set suf : (Fin D → Fin 2) → List (Fin 2) :=
    fun q ↦ (tgt g (List.ofFn q)).drop N with hsuf
  have hofFn : ∀ q : Fin D → Fin 2,
      List.ofFn (idx q) = (tgt g (List.ofFn q)).take N := by
    intro q
    exact ofFn_wordFn (by have hq := hlen q; simp only [List.length_take]; omega)
  have hsplit : ∀ q : Fin D → Fin 2,
      tgt g (List.ofFn q) = List.ofFn (idx q) ++ suf q := by
    intro q
    rw [hofFn q]
    exact (List.take_append_drop N _).symm
  have hcomp : ∀ q : Fin D → Fin 2,
      tgt (f * g) (List.ofFn q) = tgt f (List.ofFn (idx q)) ++ suf q := by
    intro q
    refine tgt_eq (MapsCylinder.comp (v := List.ofFn (idx q) ++ suf q) ?_ ?_)
    · rw [← hsplit q]
      exact hgt q
    · exact (mapsCylinder_tgt (hf _ (by simp))).append (suf q)
  have hmul := L.tableSum_mul (fun p : Fin N → Fin 2 ↦ List.ofFn p)
    (fun p ↦ tgt f (List.ofFn p)) (fun q : Fin D → Fin 2 ↦ List.ofFn q)
    (fun q ↦ tgt g (List.ofFn q)) idx suf
    (fun i i' hne ↦ ofFn_not_prefix hne) hsplit
  rw [depthSum, depthSum, depthSum, hmul]
  unfold tableSum
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  show L.wordS (tgt f (List.ofFn (idx q)) ++ suf q) * L.wordT (List.ofFn q) =
    L.wordS (tgt (f * g) (List.ofFn q)) * L.wordT (List.ofFn q)
  rw [hcomp q]

theorem tableVal_mul {f g : Equiv.Perm Boundary}
    (hf : ∃ N, HasDepth f N) (hg : ∃ M, HasDepth g M) :
    L.tableVal f * L.tableVal g = L.tableVal (f * g) := by
  obtain ⟨N, hN⟩ := hf
  obtain ⟨M, hM⟩ := hg
  rw [tableVal_eq L hN, tableVal_eq L (hM.mono (Nat.le_add_right M N)),
    tableVal_eq L (hN.mul hM)]
  exact depthSum_mul L hN hM

/-! ### Faithfulness from the word calculus -/

/-- In a nontrivial ring carrying a binary Leavitt family the only word with
`s_γ = 1` is the empty one. -/
theorem wordS_eq_one [Nontrivial A] {γ : List (Fin 2)} (h : L.wordS γ = 1) :
    γ = [] := by
  cases γ with
  | nil => rfl
  | cons j γ' =>
      exfalso
      have hj : L.t (j + 1) * L.s j = 0 := by
        rw [L.t_mul_s]
        rw [if_neg]
        intro hcon
        exact absurd (congrArg Fin.val hcon) (by fin_cases j <;> decide)
      have hzero : L.t (j + 1) = 0 := by
        calc L.t (j + 1) = L.t (j + 1) * L.wordS (j :: γ') := by rw [h, mul_one]
          _ = (L.t (j + 1) * L.s j) * L.wordS γ' := by
              rw [wordS_cons, mul_assoc]
          _ = 0 := by rw [hj, zero_mul]
      have : (1 : A) = 0 := by
        calc (1 : A) = L.t (j + 1) * L.s (j + 1) := by rw [L.t_mul_s, if_pos rfl]
          _ = 0 := by rw [hzero, zero_mul]
      exact one_ne_zero this

/-- **Lemma `lem:leaf` as a faithfulness statement**: distinct binary words have
distinct prefixing operators in every nontrivial ring carrying a binary Leavitt
family. -/
theorem wordS_injective [Nontrivial A] {v w : List (Fin 2)}
    (h : L.wordS v = L.wordS w) : v = w := by
  by_cases h1 : v <+: w
  · obtain ⟨c, hc⟩ := h1
    have hone : L.wordS c = 1 := by
      calc L.wordS c = L.wordT v * L.wordS (v ++ c) :=
            (L.wordT_mul_wordS_append_left v c).symm
        _ = L.wordT v * L.wordS v := by rw [hc, ← h]
        _ = 1 := L.wordT_mul_wordS_self v
    rw [← hc, L.wordS_eq_one hone, List.append_nil]
  · by_cases h2 : w <+: v
    · obtain ⟨c, hc⟩ := h2
      have hone : L.wordS c = 1 := by
        calc L.wordS c = L.wordT w * L.wordS (w ++ c) :=
              (L.wordT_mul_wordS_append_left w c).symm
          _ = L.wordT w * L.wordS w := by rw [hc, h]
          _ = 1 := L.wordT_mul_wordS_self w
      rw [← hc, L.wordS_eq_one hone, List.append_nil]
    · exfalso
      have hzero : (1 : A) = 0 := by
        calc (1 : A) = L.wordT v * L.wordS v := (L.wordT_mul_wordS_self v).symm
          _ = L.wordT v * L.wordS w := by rw [h]
          _ = 0 := L.wordT_mul_wordS_of_incomparable _ _ h1 h2
      exact one_ne_zero hzero

/-- **Faithfulness**: a prefix substitution with trivial table element is the
identity. -/
theorem eq_one_of_tableVal_eq_one [Nontrivial A] {f : Equiv.Perm Boundary}
    {N : ℕ} (hN : HasDepth f N) (h1 : L.tableVal f = 1) : f = 1 := by
  classical
  have hsum : L.depthSum f N = 1 := by rw [← tableVal_eq L hN, h1]
  have hword : ∀ p : Fin N → Fin 2, tgt f (List.ofFn p) = List.ofFn p := by
    intro p
    have hmul := congrArg (fun z : A ↦ z * L.wordS (List.ofFn p)) hsum
    simp only [one_mul] at hmul
    rw [depthSum, tableSum, Finset.sum_mul] at hmul
    rw [Finset.sum_eq_single p] at hmul
    · refine L.wordS_injective ?_
      calc L.wordS (tgt f (List.ofFn p))
          = L.wordS (tgt f (List.ofFn p)) *
              (L.wordT (List.ofFn p) * L.wordS (List.ofFn p)) := by
            rw [L.wordT_mul_wordS_self, mul_one]
        _ = L.wordS (tgt f (List.ofFn p)) * L.wordT (List.ofFn p) *
              L.wordS (List.ofFn p) := by rw [mul_assoc]
        _ = L.wordS (List.ofFn p) := hmul
    · intro q _ hq
      have hz : L.wordT (List.ofFn q) * L.wordS (List.ofFn p) = 0 :=
        L.wordT_mul_wordS_of_incomparable _ _ (ofFn_not_prefix hq)
          (ofFn_not_prefix (Ne.symm hq))
      calc L.wordS (tgt f (List.ofFn q)) * L.wordT (List.ofFn q) *
            L.wordS (List.ofFn p)
          = L.wordS (tgt f (List.ofFn q)) *
              (L.wordT (List.ofFn q) * L.wordS (List.ofFn p)) := by rw [mul_assoc]
        _ = 0 := by rw [hz, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_univ p) hnot
  apply Equiv.ext
  intro y
  have hcyl : MapsCylinder f (firstWord N y) (firstWord N y) := by
    have hmap := mapsCylinder_tgt (hN (firstWord N y) (length_firstWord N y))
    have heq : tgt f (firstWord N y) = firstWord N y := hword fun i : Fin N ↦ y i
    rwa [heq] at hmap
  have hval := hcyl (drop N y)
  rw [prepend_firstWord] at hval
  simpa using hval

/-! ### The embedding -/

/-- The unit `U_f` attached to a prefix substitution of the boundary. -/
noncomputable def tableUnit (f : ThompsonV.tableGroup) : Aˣ where
  val := L.tableVal (f : Equiv.Perm Boundary)
  inv := L.tableVal ((f⁻¹ : ThompsonV.tableGroup) : Equiv.Perm Boundary)
  val_inv := by
    rw [tableVal_mul L f.2 (f⁻¹ : ThompsonV.tableGroup).2]
    rw [show (f : Equiv.Perm Boundary) *
      ((f⁻¹ : ThompsonV.tableGroup) : Equiv.Perm Boundary) = 1 from by
        rw [← Subgroup.coe_mul, mul_inv_cancel]; rfl]
    exact L.tableVal_one
  inv_val := by
    rw [tableVal_mul L (f⁻¹ : ThompsonV.tableGroup).2 f.2]
    rw [show ((f⁻¹ : ThompsonV.tableGroup) : Equiv.Perm Boundary) *
      (f : Equiv.Perm Boundary) = 1 from by
        rw [← Subgroup.coe_mul, inv_mul_cancel]; rfl]
    exact L.tableVal_one

/-- The table elements assemble into a homomorphism from the group of prefix
substitutions to the units of `A`. -/
noncomputable def tableUnitHom : ThompsonV.tableGroup →* Aˣ where
  toFun := L.tableUnit
  map_one' := by
    apply Units.ext
    show L.tableVal (1 : Equiv.Perm Boundary) = 1
    exact L.tableVal_one
  map_mul' := by
    intro f g
    apply Units.ext
    show L.tableVal ((f * g : ThompsonV.tableGroup) : Equiv.Perm Boundary) =
      L.tableVal (f : Equiv.Perm Boundary) * L.tableVal (g : Equiv.Perm Boundary)
    rw [tableVal_mul L f.2 g.2]
    rfl

/-- **Proposition `prop:vembed`**: Thompson's group `V` embeds into the unit
group of every nontrivial unital ring carrying a binary Leavitt family, by the
tree-table formula `eq:Ug`. -/
noncomputable def vEmbeddingOfFamily : thompsonV →* Aˣ :=
  L.tableUnitHom.comp (Subgroup.inclusion ThompsonV.thompsonV_le_tableGroup)

@[simp] theorem vEmbeddingOfFamily_apply_val (g : thompsonV) :
    ((L.vEmbeddingOfFamily g : Aˣ) : A) =
      L.tableVal (g : Equiv.Perm Boundary) := rfl

theorem vEmbeddingOfFamily_injective [Nontrivial A] :
    Function.Injective L.vEmbeddingOfFamily := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨N, hN⟩ := ThompsonV.thompsonV_le_tableGroup g.2
  have hval : L.tableVal (g : Equiv.Perm Boundary) = 1 := by
    have := congrArg (fun u : Aˣ ↦ (u : A)) hg
    simpa using this
  exact Subtype.ext (L.eq_one_of_tableVal_eq_one hN hval)

/-- The embedding is given by the tree-table formula `eq:Ug`: on the element of
`V` presented by the table `((β_i), (α_i))` it is `∑ α_i β_i^*`. -/
theorem vEmbeddingOfFamily_tableEquiv {m : ℕ} (E B : BinaryPrefixCode (Fin m))
    (hE : ThompsonV.Covers E) (hB : ThompsonV.Covers B) :
    ((L.vEmbeddingOfFamily ⟨ThompsonV.tableEquiv E B hE hB,
        ThompsonV.tableEquiv_mem_thompsonV E B hE hB⟩ : Aˣ) : A) =
      ∑ i, L.wordS (B.word i) * L.wordT (E.word i) := by
  obtain ⟨N, hN⟩ := ThompsonV.hasDepth_tableEquiv E B hE hB
  show L.tableVal (ThompsonV.tableEquiv E B hE hB) = _
  rw [tableVal_eq L hN, depthSum]
  refine tableSum_eq_of_mapsCylinder L (ThompsonV.tableEquiv E B hE hB) _ _
    E.word B.word (L.sum_full_cylinder N) ?_ ?_ ?_
  · have hcomplete := L.isComplete_of_covers E hE
    unfold IsComplete at hcomplete
    simpa [cylinder] using hcomplete
  · exact fun p ↦ mapsCylinder_tgt (hN _ (by simp))
  · exact fun i x ↦ ThompsonV.tableMap_prepend E B hE i x

end LeavittFamily

end NonsoficGroupsExist
