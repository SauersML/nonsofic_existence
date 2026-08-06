import NonsoficGroupsExist.Leavitt.ThompsonV
import NonsoficGroupsExist.Leavitt.LeavittSimplicity
import NonsoficGroupsExist.Leavitt.PrefixCode

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
theorem isComplete_of_covers {ι : Type*} [Fintype ι]
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


namespace BinaryLeavitt

open LeavittFamily

variable (k : Type) [Field k]

/-- The finitely supported stream module. -/
abbrev StreamModule := BinaryStream →₀ k

/-- Prefixing a bit, on finitely supported functions. -/
noncomputable def finPrefixOp (i : Fin 2) :
    Module.End k (StreamModule k) :=
  Finsupp.lsum k (fun x ↦ Finsupp.lsingle (prepend i x))

open Classical in
/-- Deleting a matching leading bit, on finitely supported functions. -/
noncomputable def finDeleteOp (i : Fin 2) :
    Module.End k (StreamModule k) :=
  Finsupp.lsum k
    (fun x ↦ if x 0 = i then Finsupp.lsingle (tail x) else 0)

@[simp] theorem finPrefixOp_single (i : Fin 2) (x : BinaryStream)
    (c : k) :
    finPrefixOp k i (Finsupp.single x c) =
      Finsupp.single (prepend i x) c := by
  simp [finPrefixOp]

open Classical in
theorem finDeleteOp_single (i : Fin 2) (x : BinaryStream) (c : k) :
    finDeleteOp k i (Finsupp.single x c) =
      if x 0 = i then Finsupp.single (tail x) c else 0 := by
  by_cases h : x 0 = i <;> simp [finDeleteOp, h]

/-- The binary Leavitt family on the finitely supported stream module. -/
noncomputable def finsuppStreamFamily :
    LeavittFamily (Module.End k (StreamModule k)) where
  s0 := finPrefixOp k 0
  s1 := finPrefixOp k 1
  t0 := finDeleteOp k 0
  t1 := finDeleteOp k 1
  t0_s0 := by
    refine Finsupp.lhom_ext fun x c ↦ ?_
    simp [Module.End.mul_apply, finDeleteOp_single]
  t0_s1 := by
    refine Finsupp.lhom_ext fun x c ↦ ?_
    simp [Module.End.mul_apply, finDeleteOp_single]
  t1_s0 := by
    refine Finsupp.lhom_ext fun x c ↦ ?_
    simp [Module.End.mul_apply, finDeleteOp_single]
  t1_s1 := by
    refine Finsupp.lhom_ext fun x c ↦ ?_
    simp [Module.End.mul_apply, finDeleteOp_single]
  sum_range := by
    refine Finsupp.lhom_ext fun x c ↦ ?_
    have hx : x 0 = 0 ∨ x 0 = 1 := by omega
    rcases hx with hx | hx
    · have hxx : prepend 0 (tail x) = x := by
        rw [← hx]
        exact prepend_head_tail x
      simp [Module.End.mul_apply, finDeleteOp_single, hx,
        LinearMap.add_apply, hxx]
    · have hxx : prepend 1 (tail x) = x := by
        rw [← hx]
        exact prepend_head_tail x
      simp [Module.End.mul_apply, finDeleteOp_single, hx,
        LinearMap.add_apply, hxx]

/-- The finitely supported stream representation. -/
noncomputable def finsuppStreamRep :
    BinaryLeavittAlgebra k →ₐ[k] Module.End k (StreamModule k) :=
  lift (finsuppStreamFamily k)

/-- **Faithfulness from simplicity**: any representation of the purely
infinite simple algebra `L_k(1,2)` with `1 ≠ 0` is injective. -/
theorem finsuppStreamRep_injective :
    Function.Injective (finsuppStreamRep k) := by
  intro x y hxy
  by_contra hne
  obtain ⟨a, b, hab⟩ :=
    exists_mul_mul_eq_one k (sub_ne_zero.mpr hne)
  have hz : finsuppStreamRep k (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have h1 := congrArg (finsuppStreamRep k) hab
  rw [map_one, map_mul, map_mul, hz, mul_zero, zero_mul] at h1
  have h2 := congrArg (fun T : Module.End k (StreamModule k) ↦
    T (Finsupp.single (fun _ ↦ 0) (1 : k))) h1
  simp only [LinearMap.zero_apply, Module.End.one_apply] at h2
  exact Finsupp.single_ne_zero.mpr one_ne_zero h2.symm


section Actions

open ThompsonV

variable (k : Type) [Field k]

@[simp] theorem finsuppStreamRep_s0 :
    finsuppStreamRep k (family k).s0 = finPrefixOp k 0 := by
  show finsuppStreamRep k (generator k BinaryLeavitt.s0) = _
  rw [finsuppStreamRep, lift_generator]
  rfl

@[simp] theorem finsuppStreamRep_s1 :
    finsuppStreamRep k (family k).s1 = finPrefixOp k 1 := by
  show finsuppStreamRep k (generator k BinaryLeavitt.s1) = _
  rw [finsuppStreamRep, lift_generator]
  rfl

@[simp] theorem finsuppStreamRep_t0 :
    finsuppStreamRep k (family k).t0 = finDeleteOp k 0 := by
  show finsuppStreamRep k (generator k BinaryLeavitt.t0) = _
  rw [finsuppStreamRep, lift_generator]
  rfl

@[simp] theorem finsuppStreamRep_t1 :
    finsuppStreamRep k (family k).t1 = finDeleteOp k 1 := by
  show finsuppStreamRep k (generator k BinaryLeavitt.t1) = _
  rw [finsuppStreamRep, lift_generator]
  rfl

theorem finsuppStreamRep_s (i : Fin 2) :
    finsuppStreamRep k ((family k).s i) = finPrefixOp k i := by
  fin_cases i
  · exact finsuppStreamRep_s0 k
  · exact finsuppStreamRep_s1 k

theorem finsuppStreamRep_t (i : Fin 2) :
    finsuppStreamRep k ((family k).t i) = finDeleteOp k i := by
  fin_cases i
  · exact finsuppStreamRep_t0 k
  · exact finsuppStreamRep_t1 k

theorem tvPrepend_nil (x : Boundary) : ThompsonV.prepend [] x = x := by
  funext n
  simp [ThompsonV.prepend]

theorem tvPrepend_cons (i : Fin 2) (a : List (Fin 2)) (x : Boundary) :
    ThompsonV.prepend (i :: a) x =
      BinaryLeavitt.prepend i (ThompsonV.prepend a x) := by
  funext n
  cases n with
  | zero =>
      simp [ThompsonV.prepend, BinaryLeavitt.prepend]
  | succ m =>
      show _ = ThompsonV.prepend a x m
      rw [ThompsonV.prepend, ThompsonV.prepend]
      by_cases hm : m < a.length
      · rw [dif_pos (show m + 1 < (i :: a).length by
          simp only [List.length_cons]
          omega), dif_pos hm]
        simp
      · rw [dif_neg (show ¬ m + 1 < (i :: a).length by
          simp only [List.length_cons]
          omega), dif_neg hm]
        congr 1
        simp only [List.length_cons]
        omega

theorem isStreamPrefix_nil (x : Boundary) : IsStreamPrefix [] x := by
  intro k h
  simp at h

theorem isStreamPrefix_cons_iff (i : Fin 2) (a : List (Fin 2))
    (x : Boundary) :
    IsStreamPrefix (i :: a) x ↔
      x 0 = i ∧ IsStreamPrefix a (BinaryLeavitt.tail x) := by
  constructor
  · intro h
    have h0 : x 0 = i := by
      have := h 0 (by simp)
      rwa [List.getElem_cons_zero] at this
    refine ⟨h0, fun m hm ↦ ?_⟩
    have hstep := h (m + 1) (by
      simp only [List.length_cons]
      omega)
    rwa [List.getElem_cons_succ] at hstep
  · rintro ⟨h0, h⟩
    intro m hm
    cases m with
    | zero =>
        rw [List.getElem_cons_zero]
        exact h0
    | succ n =>
        have hn : n < a.length := by
          simp only [List.length_cons] at hm
          omega
        rw [List.getElem_cons_succ]
        exact h n hn

theorem tvDrop_succ_length (a : List (Fin 2)) (x : Boundary) :
    ThompsonV.drop (a.length + 1) x =
      ThompsonV.drop a.length (BinaryLeavitt.tail x) := by
  funext n
  rfl

open Classical in
theorem finsuppStreamRep_wordS_single (a : List (Fin 2))
    (x : Boundary) (c : k) :
    finsuppStreamRep k ((family k).wordS a) (Finsupp.single x c) =
      Finsupp.single (ThompsonV.prepend a x) c := by
  induction a generalizing x with
  | nil =>
      rw [LeavittFamily.wordS_nil, map_one, tvPrepend_nil]
      rfl
  | cons i a ih =>
      rw [LeavittFamily.wordS_cons, map_mul, Module.End.mul_apply,
        ih, finsuppStreamRep_s, finPrefixOp_single, tvPrepend_cons]

open Classical in
theorem finsuppStreamRep_wordT_single (a : List (Fin 2))
    (x : Boundary) (c : k) :
    finsuppStreamRep k ((family k).wordT a) (Finsupp.single x c) =
      if IsStreamPrefix a x then
        Finsupp.single (ThompsonV.drop a.length x) c else 0 := by
  induction a generalizing x with
  | nil =>
      rw [LeavittFamily.wordT_nil, map_one]
      rw [if_pos (isStreamPrefix_nil x)]
      rfl
  | cons i a ih =>
      rw [LeavittFamily.wordT_cons, map_mul, Module.End.mul_apply,
        finsuppStreamRep_t, finDeleteOp_single]
      by_cases h0 : x 0 = i
      · rw [if_pos h0, ih]
        by_cases hpre : IsStreamPrefix a (BinaryLeavitt.tail x)
        · rw [if_pos hpre,
            if_pos ((isStreamPrefix_cons_iff i a x).2 ⟨h0, hpre⟩)]
          rw [List.length_cons, tvDrop_succ_length]
        · rw [if_neg hpre, if_neg (fun hcon ↦
            hpre ((isStreamPrefix_cons_iff i a x).1 hcon).2)]
      · rw [if_neg h0, map_zero, if_neg (fun hcon ↦
          h0 ((isStreamPrefix_cons_iff i a x).1 hcon).1)]

end Actions


section Embedding

open ThompsonV

variable (k : Type) [Field k]

private theorem tableSum_mul {m : ℕ}
    (B E D : BinaryPrefixCode (Fin m)) :
    (∑ i, (family k).wordS (B.word i) * (family k).wordT (E.word i)) *
      (∑ j, (family k).wordS (E.word j) * (family k).wordT (D.word j)) =
    ∑ i, (family k).wordS (B.word i) * (family k).wordT (D.word i) := by
  rw [Finset.sum_mul_sum]
  calc
    (∑ i, ∑ j,
        ((family k).wordS (B.word i) * (family k).wordT (E.word i)) *
          ((family k).wordS (E.word j) * (family k).wordT (D.word j))) =
        ∑ i, ∑ j, if i = j then
          (family k).wordS (B.word i) * (family k).wordT (D.word j)
          else 0 := by
      refine Finset.sum_congr rfl fun i _ ↦
        Finset.sum_congr rfl fun j _ ↦ ?_
      calc
        ((family k).wordS (B.word i) * (family k).wordT (E.word i)) *
            ((family k).wordS (E.word j) * (family k).wordT (D.word j)) =
            (family k).wordS (B.word i) *
              (((family k).wordT (E.word i) *
                (family k).wordS (E.word j)) *
                (family k).wordT (D.word j)) := by
          simp only [mul_assoc]
        _ = if i = j then
            (family k).wordS (B.word i) * (family k).wordT (D.word j)
            else 0 := by
          rw [LeavittFamily.prefixCode_orthogonal]
          by_cases h : i = j
          · rw [if_pos h, if_pos h, one_mul]
          · rw [if_neg h, if_neg h, zero_mul, mul_zero]
    _ = ∑ i, (family k).wordS (B.word i) * (family k).wordT (D.word i) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_ite_eq]
      rw [if_pos (Finset.mem_univ i)]

private theorem tableSum_complete {m : ℕ}
    (B : BinaryPrefixCode (Fin m)) (hB : Covers B) :
    (∑ i, (family k).wordS (B.word i) * (family k).wordT (B.word i)) =
      1 := by
  have h := (family k).isComplete_of_covers B hB
  unfold LeavittFamily.IsComplete at h
  simpa [LeavittFamily.cylinder] using h

/-- The Leavitt unit of a tree table. -/
noncomputable def tableUnit {m : ℕ} (E B : BinaryPrefixCode (Fin m))
    (hE : Covers E) (hB : Covers B) : (BinaryLeavittAlgebra k)ˣ where
  val := ∑ i, (family k).wordS (B.word i) * (family k).wordT (E.word i)
  inv := ∑ i, (family k).wordS (E.word i) * (family k).wordT (B.word i)
  val_inv := by
    rw [tableSum_mul k B E B]
    exact tableSum_complete k B hB
  inv_val := by
    rw [tableSum_mul k E B E]
    exact tableSum_complete k E hE

open Classical in
theorem finsuppStreamRep_tableUnit_single {m : ℕ}
    (E B : BinaryPrefixCode (Fin m)) (hE : Covers E) (hB : Covers B)
    (x : Boundary) (c : k) :
    finsuppStreamRep k ((tableUnit k E B hE hB : (BinaryLeavittAlgebra k)ˣ) :
        BinaryLeavittAlgebra k) (Finsupp.single x c) =
      Finsupp.single (tableMap E B hE x) c := by
  show finsuppStreamRep k
    (∑ i, (family k).wordS (B.word i) * (family k).wordT (E.word i))
    (Finsupp.single x c) = _
  rw [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_eq_single_of_mem (coveringIndex E hE x)
    (Finset.mem_univ _) (fun j _ hj ↦ by
      rw [map_mul, Module.End.mul_apply, finsuppStreamRep_wordT_single,
        if_neg (fun hcon ↦ hj
          (covering_index_unique E hcon (coveringIndex_spec E hE x))),
        map_zero])]
  rw [map_mul, Module.End.mul_apply, finsuppStreamRep_wordT_single,
    if_pos (coveringIndex_spec E hE x), finsuppStreamRep_wordS_single]
  rfl

open Classical in
/-- The units acting on the basis vectors as a permutation of the
boundary. -/
noncomputable def deltaPermUnits : Subgroup (BinaryLeavittAlgebra k)ˣ where
  carrier := {u | ∃ σ : Equiv.Perm Boundary, ∀ (x : Boundary) (c : k),
    finsuppStreamRep k (u : BinaryLeavittAlgebra k)
      (Finsupp.single x c) = Finsupp.single (σ x) c}
  one_mem' := ⟨1, fun x c ↦ by simp⟩
  mul_mem' := by
    rintro u v ⟨σ, hσ⟩ ⟨τ, hτ⟩
    refine ⟨σ * τ, fun x c ↦ ?_⟩
    rw [Units.val_mul, map_mul, Module.End.mul_apply, hτ, hσ]
    rfl
  inv_mem' := by
    rintro u ⟨σ, hσ⟩
    refine ⟨σ⁻¹, fun x c ↦ ?_⟩
    have h1 : finsuppStreamRep k (u : BinaryLeavittAlgebra k)
        (Finsupp.single (σ⁻¹ x) c) = Finsupp.single x c := by
      rw [hσ]
      simp
    calc
      finsuppStreamRep k ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
          BinaryLeavittAlgebra k) (Finsupp.single x c) =
          finsuppStreamRep k ((u⁻¹ : (BinaryLeavittAlgebra k)ˣ) :
            BinaryLeavittAlgebra k)
            (finsuppStreamRep k (u : BinaryLeavittAlgebra k)
              (Finsupp.single (σ⁻¹ x) c)) := by rw [h1]
      _ = Finsupp.single (σ⁻¹ x) c := by
        rw [← Module.End.mul_apply, ← map_mul, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, map_one, Module.End.one_apply]

open Classical in
theorem deltaPermUnits_sigma_unique {σ τ : Equiv.Perm Boundary}
    (hσ : ∀ (x : Boundary) (c : k), Finsupp.single (σ x) c =
      Finsupp.single (τ x) c) : σ = τ := by
  apply Equiv.ext
  intro x
  exact Finsupp.single_left_injective one_ne_zero (hσ x 1)

open Classical in
/-- The permutation realized by a basis-permuting unit. -/
noncomputable def toPerm : deltaPermUnits k →* Equiv.Perm Boundary where
  toFun u := u.property.choose
  map_one' := by
    apply deltaPermUnits_sigma_unique k
    intro x c
    rw [← (1 : deltaPermUnits k).property.choose_spec x c]
    simp
  map_mul' := by
    intro u v
    apply deltaPermUnits_sigma_unique k
    intro x c
    rw [← (u * v).property.choose_spec x c]
    rw [show ((u * v : deltaPermUnits k) : (BinaryLeavittAlgebra k)ˣ) =
      (u : (BinaryLeavittAlgebra k)ˣ) * v from rfl]
    rw [Units.val_mul, map_mul, Module.End.mul_apply,
      v.property.choose_spec, u.property.choose_spec]
    rfl

theorem toPerm_spec (u : deltaPermUnits k) (x : Boundary) (c : k) :
    finsuppStreamRep k ((u : (BinaryLeavittAlgebra k)ˣ) :
        BinaryLeavittAlgebra k) (Finsupp.single x c) =
      Finsupp.single (toPerm k u x) c :=
  u.property.choose_spec x c

theorem toPerm_injective : Function.Injective (toPerm k) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have hval : ((u : (BinaryLeavittAlgebra k)ˣ) :
      BinaryLeavittAlgebra k) = 1 := by
    apply finsuppStreamRep_injective k
    rw [map_one]
    refine Finsupp.lhom_ext fun x c ↦ ?_
    rw [toPerm_spec, hu]
    simp
  exact Subtype.ext (Units.ext hval)

theorem tableUnit_mem_deltaPermUnits {m : ℕ}
    (E B : BinaryPrefixCode (Fin m)) (hE : Covers E) (hB : Covers B) :
    tableUnit k E B hE hB ∈ deltaPermUnits k :=
  ⟨tableEquiv E B hE hB, fun x c ↦
    finsuppStreamRep_tableUnit_single k E B hE hB x c⟩

theorem toPerm_tableUnit {m : ℕ}
    (E B : BinaryPrefixCode (Fin m)) (hE : Covers E) (hB : Covers B) :
    toPerm k ⟨tableUnit k E B hE hB,
      tableUnit_mem_deltaPermUnits k E B hE hB⟩ =
      tableEquiv E B hE hB := by
  apply deltaPermUnits_sigma_unique k
  intro x c
  rw [← toPerm_spec]
  exact finsuppStreamRep_tableUnit_single k E B hE hB x c

theorem thompsonV_le_toPerm_range :
    thompsonV ≤ (toPerm k).range := by
  rw [thompsonV]
  rw [Subgroup.closure_le]
  rintro f ⟨m, E, B, hE, hB, rfl⟩
  exact ⟨⟨tableUnit k E B hE hB,
    tableUnit_mem_deltaPermUnits k E B hE hB⟩,
    toPerm_tableUnit k E B hE hB⟩

/-- **Proposition `prop:vembed`, embedding half** (checkpoint `D2`):
Thompson's group `V` embeds into the unit group of `L_k(1,2)`, with the
tree tables acting on the basis of the faithful stream module exactly by
their prefix substitutions. -/
noncomputable def vEmbedding : thompsonV →* (BinaryLeavittAlgebra k)ˣ :=
  (deltaPermUnits k).subtype.comp
    ((MulEquiv.symm (MonoidHom.ofInjective
      (toPerm_injective k))).toMonoidHom.comp
      (Subgroup.inclusion (thompsonV_le_toPerm_range k)))

theorem vEmbedding_injective : Function.Injective (vEmbedding k) := by
  intro g h hgh
  have h2 : (MulEquiv.symm (MonoidHom.ofInjective (toPerm_injective k)))
      (Subgroup.inclusion (thompsonV_le_toPerm_range k) g) =
    (MulEquiv.symm (MonoidHom.ofInjective (toPerm_injective k)))
      (Subgroup.inclusion (thompsonV_le_toPerm_range k) h) :=
    Subtype.val_injective hgh
  have h3 := (MulEquiv.symm (MonoidHom.ofInjective
    (toPerm_injective k))).injective h2
  exact Subgroup.inclusion_injective _ h3

end Embedding

end BinaryLeavitt



end NonsoficGroupsExist
