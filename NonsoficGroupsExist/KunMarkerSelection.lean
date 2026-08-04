import NonsoficGroupsExist.KunRepairGraph

/-!
# Finite separated-marker selection

Kun's repair needs many marker vertices whose fixed-radius conflict
neighborhoods do not overlap.  The paper leaves their existence to a smallness
choice.  Here it is a finite maximum-cardinality packing argument with an
explicit cardinal hypothesis.
-/

namespace NonsoficGroupsExist
namespace KunMarkerSelection

open KunSupport

/-- No two distinct selected vertices lie in one another's conflict
neighborhood. -/
def IsSeparated {V : Type} [DecidableEq V]
    (N : V → Finset V) (M : Finset V) : Prop :=
  ∀ ⦃x⦄, x ∈ M → ∀ ⦃y⦄, y ∈ M → x ≠ y → y ∉ N x

theorem isSeparated_empty {V : Type} [DecidableEq V]
    (N : V → Finset V) : IsSeparated N ∅ := by
  simp [IsSeparated]

/-- A maximum-cardinality separated subset of `C \ F` exists. -/
theorem exists_maximalSeparated
    {V : Type} [Fintype V] [DecidableEq V]
    (C F : Finset V) (N : V → Finset V) :
    ∃ M : Finset V,
      M ⊆ C \ F ∧ IsSeparated N M ∧
        ∀ U : Finset V, U ⊆ C \ F → IsSeparated N U → U.card ≤ M.card := by
  classical
  let candidates := (C \ F).powerset.filter (IsSeparated N)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, isSeparated_empty]
  let sizes := candidates.image Finset.card
  have hsizes : sizes.Nonempty := hcandidates.image Finset.card
  let m := sizes.max' hsizes
  have hm : m ∈ sizes := Finset.max'_mem sizes hsizes
  obtain ⟨M, hMcandidate, hMcard⟩ := Finset.mem_image.mp hm
  have hMdata := Finset.mem_filter.mp hMcandidate
  refine ⟨M, Finset.mem_powerset.mp hMdata.1, hMdata.2, fun U hU hUsep ↦ ?_⟩
  have hUcandidate : U ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hU, hUsep⟩
  have hUsize : U.card ∈ sizes :=
    Finset.mem_image.mpr ⟨U, hUcandidate, rfl⟩
  rw [hMcard]
  exact Finset.le_max' sizes U.card hUsize

/-- Maximality makes the forbidden set together with the selected conflict
neighborhoods cover the entire candidate block. -/
theorem subset_forbidden_union_biUnion_of_maximal
    {V : Type} [Fintype V] [DecidableEq V]
    (C F M : Finset V) (N : V → Finset V)
    (hself : ∀ x, x ∈ N x)
    (hsymm : ∀ x y, y ∈ N x ↔ x ∈ N y)
    (hMC : M ⊆ C \ F) (hMsep : IsSeparated N M)
    (hmax : ∀ U : Finset V, U ⊆ C \ F → IsSeparated N U →
      U.card ≤ M.card) :
    C ⊆ F ∪ M.biUnion N := by
  classical
  intro y hyC
  by_cases hyF : y ∈ F
  · exact Finset.mem_union_left _ hyF
  apply Finset.mem_union_right
  by_contra hycover
  have hyN (x : V) (hx : x ∈ M) : y ∉ N x := by
    intro hy
    exact hycover (Finset.mem_biUnion.mpr ⟨x, hx, hy⟩)
  have hyM : y ∉ M := by
    intro hy
    exact hyN y hy (hself y)
  have hinsertSubset : insert y M ⊆ C \ F := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with rfl | hz
    · exact Finset.mem_sdiff.mpr ⟨hyC, hyF⟩
    · exact hMC hz
  have hinsertSeparated : IsSeparated N (insert y M) := by
    intro x hx z hz hxz
    rw [Finset.mem_insert] at hx hz
    rcases hx with rfl | hx <;> rcases hz with rfl | hz
    · exact False.elim (hxz rfl)
    · intro hzNx
      exact hyN z hz ((hsymm x z).mp hzNx)
    · exact hyN x hx
    · exact hMsep hx hz hxz
  have hcard := hmax (insert y M) hinsertSubset hinsertSeparated
  rw [Finset.card_insert_of_notMem hyM] at hcard
  omega

/-- A uniform bound on conflict-neighborhood size converts the covering lemma
into an explicit lower bound for a separated packing. -/
theorem exists_separated_of_card
    {V : Type} [Fintype V] [DecidableEq V]
    (C F : Finset V) (N : V → Finset V) (R m : ℕ)
    (hself : ∀ x, x ∈ N x)
    (hsymm : ∀ x y, y ∈ N x ↔ x ∈ N y)
    (hNcard : ∀ x, (N x).card ≤ R)
    (hlarge : F.card + m * R < C.card) :
    ∃ M : Finset V, M ⊆ C \ F ∧ IsSeparated N M ∧ m ≤ M.card := by
  classical
  obtain ⟨M, hMC, hMsep, hmax⟩ := exists_maximalSeparated C F N
  refine ⟨M, hMC, hMsep, ?_⟩
  by_contra hm
  have hmle : M.card ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hm)
  have hcover := subset_forbidden_union_biUnion_of_maximal
    C F M N hself hsymm hMC hMsep hmax
  have hbiUnion : (M.biUnion N).card ≤ M.card * R := by
    calc
      (M.biUnion N).card ≤ ∑ x ∈ M, (N x).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ M, R := Finset.sum_le_sum fun x _ ↦ hNcard x
      _ = M.card * R := by simp
  have hCcard : C.card ≤ F.card + M.card * R := by
    calc
      C.card ≤ (F ∪ M.biUnion N).card := Finset.card_le_card hcover
      _ ≤ F.card + (M.biUnion N).card := Finset.card_union_le _ _
      _ ≤ F.card + M.card * R := Nat.add_le_add_left hbiUnion _
  have hmul : M.card * R ≤ m * R := Nat.mul_le_mul_right R hmle
  omega

/-- Assign a distinct separated marker to every element of a finite index
type.  This is the form consumed by crossing stubs. -/
theorem exists_marker_assignment
    {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    (C F : Finset V) (N : V → Finset V) (R : ℕ)
    (hself : ∀ x, x ∈ N x)
    (hsymm : ∀ x y, y ∈ N x ↔ x ∈ N y)
    (hNcard : ∀ x, (N x).card ≤ R)
    (hlarge : F.card + Fintype.card I * R < C.card) :
    ∃ marker : I → V,
      Function.Injective marker ∧
      (∀ i, marker i ∈ C \ F) ∧
      ∀ i j, i ≠ j → marker j ∉ N (marker i) := by
  classical
  obtain ⟨M, hMC, hMsep, hMcard⟩ :=
    exists_separated_of_card C F N R (Fintype.card I)
      hself hsymm hNcard hlarge
  have hcard : Fintype.card I ≤ Fintype.card {x : V // x ∈ M} := by
    simpa [Fintype.card_coe] using hMcard
  let emb : I → {x : V // x ∈ M} := fun i ↦
    (Fintype.equivFin {x : V // x ∈ M}).symm
      (Fin.castLE hcard (Fintype.equivFin I i))
  have hemb : Function.Injective emb := by
    intro i j hij
    have hfin : Fin.castLE hcard (Fintype.equivFin I i) =
        Fin.castLE hcard (Fintype.equivFin I j) :=
      (Fintype.equivFin {x : V // x ∈ M}).symm.injective hij
    apply (Fintype.equivFin I).injective
    apply Fin.ext
    have hval := congrArg
      (fun x : Fin (Fintype.card {x : V // x ∈ M}) ↦ x.val) hfin
    exact hval
  let marker : I → V := fun i ↦ (emb i).1
  refine ⟨marker, ?_, ?_, ?_⟩
  · intro i j hij
    exact hemb (Subtype.ext hij)
  · intro i
    exact hMC (emb i).2
  · intro i j hij
    apply hMsep (emb i).2 (emb j).2
    intro heq
    exact hij (hemb (Subtype.ext heq))

/-- Vertices whose radius-`r` forward neighborhoods meet.  This relation is
manifestly symmetric, and its neighborhood size has the same
backward-forward bound used in the finite removal argument. -/
noncomputable def commonFutureNeighborhood
    {G : Type} (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (x : M) : Finset M :=
  Finset.univ.filter fun y ↦
    ∃ z,
      z ∈ forwardNeighborhood M τ S r {x} ∧
      z ∈ forwardNeighborhood M τ S r {y}

theorem mem_commonFutureNeighborhood
    {G : Type} (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (x y : M) :
    y ∈ commonFutureNeighborhood M τ S r x ↔
      ∃ z,
        z ∈ forwardNeighborhood M τ S r {x} ∧
        z ∈ forwardNeighborhood M τ S r {y} := by
  classical
  simp [commonFutureNeighborhood]

theorem self_mem_commonFutureNeighborhood
    {G : Type} (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (x : M) :
    x ∈ commonFutureNeighborhood M τ S r x := by
  rw [mem_commonFutureNeighborhood]
  exact ⟨x,
    forwardNeighborhood_mono_time M τ S (Nat.zero_le r) {x}
      (by simp [forwardNeighborhood]),
    forwardNeighborhood_mono_time M τ S (Nat.zero_le r) {x}
      (by simp [forwardNeighborhood])⟩

theorem commonFutureNeighborhood_symmetric
    {G : Type} (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (x y : M) :
    y ∈ commonFutureNeighborhood M τ S r x ↔
      x ∈ commonFutureNeighborhood M τ S r y := by
  rw [mem_commonFutureNeighborhood, mem_commonFutureNeighborhood]
  constructor <;> rintro ⟨z, hz₁, hz₂⟩
  · exact ⟨z, hz₂, hz₁⟩
  · exact ⟨z, hz₂, hz₁⟩

theorem commonFutureNeighborhood_subset_backwardForward
    {G : Type} (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (x : M) :
    commonFutureNeighborhood M τ S r x ⊆
      backwardNeighborhood M τ S r
        (forwardNeighborhood M τ S r {x}) := by
  intro y hy
  obtain ⟨z, hzx, hzy⟩ :=
    (mem_commonFutureNeighborhood M τ S r x y).mp hy
  obtain ⟨y', hy'singleton, hy'back⟩ :=
    exists_source_mem_backwardNeighborhood M τ S r {y} hzy
  have hy'y : y' = y := by simpa using hy'singleton
  subst y'
  have hsingleton : ({z} : Finset M) ⊆
      forwardNeighborhood M τ S r {x} := by simpa using hzx
  exact backwardNeighborhood_mono M τ S r hsingleton hy'back

theorem card_commonFutureNeighborhood_le
    {G : Type} (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (x : M) :
    (commonFutureNeighborhood M τ S r x).card ≤
      (S.card + 1) ^ (2 * r) := by
  calc
    (commonFutureNeighborhood M τ S r x).card ≤
        (backwardNeighborhood M τ S r
          (forwardNeighborhood M τ S r {x})).card :=
      Finset.card_le_card
        (commonFutureNeighborhood_subset_backwardForward M τ S r x)
    _ ≤ (S.card + 1) ^ (2 * r) * ({x} : Finset M).card :=
      card_backwardForwardNeighborhood_le M τ S r {x}
    _ = (S.card + 1) ^ (2 * r) := by simp

/-- Explicit separated markers for the common-future conflict relation. -/
theorem exists_commonFuture_marker_assignment
    {G I : Type} [Fintype I]
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (C F : Finset M)
    (hlarge : F.card + Fintype.card I * (S.card + 1) ^ (2 * r) < C.card) :
    ∃ marker : I → M,
      Function.Injective marker ∧
      (∀ i, marker i ∈ C \ F) ∧
      ∀ i j, i ≠ j →
        Disjoint (forwardNeighborhood M τ S r {marker i})
          (forwardNeighborhood M τ S r {marker j}) := by
  obtain ⟨marker, hinjective, hmarker, hseparated⟩ :=
    exists_marker_assignment C F
      (commonFutureNeighborhood M τ S r) ((S.card + 1) ^ (2 * r))
      (self_mem_commonFutureNeighborhood M τ S r)
      (commonFutureNeighborhood_symmetric M τ S r)
      (card_commonFutureNeighborhood_le M τ S r) hlarge
  refine ⟨marker, hinjective, hmarker, fun i j hij ↦ ?_⟩
  rw [Finset.disjoint_left]
  intro z hzi hzj
  exact hseparated i j hij
    ((mem_commonFutureNeighborhood M τ S r (marker i) (marker j)).2
      ⟨z, hzi, hzj⟩)

end KunMarkerSelection
end NonsoficGroupsExist
