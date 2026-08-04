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

/-- Crossing stubs whose old endpoint belongs to one chosen block. -/
def blockStubs (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (C : Finset X.vertex) : Finset (KunRepairGraph.CrossingStub X P) :=
  Finset.univ.filter fun s ↦ KunRepairGraph.stubEndpoint X P s ∈ C

/-- Vertices of `C` incident to a crossing occurrence, presented as the image
of its block-side stubs. -/
def boundaryVertices (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (C : Finset X.vertex) : Finset X.vertex :=
  (blockStubs X P C).image (KunRepairGraph.stubEndpoint X P)

theorem boundaryVertices_subset
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (C : Finset X.vertex) : boundaryVertices X P C ⊆ C := by
  intro y hy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
  exact (Finset.mem_filter.mp hs).2

theorem card_boundaryVertices_le
    (X : FiniteMultiGraph) (P : BlockStructure X.vertex)
    (C : Finset X.vertex) :
    (boundaryVertices X P C).card ≤ (blockStubs X P C).card := by
  exact Finset.card_image_le

/-- Vertices excluded because a radius-`r` forward trajectory from them could
hit a block-boundary vertex. -/
noncomputable def blockForbidden
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (P : BlockStructure M) (C : Finset M) :
    Finset M :=
  backwardNeighborhood M τ S r
    (boundaryVertices (generatorGraph M S τ) P C)

theorem card_blockForbidden_le
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (P : BlockStructure M) (C : Finset M) :
    (blockForbidden M τ S r P C).card ≤
      (S.card + 1) ^ r *
        (blockStubs (generatorGraph M S τ) P C).card := by
  calc
    (blockForbidden M τ S r P C).card ≤
        (S.card + 1) ^ r *
          (boundaryVertices (generatorGraph M S τ) P C).card :=
      card_backwardNeighborhood_le M τ S r _
    _ ≤ (S.card + 1) ^ r *
        (blockStubs (generatorGraph M S τ) P C).card := by
      gcongr
      exact card_boundaryVertices_le (generatorGraph M S τ) P C

/-- The source of a generator occurrence leaving one block is one of that
block's formally enumerated boundary vertices. -/
theorem sourceBoundary_mem_boundaryVertices
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (y : M)
    {s : G} (hs : s ∈ S) {w : M}
    (hw : w ∈ P.block y) (hout : τ s w ∉ P.block y) :
    w ∈ boundaryVertices (generatorGraph M S τ) P (P.block y) := by
  classical
  have hmove : τ s w ≠ w := by
    intro hfix
    exact hout (by simpa [hfix] using hw)
  let t : S := ⟨s, hs⟩
  let e : (generatorGraph M S τ).edge :=
    ⟨(t, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmove⟩⟩
  have hwBlock : P.block w = P.block y := P.eq_of_mem y w hw
  have hblocks : P.block w ≠ P.block (τ s w) := by
    intro heq
    apply hout
    rw [← hwBlock, heq]
    exact P.self_mem _
  have heCrossing : e ∈ (generatorGraph M S τ).crossingEdges P.block := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [e, t] using hblocks⟩
  let stub : KunRepairGraph.CrossingStub (generatorGraph M S τ) P :=
    (⟨e, heCrossing⟩, KunRepairGraph.StubSide.first)
  apply Finset.mem_image.mpr
  refine ⟨stub, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [stub, KunRepairGraph.stubEndpoint, e, t] using hw⟩
  · simp [stub, KunRepairGraph.stubEndpoint, e]

/-- If a forward trajectory starts inside a block and reaches outside it,
some block-boundary vertex was reached no later than the same horizon. -/
theorem exists_boundaryVertex_of_mem_forwardNeighborhood_not_mem_block
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (y x : M)
    (hx : x ∈ P.block y) (r : ℕ) {z : M}
    (hz : z ∈ forwardNeighborhood M τ S r {x})
    (hzout : z ∉ P.block y) :
    ∃ b ∈ boundaryVertices (generatorGraph M S τ) P (P.block y),
      b ∈ forwardNeighborhood M τ S r {x} := by
  induction r generalizing z with
  | zero =>
      have hzx : z = x := by simpa [forwardNeighborhood] using hz
      subst z
      exact False.elim (hzout hx)
  | succ r ih =>
      change z ∈ forwardStep M τ S
        (forwardNeighborhood M τ S r {x}) at hz
      simp only [forwardStep, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_map] at hz
      rcases hz with hzPrev | ⟨s, hs, w, hw, hzw⟩
      · obtain ⟨b, hbBoundary, hbReach⟩ := ih hzPrev hzout
        exact ⟨b, hbBoundary,
          forwardNeighborhood_subset_succ M τ S r {x} hbReach⟩
      · subst z
        by_cases hwBlock : w ∈ P.block y
        · have hwBoundary := sourceBoundary_mem_boundaryVertices
            M τ S P y hs hwBlock hzout
          exact ⟨w, hwBoundary,
            forwardNeighborhood_subset_succ M τ S r {x} hw⟩
        · obtain ⟨b, hbBoundary, hbReach⟩ := ih hw hwBlock
          exact ⟨b, hbBoundary,
            forwardNeighborhood_subset_succ M τ S r {x} hbReach⟩

/-- Excluding the backward neighborhood of the block boundary forces the
whole forward marker neighborhood to remain in the block. -/
theorem forwardNeighborhood_subset_block_of_not_mem_forbidden
    {G : Type} [Group G] (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (P : BlockStructure M) (y x : M) (r : ℕ)
    (hxBlock : x ∈ P.block y)
    (hxForbidden : x ∉ blockForbidden M τ S r P (P.block y)) :
    forwardNeighborhood M τ S r {x} ⊆ P.block y := by
  intro z hz
  by_contra hzBlock
  obtain ⟨b, hbBoundary, hbReach⟩ :=
    exists_boundaryVertex_of_mem_forwardNeighborhood_not_mem_block
      M τ S P y x hxBlock r hz hzBlock
  obtain ⟨x', hx'singleton, hx'back⟩ :=
    exists_source_mem_backwardNeighborhood M τ S r {x} hbReach
  have hx'x : x' = x := by simpa using hx'singleton
  subst x'
  apply hxForbidden
  have hsingleton : ({b} : Finset M) ⊆
      boundaryVertices (generatorGraph M S τ) P (P.block y) := by
    simpa using hbBoundary
  exact backwardNeighborhood_mono M τ S r hsingleton hx'back

/-- A block whose stub density is below the explicit packing threshold has a
distinct separated marker for every one of its crossing stubs. -/
theorem exists_block_marker_assignment
    {G : Type} [Group G]
    (M : FiniteModel) (τ : G → Equiv.Perm M)
    (S : Finset G) (r : ℕ) (P : BlockStructure M) (C : Finset M)
    (hlarge :
      ((S.card + 1) ^ r + (S.card + 1) ^ (2 * r)) *
          (blockStubs (generatorGraph M S τ) P C).card < C.card) :
    ∃ marker :
        {s : KunRepairGraph.CrossingStub (generatorGraph M S τ) P //
          s ∈ blockStubs (generatorGraph M S τ) P C} → M,
      Function.Injective marker ∧
      (∀ s, marker s ∈ C \ blockForbidden M τ S r P C) ∧
      ∀ s t, s ≠ t →
        Disjoint (forwardNeighborhood M τ S r {marker s})
          (forwardNeighborhood M τ S r {marker t}) := by
  let I := {s : KunRepairGraph.CrossingStub (generatorGraph M S τ) P //
    s ∈ blockStubs (generatorGraph M S τ) P C}
  have hforbidden := card_blockForbidden_le M τ S r P C
  have hIcard : Fintype.card I =
      (blockStubs (generatorGraph M S τ) P C).card := Fintype.card_coe _
  have htotal :
      (blockForbidden M τ S r P C).card +
          Fintype.card I * (S.card + 1) ^ (2 * r) < C.card := by
    calc
      (blockForbidden M τ S r P C).card +
          Fintype.card I * (S.card + 1) ^ (2 * r) ≤
        (S.card + 1) ^ r *
            (blockStubs (generatorGraph M S τ) P C).card +
          (blockStubs (generatorGraph M S τ) P C).card *
            (S.card + 1) ^ (2 * r) := by
          rw [hIcard]
          exact Nat.add_le_add_right hforbidden _
      _ = ((S.card + 1) ^ r + (S.card + 1) ^ (2 * r)) *
          (blockStubs (generatorGraph M S τ) P C).card := by ring
      _ < C.card := hlarge
  exact exists_commonFuture_marker_assignment M τ S r C
    (blockForbidden M τ S r P C) htotal

end KunMarkerSelection
end NonsoficGroupsExist
