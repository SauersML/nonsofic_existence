import Mathlib.Data.ZMod.Basic
import NonsoficGroupsExist.A2MagicHilbert
import NonsoficGroupsExist.AlmostAutomorphism
import NonsoficGroupsExist.FiniteClassTwoOrthogonality
import NonsoficGroupsExist.FreeRootCharacterValuation
import NonsoficGroupsExist.HilbertEpsilonOrthogonality
import NonsoficGroupsExist.KazhdanControl
import NonsoficGroupsExist.KazhdanFiniteModel
import NonsoficGroupsExist.KazhdanImprovement
import NonsoficGroupsExist.KunSpectralCounterexample
import NonsoficGroupsExist.MaximalCutRepair
import NonsoficGroupsExist.SoficPositiveControl
import NonsoficGroupsExist.TableCover
import NonsoficGroupsExist.UniversalLeavitt

/-!
# Semantic positive controls

Closed examples for proposition and structure interfaces used by the negative
argument.  These declarations are deliberately independent of the headline
nonsoficity proof: they show that the interfaces describe actual mathematics,
instead of being satisfied only under relocated hypotheses.
-/

namespace NonsoficGroupsExist

private abbrev C2 := Multiplicative (ZMod 2)

private abbrev pairedCarrier (n : ℕ) :=
  C2 × Multiplicative (ZMod (n + 1))

private abbrev pairedModel (n : ℕ) : FiniteModel :=
  regularModel (pairedCarrier n)

private def pairedMap (n : ℕ) (g : C2) : Equiv.Perm (pairedModel n) :=
  Equiv.mulLeft (g, 1)

private theorem pairedMap_mul (n : ℕ) (g h : C2) :
    pairedMap n (g * h) = pairedMap n g * pairedMap n h := by
  simpa [pairedMap] using
    (mulLeft_mul (pairedCarrier n) (g, 1) (h, 1))

private theorem pairedMap_distance_one (n : ℕ) {g : C2} (hg : g ≠ 1) :
    hammingDistance (pairedModel n) (pairedMap n g) 1 = 1 := by
  rw [show (1 : Equiv.Perm (pairedModel n)) =
    Equiv.mulLeft (1 : pairedCarrier n) by
      apply Equiv.ext
      intro x
      change x = (1 : pairedCarrier n) * x
      rw [one_mul]]
  apply hammingDistance_mulLeft
  intro hp
  apply hg
  exact congrArg Prod.fst hp

/-- An exact sofic approximation of the group of order two.  The second
coordinate only amplifies the model, while the first carries the regular
action. -/
private noncomputable abbrev pairedApproximation : SoficApproximation C2 where
  model := pairedModel
  map := pairedMap
  card_tendsToInfinity := by
    intro M
    refine ⟨M, fun n hn ↦ ?_⟩
    simp only [pairedModel, pairedCarrier, regularModel, Fintype.card_prod,
      Fintype.card_multiplicative, ZMod.card]
    omega
  asymptoticallyMultiplicative := by
    intro g h ε hε
    refine ⟨0, fun _ _ ↦ ?_⟩
    rw [pairedMap_mul]
    simpa using hε
  asymptoticallyFaithful := by
    intro g hg ε hε
    refine ⟨0, fun n _ ↦ ?_⟩
    rw [pairedMap_distance_one n hg]
    linarith

private def c2Generator : C2 := Multiplicative.ofAdd 1

private theorem c2Generator_ne_one : c2Generator ≠ 1 := by
  norm_num [c2Generator]

private noncomputable def pairedBlocks (n : ℕ) :
    BlockStructure (pairedModel n) where
  block y := Finset.univ.filter fun z ↦ z.2 = y.2
  self_mem := by simp
  eq_of_mem := by
    intro x y hy
    have hxy : y.2 = x.2 := by simpa using hy
    ext z
    simp [hxy]

private noncomputable def edgeEditWitnessRefl (X : FiniteMultiGraph) :
    EdgeEditWitness X X (Equiv.refl X.vertex) where
  sourceKept := Finset.univ
  targetKept := Finset.univ
  edgeEquiv := Equiv.refl _
  preservesEndpoints := by
    intro a
    exact Or.inl ⟨rfl, rfl⟩

private theorem edgeEditWitnessRefl_unmatchedCount (X : FiniteMultiGraph) :
    (edgeEditWitnessRefl X).unmatchedCount = 0 := by
  simp [edgeEditWitnessRefl, EdgeEditWitness.unmatchedCount,
    EdgeEditWitness.sourceUnmatched, EdgeEditWitness.targetUnmatched]

private theorem pairedBlock_card (n : ℕ) (y : pairedModel n) :
    ((pairedBlocks n).block y).card = 2 := by
  classical
  let e : (↑((pairedBlocks n).block y)) ≃ C2 :=
    { toFun := fun z ↦ z.1.1
      invFun := fun a ↦ ⟨(a, y.2), by simp [pairedBlocks]⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · have hzmem := z.2
          change z.1 ∈ Finset.univ.filter
            (fun w : pairedCarrier n ↦ w.2 = y.2) at hzmem
          have hz : z.1.2 = y.2 := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hzmem
          exact hz.symm
      right_inv := fun _ ↦ rfl }
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr e]
  norm_num [C2]

private theorem pairedMap_generator_ne (n : ℕ) (y : pairedModel n) :
    pairedMap n c2Generator y ≠ y := by
  intro h
  apply c2Generator_ne_one
  have hfirst := congrArg Prod.fst h
  have hfirst' : c2Generator * y.1 = 1 * y.1 := by
    simpa [pairedMap] using hfirst
  exact mul_right_cancel hfirst'

private theorem pairedComponent_expands (n : ℕ) (y : pairedModel n) :
    ((generatorGraph (pairedModel n) {c2Generator} (pairedMap n)).induce
      ((pairedBlocks n).block y)).HasCheegerLowerBound 1 := by
  classical
  let X := generatorGraph (pairedModel n) {c2Generator} (pairedMap n)
  let B := (pairedBlocks n).block y
  have hBcard : B.card = 2 := pairedBlock_card n y
  refine ⟨by norm_num, ?_⟩
  intro U hUne hhalf
  have hvertex : Fintype.card (X.induce B).vertex = 2 := by
    simpa [FiniteMultiGraph.induce] using hBcard
  rw [hvertex] at hhalf
  have hUpos : 0 < U.card := Finset.card_pos.mpr hUne
  have hUcard : U.card = 1 := by omega
  obtain ⟨u, hu⟩ := hUne
  have hUeq : U = {u} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hUcard
    have huw : u = w := by simpa [hw] using hu
    simpa [huw] using hw
  let v0 : pairedModel n := pairedMap n c2Generator u.1
  have hv0B : v0 ∈ B := by
    have huSecond : u.1.2 = y.2 := by
      have huB : (u.1 : pairedModel n) ∈ B := u.2
      change u.1 ∈ Finset.univ.filter
        (fun w : pairedCarrier n ↦ w.2 = y.2) at huB
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using huB
    simpa [B, pairedBlocks, v0, pairedMap] using huSecond
  let v : (X.induce B).vertex := ⟨v0, hv0B⟩
  have hvne : v ≠ u := by
    intro hvu
    exact pairedMap_generator_ne n u.1 (congrArg Subtype.val hvu)
  have hvnot : v ∉ U := by simp [hUeq, hvne]
  let a : ({c2Generator} : Finset C2) :=
    ⟨c2Generator, Finset.mem_singleton_self c2Generator⟩
  have hmove : pairedMap n a.1 u.1 ≠ u.1 := by
    simpa [a] using pairedMap_generator_ne n u.1
  let e : X.edge := ⟨(a, u.1), by
    change (a, u.1) ∈ Finset.univ.filter
      (fun p : ({c2Generator} : Finset C2) × pairedModel n ↦
        pairedMap n p.1.1 p.2 ≠ p.2)
    simp [hmove]⟩
  let eB : (X.induce B).edge := ⟨e, by
    constructor
    · exact u.2
    · exact hv0B⟩
  have heBoundary : eB ∈ (X.induce B).boundary U := by
    change eB ∈ Finset.univ.filter (fun edge : (X.induce B).edge ↦
      ((X.induce B).first edge ∈ U ∧ (X.induce B).second edge ∉ U) ∨
      ((X.induce B).second edge ∈ U ∧ (X.induce B).first edge ∉ U))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    left
    constructor
    · change u ∈ U
      exact hu
    · change v ∉ U
      exact hvnot
  have hboundary : 1 ≤ (X.induce B).boundaryCard U := by
    exact Finset.one_le_card.mpr ⟨eB, heBoundary⟩
  norm_num [hUcard]
  exact_mod_cast hboundary

/-- A closed, non-singleton expander decomposition.  Every component is a
two-point orbit of the nontrivial element of `C2`, while an independent cyclic
coordinate makes the finite models diverge. -/
noncomputable def c2_expanderDecomposition :
    ExpanderDecomposition pairedApproximation {c2Generator} where
  blocks := pairedBlocks
  cheeger := 1
  cheeger_pos := by norm_num
  graph := fun n ↦
    generatorGraph (pairedModel n) {c2Generator} (pairedMap n)
  vertexEquiv := fun n ↦
    generatorGraphVertexEquiv (pairedModel n) {c2Generator} (pairedMap n)
  degreeBound := 2
  degree_le := by
    intro n
    simpa using generatorGraph_hasDegreeBound
      (pairedModel n) {c2Generator} (pairedMap n)
  edit_negligible := by
    apply Negligible.congr (Negligible.zero)
    intro n
    simp [generatorGraphVertexEquiv, FiniteMultiGraph.editDistance,
      FiniteMultiGraph.edgeMultiplicity]
  editWitness := by
    intro n
    change EdgeEditWitness
      (generatorGraph (pairedModel n) {c2Generator} (pairedMap n))
      (generatorGraph (pairedModel n) {c2Generator} (pairedMap n))
      (Equiv.refl _)
    exact edgeEditWitnessRefl _
  unmatched_negligible := by
    apply Negligible.congr (Negligible.zero)
    intro n
    exact_mod_cast (edgeEditWitnessRefl_unmatchedCount
      (generatorGraph (pairedModel n) {c2Generator} (pairedMap n))).symm
  edge_inside := by
    intro n e
    unfold generatorGraphVertexEquiv
    ext z
    simp [pairedBlocks, pairedMap]
  component_expands := by
    intro n y
    exact pairedComponent_expands n y
  almost_invariant := by
    intro t ht
    apply Negligible.congr (Negligible.zero)
    intro n
    have ht' : t = c2Generator := by simpa using ht
    subst t
    simp [pairedApproximation, pairedBlocks, pairedMap]

private abbrev boolModel : FiniteModel :=
  { carrier := Bool
    fintype := inferInstance
    decidableEq := inferInstance }

private noncomputable abbrev boolEmptyGraph : FiniteMultiGraph where
  vertex := boolModel
  edge :=
    { carrier := Fin 0
      fintype := inferInstance
      decidableEq := inferInstance }
  first := Fin.elim0
  second := Fin.elim0
  loopless := fun e ↦ Fin.elim0 e

private abbrev twoPointModel := pairedModel 0

private def twoPointSwap : Equiv.Perm twoPointModel :=
  pairedMap 0 c2Generator

private theorem twoPointModel_card : Fintype.card twoPointModel = 2 := by
  simp [pairedCarrier, Fintype.card_multiplicative, ZMod.card]

private theorem twoPointSwap_ne (y : twoPointModel) : twoPointSwap y ≠ y :=
  pairedMap_generator_ne 0 y

/-- The exact two-point swap has directed Cheeger constant one.  Unlike the
singleton branch probe, this has an admissible cut and an actual crossing. -/
theorem twoPointSwap_hasDirectedCheegerLowerBound :
    DirectedCoarea.HasCheegerLowerBound twoPointModel {twoPointSwap} 1 := by
  classical
  refine ⟨by norm_num, ?_⟩
  intro U hUne hhalf
  rw [twoPointModel_card] at hhalf
  have hUpos : 0 < U.card := Finset.card_pos.mpr hUne
  have hUcard : U.card = 1 := by omega
  obtain ⟨u, hu⟩ := hUne
  have hUeq : U = {u} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hUcard
    have huw : u = w := by simpa [hw] using hu
    simpa [huw] using hw
  let p : Equiv.Perm twoPointModel × twoPointModel := (twoPointSwap, u)
  have hp : p ∈ AlmostAutomorphism.directedBoundary
      twoPointModel {twoPointSwap} U := by
    rw [AlmostAutomorphism.mem_directedBoundary]
    refine ⟨by simp [p], ?_⟩
    left
    constructor
    · exact hu
    · rw [hUeq]
      simpa [p] using twoPointSwap_ne u
  norm_num [hUcard]
  exact ⟨p, hp⟩

/-- The same real crossing supplies expansion at the cluster scale `m = 1`. -/
theorem twoPointSwap_hasDirectedExpansionAtScale :
    AlmostAutomorphism.HasDirectedExpansionAtScale
      twoPointModel {twoPointSwap} 1 1 := by
  refine ⟨by norm_num, ?_⟩
  intro U hm hhalf
  apply twoPointSwap_hasDirectedCheegerLowerBound.2 U
  · exact Finset.card_pos.mp (by omega)
  · exact hhalf

/-- Directed Cheeger expansion gives a closed `ℓ¹` Poincare control. -/
theorem twoPointSwap_hasL1PoincareAtOne :
    KazhdanImprovement.HasL1PoincareAtOne
      twoPointModel {twoPointSwap} 1 :=
  KazhdanImprovement.hasL1PoincareAtOne_of_cheeger
    twoPointModel {twoPointSwap} twoPointSwap_hasDirectedCheegerLowerBound

private def twoPointAction : C2 →* Equiv.Perm twoPointModel where
  toFun := pairedMap 0
  map_one' := by
    apply Equiv.ext
    intro x
    change (1 : pairedCarrier 0) * x = x
    rw [one_mul]
  map_mul' := pairedMap_mul 0

/-- The regular action of `C₂` on two points has labelled action expansion;
the unique admissible cut moves to its disjoint complement. -/
theorem twoPointAction_hasActionExpansion :
    KazhdanFiniteModel.HasActionExpansion
      twoPointAction {c2Generator} 1 := by
  classical
  intro U hUne hhalf
  rw [twoPointModel_card] at hhalf
  have hUpos : 0 < U.card := Finset.card_pos.mpr hUne
  have hUcard : U.card = 1 := by omega
  obtain ⟨u, hu⟩ := hUne
  have hUeq : U = {u} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hUcard
    have huw : u = w := by simpa [hw] using hu
    simpa [huw] using hw
  have hne : pairedMap 0 c2Generator u ≠ u :=
    pairedMap_generator_ne 0 u
  rw [hUeq]
  simp [KazhdanFiniteModel.actionBoundarySize, twoPointAction, hne]

/-- Cauchy--Schwarz gives a nonzero, nonvacuous epsilon-orthogonality
control on the full real line. -/
theorem real_top_epsilonOrthogonal :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (⊤ : Submodule ℝ ℝ) ⊤ 1 := by
  intro u _ v _
  simpa only [one_mul] using abs_real_inner_le_norm u v

/-- A singleton in a two-vertex edgeless graph is an actual sparse cut. -/
theorem boolEmptyGraph_hasSparseCut :
    MaximalCutRepair.IsSparseCut boolEmptyGraph 1
      ({show boolEmptyGraph.vertex from false} :
        Finset boolEmptyGraph.vertex) := by
  refine ⟨by simp, ?_, ?_⟩
  · change 2 ≤ Fintype.card Bool
    norm_num [Fintype.card_bool]
  · norm_num [boolEmptyGraph, boolModel, FiniteMultiGraph.boundaryCard,
      FiniteMultiGraph.boundary]

/-- The identity is a good almost automorphism at a positive defect scale. -/
theorem bool_identity_isGood :
    AlmostAutomorphism.IsGood boolModel ∅ 1 1 1 := by
  norm_num [AlmostAutomorphism.IsGood, AlmostAutomorphism.badArcs]

/-- The independent epsilon-good predicate also contains the identity. -/
theorem bool_identity_isEpsilonGood :
    KazhdanImprovement.IsEpsilonGood boolModel ∅ 1 1 := by
  constructor <;> simp [AlmostAutomorphism.badArcs]

/-- Detection at degree zero is realized by the empty word and the constant
minus-one functional. -/
theorem unit_hasDetectionAtDegreeZero :
    FreeRootCharacterValuation.HasDetectionAtDegree Unit
      (n := 0) (fun _ ↦ (-1 : ℝ)) 0 := by
  refine ⟨1, ?_⟩
  have hlen : FreeAlgebraDegree.freeWordLength Unit (1 : FreeMonoid Unit) = 0 :=
    (FreeAlgebraDegree.freeWordLength_eq_zero_iff Unit 1).2 rfl
  exact ⟨hlen, by omega, rfl⟩

/-- The constant-positive sign assignment is the trivial character on a
concrete plane. -/
theorem unit_constantTrue_isPlaneCharacterSign :
    FreeRootCharacterValuation.IsPlaneCharacterSign Unit
      0 1 2 (by decide) (by decide) (by decide) 0 (fun _ ↦ true) := by
  intro g h
  simp [FreeRootPlaneFourier.planeEigenvalue]

/-- The universal Leavitt relation family has a concrete member. -/
theorem universalLeavitt_t0_s0_relation :
    UniversalLeavitt.Relation
      (FreeAlgebra.ι (ZMod 2) BinaryLeavitt.t0 *
        FreeAlgebra.ι (ZMod 2) BinaryLeavitt.s0) 1 :=
  BinaryLeavitt.Relation.t0_s0

/-- Both switching predicates are realized by their named edge occurrences. -/
theorem kunSpectral_firstSwitch_exists :
    KunSpectral.isFirstSwitch
      ((0, 0) : KunSpectral.Ix 0 × KunSpectral.Ix 0) :=
  ⟨rfl, rfl⟩

theorem kunSpectral_secondSwitch_exists :
    KunSpectral.isSecondSwitch
      ((1, 1) : KunSpectral.Ix 0 × KunSpectral.Ix 0) :=
  ⟨rfl, rfl⟩

/-- An edgeless two-vertex graph is concretely bipartite. -/
theorem boolEmptyGraph_isBipartite :
    KunSpectral.IsBipartite boolEmptyGraph := by
  refine ⟨fun _ ↦ false, ?_⟩
  intro e
  exact Fin.elim0 e

/-- The trivial orthogonal action on the real line is irreducible. -/
theorem real_trivial_isOrthogonallyIrreducible :
    FiniteClassTwoOrthogonality.IsOrthogonallyIrreducible
      (1 : Unit →* (ℝ ≃ₗᵢ[ℝ] ℝ)) := by
  refine ⟨inferInstance, ?_⟩
  intro U _
  by_cases hU : U = ⊥
  · exact Or.inl hU
  · right
    rw [eq_top_iff]
    intro x
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    have hone : (1 : ℝ) ∈ U := by
      have := U.smul_mem (u⁻¹) hu
      simpa [hu0] using this
    have := U.smul_mem x hone
    simpa using this

private abbrev concreteA2 := elementaryA2System (ZMod 2)

private theorem concreteA2_exponentTwo :
    ∀ (i j : Fin 3) (hij : i ≠ j),
      ∀ g ∈ concreteA2.root i j hij, g ^ 2 = 1 := by
  intro i j hij g hg
  exact elementaryRootSubgroup_sq i j hij g hg

private theorem concreteA2_existsConstantProjectionBound :
    ∃ gamma : ℝ, 0 ≤ gamma ∧ gamma < 1 ∧
      A2MagicHilbert.ConstantProjectionBound.{0, 0} concreteA2 gamma := by
  exact A2MagicHilbert.exists_constantProjectionBound
    concreteA2 concreteA2_exponentTwo

private noncomputable def concreteA2ProjectionGamma : ℝ :=
  Classical.choose concreteA2_existsConstantProjectionBound

private theorem concreteA2ProjectionGamma_nonneg :
    0 ≤ concreteA2ProjectionGamma :=
  (Classical.choose_spec
    concreteA2_existsConstantProjectionBound).1

/-- The characteristic-two elementary A2 system satisfies the constant-family
projection predicate for a closed, constructed constant. -/
theorem concreteA2_constantProjectionBound :
    A2MagicHilbert.ConstantProjectionBound.{0, 0}
      concreteA2 concreteA2ProjectionGamma :=
  (Classical.choose_spec concreteA2_existsConstantProjectionBound).2.2

/-- The same concrete system satisfies the operator-facing projection bound. -/
theorem concreteA2_vertexProjectionBound :
    A2System.VertexProjectionBound.{0, 0}
      concreteA2 concreteA2ProjectionGamma :=
  A2MagicHilbert.vertexProjectionBound_of_constantProjectionBound
    concreteA2 concreteA2_constantProjectionBound

/-- The same concrete system satisfies the six-space codistance bound. -/
theorem concreteA2_vertexCodistanceBound :
    A2System.VertexCodistanceBound.{0, 0}
      concreteA2 concreteA2ProjectionGamma :=
  concreteA2.vertexCodistanceBound_of_projectionBound
    concreteA2ProjectionGamma_nonneg concreteA2_vertexProjectionBound

/-- The one-element group has the elementary Kazhdan pair `(∅, 1)`. -/
theorem unit_isKazhdanPair :
    IsKazhdanPair.{0, 0} Unit ∅ 1 := by
  refine ⟨by norm_num, ?_⟩
  intro E _ _ _ ρ x hx _
  refine ⟨x, ?_, ?_⟩
  · intro hzero
    rw [hzero, norm_zero] at hx
    norm_num at hx
  · intro g
    cases g
    change ρ 1 x = x
    rw [map_one]
    rfl

/-- The same finite control set is an inhabited Kazhdan subset. -/
theorem unit_isKazhdanSubset :
    IsKazhdanSubset.{0, 0} Unit (∅ : Set Unit) 1 :=
  by simpa using IsKazhdanSubset.of_pair unit_isKazhdanPair

/-- Product-restricted soficity is satisfiable, independently of its
equivalence theorem. -/
theorem unit_isSoficProductRestricted : IsSoficProductRestricted Unit :=
  (isSofic_iff_productRestricted Unit).mp (isSofic_of_finite Unit)

/-- A closed multiplication-table model on a concrete finite group. -/
theorem zmodTwo_tableModel :
    Nonempty (TableModel (Multiplicative (ZMod 2)) {1} (1 / 2 : ℝ)) :=
  tableModel_of_isSofic (isSofic_of_finite (Multiplicative (ZMod 2)))
    {1} (1 / 2) (by norm_num)

/-- A closed finite cluster.  Its ambient permutation model has two points;
the selected finite group is the identity subgroup and rounding is its retraction. -/
noncomputable def zmodTwo_identityClusterData :
    AlmostAutomorphism.ClusterData
      (regularModel (Multiplicative (ZMod 2))) where
  radius := 1 / 4
  radius_pos := by norm_num
  candidate := {1}
  one_mem := by simp
  inv_mem := by
    intro c hc
    simpa using hc
  round := fun _ ↦ 1
  round_product_mem := by simp
  round_product_close := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    simp
  gap := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    left
    simp

end NonsoficGroupsExist
