import NonsoficGroupsExist.Leavitt.UnitsGLProfile
import NonsoficGroupsExist.Leavitt.RankTwoCompression

/-!
# `GL_n = EL_n` at every rank, perfectness of the unit group, and the
# rank-two compression over `L_k(1,2)`

Three closures, all by transport along maps the library already proves:

* **All ranks.**  `GL_n(L) = EL_n(L)` for every `n ≥ 2` and every field,
  with no new Gaussian elimination: the coefficient equivalence along the
  prefix-code self-similarity `A ≃+* M_m(A)` and the block flattening
  `EL_p(M_q(A)) = EL_{pq}(A)` carry the rank-two collapse
  (`glTwo_eq_elementary_holds`, from the `K₁` chain) up to `EL_{2n}` and
  then back down to `EL_n` — even ranks from rank two, every rank from
  its double.

* **Perfectness.**  `L_k(1,2)ˣ` is perfect: the three-leaf prefix code
  identifies `Lˣ` with `GL₃ = EL₃`, and every elementary generator is a
  commutator by the Steinberg relation.  This removes the last use of
  the cited `K₁`-theoretic input (Ara–Goodearl–Pardo part (b)).

* **Rank two closes.**  The two-by-two Leavitt-corner theorem
  (`rankTwo_not_isSofic`) is instantiated over `L_k(1,2)` for every
  finite field: all three of its hypotheses — `GL₂ = EL₂` and property
  `(T)` for `GL₂` and for `Lˣ` — are now closed theorems.
-/

namespace NonsoficGroupsExist

open scoped commutatorElement

section Transport

variable {R S : Type*} [Ring R] [Ring S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fullness of a subgroup transports along an equivalence that carries
it onto a second subgroup. -/
private theorem map_eq_top_iff {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) {A : Subgroup G} {B : Subgroup H}
    (hmap : A.map e.toMonoidHom = B) : A = ⊤ ↔ B = ⊤ := by
  constructor
  · intro hA
    rw [← hmap, hA]
    exact Subgroup.map_top_of_surjective _ e.surjective
  · intro hB
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ B := by
      rw [hB]
      exact Subgroup.mem_top _
    rw [← hmap, Subgroup.mem_map_equiv] at hx
    simpa using hx

/-- A coefficient-ring isomorphism carries the elementary subgroup onto
the elementary subgroup (units-level form). -/
private theorem coefficientGroup_map (f : R ≃+* S) :
    (elementaryGroup ι R).map
        (Units.mapEquiv (f.mapMatrix (m := ι)).toMulEquiv).toMonoidHom =
      elementaryGroup ι S := by
  have hmap : (Units.mapEquiv
      (f.mapMatrix (m := ι)).toMulEquiv).toMonoidHom =
      elementaryMatrixUnitMap f.toRingHom := by
    ext u
    rfl
  rw [hmap]
  exact elementaryGroup_map_eq_of_surjective f.toRingHom f.surjective

/-- Coefficient transport of fullness. -/
private theorem eq_top_coeff (f : R ≃+* S)
    (h : elementaryGroup ι R = ⊤) : elementaryGroup ι S = ⊤ :=
  (map_eq_top_iff (Units.mapEquiv (f.mapMatrix (m := ι)).toMulEquiv)
    (coefficientGroup_map f)).mp h

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Block-flattening transport of fullness, upward. -/
private theorem eq_top_flatten [Nontrivial ι]
    (h : elementaryGroup ι (Matrix κ κ R) = ⊤) :
    elementaryGroup (ι × κ) R = ⊤ :=
  (map_eq_top_iff elementaryBlockUnitEquiv elementaryBlockGroup_map).mp h

/-- Block-flattening transport of fullness, downward. -/
private theorem eq_top_unflatten [Nontrivial ι]
    (h : elementaryGroup (ι × κ) R = ⊤) :
    elementaryGroup ι (Matrix κ κ R) = ⊤ :=
  (map_eq_top_iff elementaryBlockUnitEquiv elementaryBlockGroup_map).mpr h

/-- Reindexing transport of fullness. -/
private theorem eq_top_reindex (e : ι ≃ κ)
    (h : elementaryGroup ι R = ⊤) : elementaryGroup κ R = ⊤ :=
  (map_eq_top_iff (elementaryReindexUnitEquiv e)
    (elementaryReindexGroup_map e)).mp h

end Transport

namespace BinaryLeavitt

open LeavittFamily

variable (k : Type) [Field k]

set_option maxHeartbeats 1000000 in
/-- **`GL_n = EL_n` at every rank `n ≥ 2`**, as a subgroup equality,
over every field.  Even ranks are reached from rank two by coefficient
transport and block flattening; every rank is then reached back down
from its double by the same two maps. -/
theorem elementaryGroup_eq_top (n : ℕ) (hn : 2 ≤ n) :
    elementaryGroup (Fin n) (BinaryLeavittAlgebra k) = ⊤ := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  haveI : Nontrivial (Fin (n' + 1)) :=
    ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, by
      intro h
      simpa using congrArg Fin.val h⟩⟩
  -- rank two, coefficients extended to `M_n(A)`
  have h2M : elementaryGroup (Fin 2)
      (Matrix (Fin (n' + 1)) (Fin (n' + 1)) (BinaryLeavittAlgebra k)) = ⊤ :=
    eq_top_coeff
      ((family k).prefixRingEquiv (leftCombCode n')
        ((family k).leftCombCode_complete n')).symm
      (binaryLeavitt_elementaryGroup_two_eq_top k)
  -- flatten, reindex, unflatten
  have hprod : elementaryGroup (Fin 2 × Fin (n' + 1))
      (BinaryLeavittAlgebra k) = ⊤ := eq_top_flatten h2M
  have hprod' : elementaryGroup (Fin (n' + 1) × Fin 2)
      (BinaryLeavittAlgebra k) = ⊤ :=
    eq_top_reindex (Equiv.prodComm (Fin 2) (Fin (n' + 1))) hprod
  have hnM : elementaryGroup (Fin (n' + 1))
      (Matrix (Fin 2) (Fin 2) (BinaryLeavittAlgebra k)) = ⊤ :=
    eq_top_unflatten hprod'
  -- contract the coefficients back to `A`
  exact eq_top_coeff
    ((family k).prefixRingEquiv (leftCombCode 1)
      ((family k).leftCombCode_complete 1)) hnM

/-- `GL_n = EL_n` in membership form: every invertible `n × n` matrix
over `L_k(1,2)` is a product of elementary matrices, for every
`n ≥ 2` and every field `k`. -/
theorem glAll_eq_elementary (n : ℕ) (hn : 2 ≤ n)
    (M : (Matrix (Fin n) (Fin n) (BinaryLeavittAlgebra k))ˣ) :
    M ∈ elementaryGroup (Fin n) (BinaryLeavittAlgebra k) := by
  rw [elementaryGroup_eq_top k n hn]
  exact Subgroup.mem_top M

private theorem fin3_exists_third : ∀ i j : Fin 3, i ≠ j →
    ∃ l : Fin 3, i ≠ l ∧ l ≠ j := by decide

/-- **Perfectness of the unit group**: `L_k(1,2)ˣ` equals its own
commutator subgroup, over every field.  The three-leaf code identifies
`Lˣ` with `GL₃ = EL₃`, whose generators are commutators by the
Steinberg relation. -/
theorem binaryLeavittUnits_perfect :
    commutator (BinaryLeavittUnits k) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  let e : (Matrix (Fin 3) (Fin 3) (BinaryLeavittAlgebra k))ˣ ≃*
      (BinaryLeavittAlgebra k)ˣ :=
    (family k).prefixUnitsEquiv (leftCombCode 2)
      ((family k).leftCombCode_complete 2)
  -- the preimage matrix is elementary
  have hX : e.symm u ∈ elementaryGroup (Fin 3) (BinaryLeavittAlgebra k) := by
    rw [elementaryGroup_eq_top k 3 (by omega)]
    exact Subgroup.mem_top _
  -- elementary matrices land in the commutator subgroup of `Lˣ`
  have hle : elementaryGroup (Fin 3) (BinaryLeavittAlgebra k) ≤
      (commutator (BinaryLeavittUnits k)).comap e.toMonoidHom := by
    rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨i, j, hij, a, rfl⟩
    obtain ⟨l, hil, hlj⟩ := fin3_exists_third i j hij
    have hcomm : elementaryUnit i j hij a =
        ⁅elementaryUnit i l hil a, elementaryUnit l j hlj 1⁆ := by
      rw [elementaryUnit_commutator i l j hil hlj hij a 1, mul_one]
    show e (elementaryUnit i j hij a) ∈ commutator (BinaryLeavittUnits k)
    rw [hcomm, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
      (Subgroup.mem_top _)
  have := hle hX
  rw [Subgroup.mem_comap] at this
  simpa using this

end BinaryLeavitt

open BinaryLeavitt in
/-- **The manuscript's `thm:el2`, by the rank-two compression itself**:
over every finite field `k`, the group `GL₂(L_k(1,2)) = EL₂(L_k(1,2))`
is not sofic, via the two-by-two Leavitt-corner theorem — every one of
its hypotheses is a closed theorem of this library.  (The rank
equivalence gives the same conclusion by a different route; this is the
manuscript's rank-two realization, formalized as stated.) -/
theorem binaryLeavittRankTwo_not_isSofic (k : Type) [Field k]
    [Finite k] : ¬ IsSofic (BinaryLeavittGL k 1) := by
  obtain ⟨-, -, hTG, -⟩ := binaryLeavittGL_profile k 1
  obtain ⟨-, -, hTU, -⟩ := binaryLeavittUnits_profile k
  exact LeavittFamily.rankTwo_not_isSofic (BinaryLeavittAlgebra k)
    (family k) (binaryLeavitt_elementaryGroup_two_eq_top k) hTG hTU

end NonsoficGroupsExist
