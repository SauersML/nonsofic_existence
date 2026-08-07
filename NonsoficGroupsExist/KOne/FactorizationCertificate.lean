import NonsoficGroupsExist.KOne.RefineLoopDischarge
import NonsoficGroupsExist.KOne.CodeScalarMoves
import NonsoficGroupsExist.KOne.CodeChangeUnits
import NonsoficGroupsExist.KOne.IncomparableUnipotents
import NonsoficGroupsExist.Leavitt.LeavittDiagonalClass

/-!
# Factorization certificates for the `K₁` chain

`RefineLoopDischarge.K1_trivial` says that every unit `u` of
`L = L_k(1,2)` is *stable*: `diag(u, 1)` lies in `EL₂(L)`.  That is a
membership in a `Subgroup.closure`, so it carries a word in the
generators; this module extracts that word and reads it back inside
`L` itself.

Three layers.

* Over an arbitrary ring, `ElementaryMove ι R` is the data `(i, j, i ≠ j, a)`
  of one elementary matrix, `elementaryProd` evaluates a list of moves in
  order, and `mem_elementaryGroup_iff_exists_elementaryMoves` says that
  membership in `EL_ι(R)` is exactly the existence of such a list.  This is
  the constructive content of `Subgroup.closure`, nothing more.

* Along a complete prefix code `C` the isomorphism `Θ_C : M_ι(L) ≅ L`
  (`LeavittFamily.prefixUnitsEquiv`) carries `x_{ij}(a)` to the cylinder
  unipotent `1 + s_{c_i} a t_{c_j}`, so it carries a whole elementary
  certificate to a word in cylinder unipotents
  (`prefixUnitsEquiv_elementaryProd`).  For the depth-one code `{0, 1}` it
  carries `diag(u, 1)` to the corner insertion `κ_0(u) = s₀ u t₀ + s₁ t₁`.

* `Move k` is the manuscript's four-kind move vocabulary of
  Remark `rem:effectiveWH` — cylinder unipotents `1 + s_v x t_w`
  (`lem:unipapp`), code-scalar units (`lem:codescalarapp`), tree-table units
  (`lem:kappaapp`), and one nonpositive-degree window
  (`prop:windowsdieapp`) — with `Move.eval` naming the unit each move
  denotes and `Move.eval_mem_stableUnits` checking that each of the four
  kinds really is discharged by the corresponding lemma of the chain.

**What is proved here, exactly.**  `exists_moveList` produces, for every
unit `u` of `L`, an explicit finite certificate `c : List (Move k)` — all of
whose moves are cylinder unipotents at the two atoms `[0]`, `[1]` — with
`evalList c = κ_0(u)`.  The manuscript's removed claim was a factorization
of `u` itself into the four kinds; that is *not* what is proved.  The
existing chain proves `u ∈ stableUnits L`, i.e. a statement about
`diag(u, 1)`, and `Θ` turns `diag(u, 1)` into `κ_0(u)`, not into `u`.  No
size bound is proved either: `Subgroup.closure` membership carries a word
but no length, and none of the moves of the elimination chain is
witness-carrying, so the certificate produced here is finite but
unbounded as far as this development knows.  `certSize` is defined so that
a future bound has something to bound.
-/

namespace NonsoficGroupsExist

/-! ### Elementary certificates over an arbitrary ring -/

/-- The data of a single elementary move `x_{ij}(a) = 1 + a·E_{ij}`. -/
structure ElementaryMove (ι R : Type*) [Ring R] where
  /-- The row the move writes into. -/
  row : ι
  /-- The column the move reads from. -/
  col : ι
  /-- Elementary matrices are strictly off-diagonal. -/
  ne : row ≠ col
  /-- The coefficient the move adds. -/
  coeff : R

namespace ElementaryMove

variable {ι R : Type*} [Ring R]

/-- The move with the opposite coefficient; it evaluates to the inverse. -/
def negate (m : ElementaryMove ι R) : ElementaryMove ι R :=
  ⟨m.row, m.col, m.ne, -m.coeff⟩

/-- The reversed, coefficient-negated certificate. -/
def invList (c : List (ElementaryMove ι R)) : List (ElementaryMove ι R) :=
  (c.map negate).reverse

@[simp] theorem invList_nil :
    invList ([] : List (ElementaryMove ι R)) = [] := rfl

theorem invList_cons (m : ElementaryMove ι R)
    (c : List (ElementaryMove ι R)) :
    invList (m :: c) = invList c ++ [m.negate] := by
  simp [invList]

variable [Fintype ι] [DecidableEq ι]

/-- The elementary matrix named by a move. -/
def eval (m : ElementaryMove ι R) : (Matrix ι ι R)ˣ :=
  elementaryUnit m.row m.col m.ne m.coeff

@[simp] theorem eval_eq (m : ElementaryMove ι R) :
    m.eval = elementaryUnit m.row m.col m.ne m.coeff := rfl

theorem eval_mem (m : ElementaryMove ι R) :
    m.eval ∈ elementaryGroup ι R :=
  elementaryUnit_mem m.row m.col m.ne m.coeff

theorem eval_negate (m : ElementaryMove ι R) : m.negate.eval = m.eval⁻¹ :=
  eq_inv_of_mul_eq_one_left (by
    show elementaryUnit m.row m.col m.ne (-m.coeff) *
        elementaryUnit m.row m.col m.ne m.coeff = 1
    rw [elementaryUnit_mul, neg_add_cancel, elementaryUnit_zero])

end ElementaryMove

section ElementaryCertificate

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The matrix named by an elementary certificate: the ordered product of
its moves. -/
def elementaryProd (c : List (ElementaryMove ι R)) : (Matrix ι ι R)ˣ :=
  (c.map ElementaryMove.eval).prod

@[simp] theorem elementaryProd_nil :
    elementaryProd ([] : List (ElementaryMove ι R)) = 1 := rfl

@[simp] theorem elementaryProd_cons (m : ElementaryMove ι R)
    (c : List (ElementaryMove ι R)) :
    elementaryProd (m :: c) = m.eval * elementaryProd c := rfl

theorem elementaryProd_append (c d : List (ElementaryMove ι R)) :
    elementaryProd (c ++ d) = elementaryProd c * elementaryProd d := by
  unfold elementaryProd
  rw [List.map_append, List.prod_append]

theorem elementaryProd_invList (c : List (ElementaryMove ι R)) :
    elementaryProd (ElementaryMove.invList c) = (elementaryProd c)⁻¹ := by
  induction c with
  | nil => rw [ElementaryMove.invList_nil, elementaryProd_nil, inv_one]
  | cons m c ih =>
      rw [ElementaryMove.invList_cons, elementaryProd_append, ih,
        elementaryProd_cons, elementaryProd_nil, mul_one,
        ElementaryMove.eval_negate, elementaryProd_cons, mul_inv_rev]

/-- Soundness: a certificate evaluates into the elementary group. -/
theorem elementaryProd_mem (c : List (ElementaryMove ι R)) :
    elementaryProd c ∈ elementaryGroup ι R := by
  induction c with
  | nil =>
      rw [elementaryProd_nil]
      exact one_mem _
  | cons m c ih =>
      rw [elementaryProd_cons]
      exact mul_mem m.eval_mem ih

/-- Completeness: membership in `EL_ι(R)` is closure membership, and a
closure membership unfolds to a word.  The generating set is closed under
inversion (`ElementaryMove.eval_negate`), so the word needs no formal
inverses. -/
theorem exists_elementaryMoves {M : (Matrix ι ι R)ˣ}
    (hM : M ∈ elementaryGroup ι R) :
    ∃ c : List (ElementaryMove ι R), elementaryProd c = M := by
  induction hM using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨i, j, hij, a, rfl⟩ := hz
      refine ⟨[⟨i, j, hij, a⟩], ?_⟩
      rw [elementaryProd_cons, elementaryProd_nil, mul_one]
      rfl
  | one => exact ⟨[], elementaryProd_nil⟩
  | mul _ _ _ _ hx hy =>
      obtain ⟨cx, hcx⟩ := hx
      obtain ⟨cy, hcy⟩ := hy
      exact ⟨cx ++ cy, by rw [elementaryProd_append, hcx, hcy]⟩
  | inv _ _ hx =>
      obtain ⟨cx, hcx⟩ := hx
      exact ⟨ElementaryMove.invList cx, by rw [elementaryProd_invList, hcx]⟩

theorem mem_elementaryGroup_iff_exists_elementaryMoves
    {M : (Matrix ι ι R)ˣ} :
    M ∈ elementaryGroup ι R ↔
      ∃ c : List (ElementaryMove ι R), elementaryProd c = M :=
  ⟨exists_elementaryMoves, fun ⟨c, hc⟩ ↦ hc ▸ elementaryProd_mem c⟩

end ElementaryCertificate

/-! ### The depth-one code -/

/-- The depth-one complete code `{0, 1}`, indexed by `Fin 2` on the nose.
`leftCombCode 1` is the same code carried by `Fin (1 + 1)`; the index type
here is chosen so that the rank-two diagonal `diag(u, 1)` transports along
it without a cast. -/
def atomCode : BinaryPrefixCode (Fin 2) where
  word i := [i]
  prefix_free := by
    intro i j hij hp
    obtain ⟨t, ht⟩ := hp
    have hcons : i :: t = j :: ([] : List (Fin 2)) := ht
    injection hcons with h1 _
    exact hij h1

@[simp] theorem atomCode_word (i : Fin 2) : atomCode.word i = [i] := rfl

/-! ### Transport of a certificate along `Θ_C` -/

namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Under `Θ_C` an elementary matrix is the cylinder unipotent at the two
leaves it names. -/
theorem prefixUnitsEquiv_elementaryUnit (E : BinaryPrefixCode ι)
    (hE : L.IsComplete E) (i j : ι) (hij : i ≠ j) (a : A) :
    L.prefixUnitsEquiv E hE (elementaryUnit i j hij a) =
      L.incomparableUnit (E.prefix_free hij) (E.prefix_free (Ne.symm hij))
        a :=
  Units.ext (by
    rw [L.prefixUnitsEquiv_elementaryUnit_val E hE i j hij a]
    rfl)

/-- **An elementary certificate transports to a word in cylinder
unipotents** at the leaves of `C`. -/
theorem prefixUnitsEquiv_elementaryProd (E : BinaryPrefixCode ι)
    (hE : L.IsComplete E) (c : List (ElementaryMove ι A)) :
    L.prefixUnitsEquiv E hE (elementaryProd c) =
      (c.map fun m ↦ L.incomparableUnit (E.prefix_free m.ne)
        (E.prefix_free (Ne.symm m.ne)) m.coeff).prod := by
  induction c with
  | nil => rw [elementaryProd_nil, map_one, List.map_nil, List.prod_nil]
  | cons m c ih =>
      rw [elementaryProd_cons, map_mul, ih, List.map_cons, List.prod_cons,
        ElementaryMove.eval_eq, L.prefixUnitsEquiv_elementaryUnit E hE]

/-- The two atoms form a complete code. -/
theorem isComplete_atomCode : L.IsComplete atomCode := by
  have h := L.sum_s_mul_t
  show ∑ i : Fin 2, L.cylinder (atomCode.word i) = 1
  rw [Fin.sum_univ_two]
  simpa [cylinder] using h

/-- **`Θ` at the two atoms turns the diagonal stabilization into the
corner insertion**: `Θ(diag(u, 1)) = s₀ u t₀ + s₁ t₁ = κ_{[0]}(u)`. -/
theorem prefixUnitsEquiv_atomCode_diagUnit (u : Aˣ) :
    L.prefixUnitsEquiv atomCode L.isComplete_atomCode (diagUnit u) =
      L.kappaUnit [0] u := by
  have h00 : ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
      Matrix (Fin 2) (Fin 2) A) 0 0 = (u : A) := rfl
  have h01 : ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
      Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := rfl
  have h10 : ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
      Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := rfl
  have h11 : ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
      Matrix (Fin 2) (Fin 2) A) 1 1 = 1 := rfl
  have hcompl : L.wordS [1] * L.wordT [1] =
      1 - L.wordS ([0] : List (Fin 2)) * L.wordT [0] := by
    have h : L.wordS ([0] : List (Fin 2)) * L.wordT [0] +
        L.wordS ([1] : List (Fin 2)) * L.wordT [1] = 1 := by
      simpa using L.sum_s_mul_t
    rw [← h]
    abel
  refine Units.ext ?_
  show (∑ i : Fin 2, ∑ j : Fin 2, L.wordS (atomCode.word i) *
      ((diagUnit u : (Matrix (Fin 2) (Fin 2) A)ˣ) :
        Matrix (Fin 2) (Fin 2) A) i j * L.wordT (atomCode.word j)) = _
  simp only [Fin.sum_univ_two, atomCode_word, h00, h01, h10, h11,
    mul_zero, zero_mul, mul_one, add_zero, zero_add]
  rw [hcompl]
  rfl

end LeavittFamily

/-! ### The four-kind move vocabulary -/

namespace BinaryLeavitt

open LeavittFamily MatrixDiagonalization

/-- The four kinds of move of Remark `rem:effectiveWH`.  A move carries the
data the manuscript writes down for it; where the data alone does not
determine a unit of `L`, the move also carries the unit and the identity
pinning its value, which is the shape in which the chain's lemmas consume
it. -/
inductive Move (k : Type) [Field k] where
  /-- A cylinder unipotent `1 + s_v x t_w` at prefix-incomparable words. -/
  | unipotent (v w : List (Fin 2)) (hvw : ¬v <+: w) (hwv : ¬w <+: v)
      (x : BinaryLeavittAlgebra k) : Move k
  /-- A code-scalar unit: an invertible matrix over `k` transported along a
  complete leaf set. -/
  | codeScalar (n : ℕ) (D : BinaryPrefixCode (Fin n))
      (hD : (family k).IsComplete D) (G : Matrix (Fin n) (Fin n) k)
      (hG : IsUnit G) (g : (BinaryLeavittAlgebra k)ˣ)
      (hg : (g : BinaryLeavittAlgebra k) =
        (family k).codeScalar (k := k) D G) : Move k
  /-- A tree-table unit: a pairing of two complete leaf sets, i.e. an
  element of Thompson's group `V`. -/
  | treeTable (P : List (List (Fin 2) × List (Fin 2)))
      (hsrc : (family k).IsCompleteCode (P.map Prod.snd))
      (htgt : (family k).IsCompleteCode (P.map Prod.fst))
      (g : (BinaryLeavittAlgebra k)ˣ)
      (hg : (g : BinaryLeavittAlgebra k) = (family k).pairValue P) : Move k
  /-- A unit whose value lies in a window of nonpositive degree. -/
  | window (N : ℕ) (g : (BinaryLeavittAlgebra k)ˣ)
      (hg : (g : BinaryLeavittAlgebra k) ∈ Submodule.span k
        ((family k).degreeMonomials (-(N : ℤ) - 1) 0)) : Move k

namespace Move

variable {k : Type} [Field k]

/-- The unit a move denotes. -/
def eval : Move k → (BinaryLeavittAlgebra k)ˣ
  | .unipotent _ _ hvw hwv x => (family k).incomparableUnit hvw hwv x
  | .codeScalar _ _ _ _ _ g _ => g
  | .treeTable _ _ _ g _ => g
  | .window _ g _ => g

/-- The data a move writes down, as a natural number. -/
def size : Move k → ℕ
  | .unipotent v w _ _ _ => v.length + w.length + 1
  | .codeScalar n _ _ _ _ _ _ => n + 1
  | .treeTable P _ _ _ _ => P.length + 1
  | .window N _ _ => N + 1

theorem size_pos (m : Move k) : 0 < m.size := by
  cases m <;> exact Nat.succ_pos _

/-- **Each of the four kinds is discharged by the chain.**  Over `L` this
is also a consequence of `K1_trivial`, which says `stableUnits L = ⊤`; the
point of stating it separately is that each constructor is matched to the
specific lemma of Appendix A that kills it. -/
theorem eval_mem_stableUnits (m : Move k) :
    m.eval ∈ stableUnits (BinaryLeavittAlgebra k) := by
  have hdiv : ∀ x : BinaryLeavittAlgebra k, x ≠ 0 →
      ∃ p q : BinaryLeavittAlgebra k, p * x * q = 1 :=
    fun x hx ↦ exists_mul_mul_eq_one k hx
  cases m with
  | unipotent _ _ hvw hwv x =>
      exact (family k).incomparableUnit_mem hvw hwv x
  | codeScalar n D hD G hG g hg =>
      exact (family k).codeScalar_unit_mem hdiv D hD G hG g hg
  | treeTable P hsrc htgt g hg =>
      exact (family k).codeChange_mem_stableUnits (k := k) hdiv P.length P
        rfl hsrc htgt g hg
  | window N g hg => exact window_nonpos_mem_stableUnits k N g hg

end Move

variable {k : Type} [Field k]

/-- The unit a certificate denotes: the ordered product of its moves. -/
def evalList (c : List (Move k)) : (BinaryLeavittAlgebra k)ˣ :=
  (c.map Move.eval).prod

@[simp] theorem evalList_nil : evalList ([] : List (Move k)) = 1 := rfl

@[simp] theorem evalList_cons (m : Move k) (c : List (Move k)) :
    evalList (m :: c) = m.eval * evalList c := rfl

/-- The size of a certificate: the total data written down. -/
def certSize (c : List (Move k)) : ℕ := (c.map Move.size).sum

theorem length_le_certSize (c : List (Move k)) : c.length ≤ certSize c := by
  induction c with
  | nil => simp [certSize]
  | cons m c ih =>
      have hm := m.size_pos
      simp only [certSize] at ih
      simp only [certSize, List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem evalList_mem_stableUnits (c : List (Move k)) :
    evalList c ∈ stableUnits (BinaryLeavittAlgebra k) := by
  induction c with
  | nil =>
      rw [evalList_nil]
      exact one_mem _
  | cons m c ih =>
      rw [evalList_cons]
      exact mul_mem m.eval_mem_stableUnits ih

/-! ### The certificates -/

/-- **Whitehead form with a witness**: `diag(u, 1)` is an *explicit* product
of elementary matrices of `M₂(L)`.  This is `K1_trivial` with the word that
`Subgroup.closure` membership was hiding. -/
theorem exists_elementaryCertificate (u : (BinaryLeavittAlgebra k)ˣ) :
    ∃ c : List (ElementaryMove (Fin 2) (BinaryLeavittAlgebra k)),
      elementaryProd c = diagUnit u :=
  exists_elementaryMoves ((mem_stableUnits_iff u).mp (K1_trivial k u))

/-- **The factorization certificate.**  For every unit `u` of `L` the corner
insertion `κ_{[0]}(u) = s₀ u t₀ + s₁ t₁` is an explicit finite product of
moves, all of them cylinder unipotents `1 + s_v x t_w` at the two atoms
`v, w ∈ {[0], [1]}`.

This is the effectivity content the chain actually supports.  It is *not*
a factorization of `u` itself: `K1_trivial` is a statement about
`diag(u, 1)`, and `Θ` reads `diag(u, 1)` inside `L` as `κ_{[0]}(u)`.  No
bound on `c.length` or `certSize c` is claimed — see the module docstring. -/
theorem exists_moveList (u : (BinaryLeavittAlgebra k)ˣ) :
    ∃ c : List (Move k),
      (∀ m ∈ c, ∃ (i j : Fin 2) (h : i ≠ j) (x : BinaryLeavittAlgebra k),
        m = Move.unipotent (atomCode.word i) (atomCode.word j)
          (atomCode.prefix_free h) (atomCode.prefix_free (Ne.symm h)) x) ∧
      evalList c = (family k).kappaUnit [0] u := by
  obtain ⟨c, hc⟩ := exists_elementaryCertificate u
  refine ⟨c.map (fun m ↦ Move.unipotent (atomCode.word m.row)
      (atomCode.word m.col) (atomCode.prefix_free m.ne)
      (atomCode.prefix_free (Ne.symm m.ne)) m.coeff), ?_, ?_⟩
  · intro m hm
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hm
    exact ⟨a.row, a.col, a.ne, a.coeff, rfl⟩
  · have hΦ := (family k).prefixUnitsEquiv_elementaryProd atomCode
      (family k).isComplete_atomCode c
    rw [hc, (family k).prefixUnitsEquiv_atomCode_diagUnit u] at hΦ
    rw [hΦ]
    unfold evalList
    rw [List.map_map]
    rfl

end BinaryLeavitt
end NonsoficGroupsExist
