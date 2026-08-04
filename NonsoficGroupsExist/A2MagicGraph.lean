import NonsoficGroupsExist.A2System
import NonsoficGroupsExist.KazhdanFixedSpace

/-!
# The six-vertex magic graph of type A₂

The vertices are the six ordered pairs of distinct coordinates.  A vertex
`(i,j)` is adjacent to the four vertices other than itself and `(j,i)`.
The explicit ordering below matches the four edge subgroups used in the local
codistance estimate.
-/

namespace NonsoficGroupsExist

namespace A2MagicGraph

/-- Explicit enumeration `(01,02,10,12,20,21)` of the six vertices. -/
def vertex : Fin 6 → A2Root :=
  ![⟨((0 : Fin 3), (1 : Fin 3)), by
      intro h; have := congrArg Fin.val h; norm_num at this⟩,
    ⟨((0 : Fin 3), (2 : Fin 3)), by
      intro h; have := congrArg Fin.val h; norm_num at this⟩,
    ⟨((1 : Fin 3), (0 : Fin 3)), by
      intro h; have := congrArg Fin.val h; norm_num at this⟩,
    ⟨((1 : Fin 3), (2 : Fin 3)), by
      intro h; have := congrArg Fin.val h; norm_num at this⟩,
    ⟨((2 : Fin 3), (0 : Fin 3)), by
      intro h; have := congrArg Fin.val h; norm_num at this⟩,
    ⟨((2 : Fin 3), (1 : Fin 3)), by
      intro h; have := congrArg Fin.val h; norm_num at this⟩]

theorem vertex_injective : Function.Injective vertex := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [vertex]

theorem vertex_surjective : Function.Surjective vertex := by
  rintro ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact ⟨0, by apply Subtype.ext; rfl⟩
  · exact ⟨1, by apply Subtype.ext; rfl⟩
  · exact ⟨2, by apply Subtype.ext; rfl⟩
  · exact (hij rfl).elim
  · exact ⟨3, by apply Subtype.ext; rfl⟩
  · exact ⟨4, by apply Subtype.ext; rfl⟩
  · exact ⟨5, by apply Subtype.ext; rfl⟩
  · exact (hij rfl).elim

/-- The concrete enumeration as an equivalence. -/
noncomputable def vertexEquiv : Fin 6 ≃ A2Root :=
  Equiv.ofBijective vertex ⟨vertex_injective, vertex_surjective⟩

@[simp] theorem vertexEquiv_apply (i : Fin 6) : vertexEquiv i = vertex i := rfl

theorem a2Root_card : Fintype.card A2Root = 6 := by
  simpa using (Fintype.card_congr vertexEquiv).symm

/-- Opposite vertices in the explicit six-element indexing. -/
def oppositeIndex : Fin 6 → Fin 6 := ![2, 4, 0, 5, 1, 3]

/-- The four neighbors in the explicit six-element indexing. -/
def neighborIndex : Fin 6 → Fin 4 → Fin 6 :=
  ![![1, 5, 3, 4],
    ![0, 3, 5, 2],
    ![3, 4, 1, 5],
    ![2, 1, 4, 0],
    ![5, 2, 0, 3],
    ![4, 0, 2, 1]]

/-- The vertex opposite `(i,j)` is `(j,i)`. -/
def opposite (r : A2Root) : A2Root :=
  ⟨(r.1.2, r.1.1), r.2.symm⟩

/-- The four neighbors of `(i,j)`, with `k` the remaining coordinate, are
`(i,k)`, `(k,j)`, `(j,k)`, and `(k,i)`. -/
def neighbor (r : A2Root) : Fin 4 → A2Root :=
  let i := r.1.1
  let j := r.1.2
  let k := a2ThirdIndex i j
  ![⟨(i, k), (a2ThirdIndex_ne_left i j r.2).symm⟩,
    ⟨(k, j), a2ThirdIndex_ne_right i j r.2⟩,
    ⟨(j, k), (a2ThirdIndex_ne_right i j r.2).symm⟩,
    ⟨(k, i), a2ThirdIndex_ne_left i j r.2⟩]

@[simp] theorem vertex_oppositeIndex (i : Fin 6) :
    vertex (oppositeIndex i) = opposite (vertex i) := by
  fin_cases i <;> simp [vertex, oppositeIndex, opposite]

@[simp] theorem vertex_neighborIndex (i : Fin 6) (n : Fin 4) :
    vertex (neighborIndex i n) = neighbor (vertex i) n := by
  fin_cases i <;> fin_cases n <;>
    simp [vertex, neighborIndex, neighbor, a2ThirdIndex]

@[simp] theorem third_same_left (i j : Fin 3) (hij : i ≠ j) :
    a2ThirdIndex i (a2ThirdIndex i j) = j := by
  fin_cases i <;> fin_cases j <;> simp_all [a2ThirdIndex]

@[simp] theorem third_same_right (i j : Fin 3) (hij : i ≠ j) :
    a2ThirdIndex (a2ThirdIndex i j) j = i := by
  fin_cases i <;> fin_cases j <;> simp_all [a2ThirdIndex]

@[simp] theorem third_reversed_left (i j : Fin 3) (hij : i ≠ j) :
    a2ThirdIndex j (a2ThirdIndex i j) = i := by
  fin_cases i <;> fin_cases j <;> simp_all [a2ThirdIndex]

@[simp] theorem third_reversed_right (i j : Fin 3) (hij : i ≠ j) :
    a2ThirdIndex (a2ThirdIndex i j) i = j := by
  fin_cases i <;> fin_cases j <;> simp_all [a2ThirdIndex]

@[simp] theorem neighbor_zero (r : A2Root) :
    neighbor r 0 =
      ⟨(r.1.1, a2ThirdIndex r.1.1 r.1.2),
        (a2ThirdIndex_ne_left r.1.1 r.1.2 r.2).symm⟩ := rfl

@[simp] theorem neighbor_one (r : A2Root) :
    neighbor r 1 =
      ⟨(a2ThirdIndex r.1.1 r.1.2, r.1.2),
        a2ThirdIndex_ne_right r.1.1 r.1.2 r.2⟩ := rfl

@[simp] theorem neighbor_two (r : A2Root) :
    neighbor r 2 =
      ⟨(r.1.2, a2ThirdIndex r.1.1 r.1.2),
        (a2ThirdIndex_ne_right r.1.1 r.1.2 r.2).symm⟩ := rfl

@[simp] theorem neighbor_three (r : A2Root) :
    neighbor r 3 =
      ⟨(a2ThirdIndex r.1.1 r.1.2, r.1.1),
        a2ThirdIndex_ne_left r.1.1 r.1.2 r.2⟩ := rfl

@[simp] theorem opposite_opposite (r : A2Root) :
    opposite (opposite r) = r := by
  apply Subtype.ext
  rfl

theorem neighbor_ne_self (r : A2Root) (n : Fin 4) : neighbor r n ≠ r := by
  fin_cases n
  · intro h
    have hc := congrArg (fun s : A2Root ↦ s.1.2) h
    exact (a2ThirdIndex_ne_right r.1.1 r.1.2 r.2) hc
  · intro h
    have hc := congrArg (fun s : A2Root ↦ s.1.1) h
    exact (a2ThirdIndex_ne_left r.1.1 r.1.2 r.2) hc
  · intro h
    have hc := congrArg (fun s : A2Root ↦ s.1.1) h
    exact r.2 hc.symm
  · intro h
    have hc := congrArg (fun s : A2Root ↦ s.1.2) h
    exact r.2 hc

theorem neighbor_ne_opposite (r : A2Root) (n : Fin 4) :
    neighbor r n ≠ opposite r := by
  fin_cases n
  · intro h
    have hc := congrArg (fun s : A2Root ↦ s.1.1) h
    exact r.2 hc
  · intro h
    have hc := congrArg (fun s : A2Root ↦ s.1.2) h
    exact r.2 hc.symm
  · intro h
    have hc := congrArg (fun s : A2Root ↦ s.1.2) h
    exact (a2ThirdIndex_ne_left r.1.1 r.1.2 r.2) hc
  · intro h
    have hc := congrArg (fun s : A2Root ↦ s.1.1) h
    exact (a2ThirdIndex_ne_right r.1.1 r.1.2 r.2) hc

variable {G : Type*} [Group G]

/-- The four edge subgroups incident to a magic-graph vertex, ordered in the
same way as `neighbor`. -/
def edgeGroup (A : A2System G) (r : A2Root) : Fin 4 → Subgroup G :=
  ![A.leftEdgeGroup r, A.rightEdgeGroup r,
    A.leftRootGroup r, A.rightRootGroup r]

theorem edgeGroup_le_sourceVertex (A : A2System G) (r : A2Root) (n : Fin 4) :
    edgeGroup A r n ≤ A.vertexGroup r := by
  fin_cases n
  · exact A.leftEdgeGroup_le_vertexGroup r
  · exact A.rightEdgeGroup_le_vertexGroup r
  · exact A.leftRoot_le_vertexGroup r
  · exact A.rightRoot_le_vertexGroup r

theorem edgeGroup_le_targetVertex (A : A2System G) (r : A2Root) (n : Fin 4) :
    edgeGroup A r n ≤ A.vertexGroup (neighbor r n) := by
  fin_cases n
  · apply sup_le
    · simpa [edgeGroup, A2System.leftEdgeGroup, A2System.leftRootGroup,
        A2System.rootAt] using A.rootAt_le_vertexGroup (neighbor r 0)
    · have hthird := third_same_left r.1.1 r.1.2 r.2
      simpa [edgeGroup, A2System.leftEdgeGroup, A2System.leftRootGroup,
        A2System.rootAt, hthird] using
          A.leftRoot_le_vertexGroup (neighbor r 0)
  · apply sup_le
    · simpa [edgeGroup, A2System.rightEdgeGroup, A2System.rightRootGroup,
        A2System.rootAt] using A.rootAt_le_vertexGroup (neighbor r 1)
    · have hthird := third_same_right r.1.1 r.1.2 r.2
      simpa [edgeGroup, A2System.rightEdgeGroup, A2System.rightRootGroup,
        A2System.rootAt, hthird] using
          A.rightRoot_le_vertexGroup (neighbor r 1)
  · have hthird := third_reversed_left r.1.1 r.1.2 r.2
    simpa [edgeGroup, A2System.leftRootGroup, A2System.rightRootGroup,
      hthird] using A.rightRoot_le_vertexGroup (neighbor r 2)
  · have hthird := third_reversed_right r.1.1 r.1.2 r.2
    simpa [edgeGroup, A2System.leftRootGroup, A2System.rightRootGroup,
      hthird] using A.leftRoot_le_vertexGroup (neighbor r 3)

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Differences of vertex-fixed vectors are fixed by the edge joining the
two vertices. -/
theorem vertexFixed_sub_neighbor_mem_edgeFixed
    (A : A2System G) (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (f : A2Root → E)
    (hf : ∀ r, f r ∈ KazhdanFixedSpace.fixedSubspace rho (A.vertexGroup r))
    (r : A2Root) (n : Fin 4) :
    f r - f (neighbor r n) ∈
      KazhdanFixedSpace.fixedSubspace rho (edgeGroup A r n) := by
  exact (KazhdanFixedSpace.fixedSubspace rho (edgeGroup A r n)).sub_mem
    (KazhdanFixedSpace.antitone rho (edgeGroup_le_sourceVertex A r n) (hf r))
    (KazhdanFixedSpace.antitone rho (edgeGroup_le_targetVertex A r n)
      (hf (neighbor r n)))

end A2MagicGraph
end NonsoficGroupsExist
