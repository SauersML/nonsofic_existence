import NonsoficGroupsExist.Sofic
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.Data.Countable.Small
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite multiplication tables and finitely presented covers

This file formalizes Section `sec:fp` of the manuscript.

`TableModel G F ε` is Definition `def:model`: a permutation model of the finite
multiplication table `F` with error `ε`.  Lemma `lem:models` is the pair
`tableModel_of_isSofic` / `isSofic_of_tableModels`: a countable group is sofic
exactly when every finite table admits models of every positive accuracy.

Theorem `thm:table` is `tableGroup_not_isSofic`: imposing a forbidden finite
table as relators produces a finitely presented group that is not sofic and
surjects onto the original group.
-/

namespace NonsoficGroupsExist

open scoped BigOperators

variable {G : Type*} [Group G]

/-- Definition `def:model`: a finite permutation model of the finite table `F`,
accurate to within `ε`. -/
structure TableModel (G : Type*) [Group G] (F : Finset G) (ε : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  act : G → Equiv.Perm carrier
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    hammingDistance carrier (act (g * h)) (act g * act h) < ε
  separated : ∀ g ∈ F, g ≠ 1 → 1 - ε < hammingDistance carrier (act g) 1

/-! ### Amplification -/

/-- Multiply the carrier of a finite model by a fixed finite factor. -/
def FiniteModel.amplify (Y : FiniteModel) (k : ℕ) : FiniteModel where
  carrier := Fin k × Y
  fintype := inferInstance
  decidableEq := inferInstance

/-- Amplify a permutation by acting trivially on the new factor. -/
def amplifyPerm {Y : FiniteModel} (k : ℕ) (p : Equiv.Perm Y) :
    Equiv.Perm (Y.amplify k) :=
  (Equiv.refl (Fin k)).prodCongr p

theorem hammingDistance_amplify {Y : FiniteModel} {k : ℕ} (hk : 0 < k)
    (p q : Equiv.Perm Y) :
    hammingDistance (Y.amplify k) (amplifyPerm k p) (amplifyPerm k q) =
      hammingDistance Y p q := by
  classical
  have hfilter :
      (Finset.univ.filter fun z : Fin k × Y ↦
          amplifyPerm k p z ≠ amplifyPerm k q z) =
        (Finset.univ : Finset (Fin k)) ×ˢ
          (Finset.univ.filter fun y : Y ↦ p y ≠ q y) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      amplifyPerm]
    change ((z.1, p z.2) ≠ (z.1, q z.2)) ↔ p z.2 ≠ q z.2
    simp
  have hcard : Fintype.card (Y.amplify k) = k * Fintype.card Y := by
    change Fintype.card (Fin k × Y) = k * Fintype.card Y
    rw [Fintype.card_prod]
    simp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold hammingDistance
  change
    ((Finset.univ.filter fun z : Fin k × Y ↦
      amplifyPerm k p z ≠ amplifyPerm k q z).card : ℝ) /
        Fintype.card (Y.amplify k) =
      ((Finset.univ.filter fun y : Y ↦ p y ≠ q y).card : ℝ) / Fintype.card Y
  rw [hfilter, Finset.card_product, Finset.card_univ, Fintype.card_fin, hcard]
  push_cast
  rw [mul_comm (k : ℝ), mul_comm (k : ℝ)]
  rw [mul_div_mul_right _ _ (ne_of_gt hkR)]

/-- Amplification of a whole table model. -/
def TableModel.amplify {F : Finset G} {ε : ℝ} (M : TableModel G F ε) (k : ℕ)
    (hk : 0 < k) : TableModel G F ε where
  carrier := M.carrier.amplify k
  nonempty := by
    change 0 < Fintype.card (Fin k × M.carrier)
    rw [Fintype.card_prod]
    simpa using Nat.mul_pos hk M.nonempty
  act g := amplifyPerm k (M.act g)
  multiplicative g hg h hh := by
    have hmul : amplifyPerm k (M.act g) * amplifyPerm k (M.act h) =
        amplifyPerm k (M.act g * M.act h) := by
      apply Equiv.ext
      intro z
      rfl
    rw [hmul, hammingDistance_amplify hk]
    exact M.multiplicative g hg h hh
  separated g hg hne := by
    have hone : (1 : Equiv.Perm (M.carrier.amplify k)) =
        amplifyPerm k (1 : Equiv.Perm M.carrier) := by
      apply Equiv.ext
      intro z
      rfl
    rw [hone, hammingDistance_amplify hk]
    exact M.separated g hg hne

theorem TableModel.card_amplify {F : Finset G} {ε : ℝ} (M : TableModel G F ε)
    (k : ℕ) (hk : 0 < k) : k ≤ Fintype.card (M.amplify k hk).carrier := by
  change k ≤ Fintype.card (Fin k × M.carrier)
  rw [Fintype.card_prod]
  simpa using Nat.mul_le_mul_left k (Nat.succ_le_iff.mpr M.nonempty)

/-! ### Lemma `lem:models` -/

/-- Every sofic group has models of every finite table to every accuracy. -/
theorem tableModel_of_isSofic [Countable G] (h : IsSofic G) (F : Finset G)
    (ε : ℝ) (hε : 0 < ε) : Nonempty (TableModel G F ε) := by
  classical
  obtain ⟨S⟩ := h
  -- choose one index at which all finitely many constraints hold
  have hpairs : ∃ N : ℕ, ∀ n ≥ N,
      (0 < Fintype.card (S.model n)) ∧
      (∀ g ∈ F, ∀ h ∈ F,
        hammingDistance (S.model n) (S.map n (g * h)) (S.map n g * S.map n h) < ε) ∧
      (∀ g ∈ F, g ≠ 1 → 1 - ε < hammingDistance (S.model n) (S.map n g) 1) := by
    obtain ⟨N₀, hN₀⟩ := S.card_tendsToInfinity 1
    -- finitely many multiplicativity constraints
    have hmul : ∀ p : G × G, ∃ N : ℕ, ∀ n ≥ N,
        hammingDistance (S.model n) (S.map n (p.1 * p.2))
          (S.map n p.1 * S.map n p.2) < ε := fun p ↦
      S.asymptoticallyMultiplicative p.1 p.2 ε hε
    have hfaith : ∀ g : G, ∃ N : ℕ, ∀ n ≥ N,
        g ≠ 1 → 1 - ε < hammingDistance (S.model n) (S.map n g) 1 := by
      intro g
      by_cases hg : g = 1
      · exact ⟨0, fun n _ hne ↦ absurd hg hne⟩
      · obtain ⟨N, hN⟩ := S.asymptoticallyFaithful g hg ε hε
        exact ⟨N, fun n hn _ ↦ hN n hn⟩
    choose Nmul hNmul using hmul
    choose Nfaith hNfaith using hfaith
    set Bm : Finset ℕ := insert 0 ((F ×ˢ F).image fun p ↦ Nmul p) with hBm
    set Bf : Finset ℕ := insert 0 (F.image fun g ↦ Nfaith g) with hBf
    set Nm : ℕ := Bm.max' (Finset.insert_nonempty 0 _) with hNm
    set Nf : ℕ := Bf.max' (Finset.insert_nonempty 0 _) with hNf
    refine ⟨max N₀ (max Nm Nf), fun n hn ↦ ⟨?_, ?_, ?_⟩⟩
    · exact hN₀ n ((le_max_left _ _).trans hn)
    · intro g hg h hh
      have hle : Nmul (g, h) ≤ Nm := by
        apply Bm.le_max'
        rw [hBm]
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr
          ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩
      exact hNmul (g, h) n (hle.trans ((le_max_left Nm Nf).trans
        ((le_max_right N₀ _).trans hn)))
    · intro g hg hne
      have hle : Nfaith g ≤ Nf := by
        apply Bf.le_max'
        rw [hBf]
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
      exact hNfaith g n (hle.trans ((le_max_right Nm Nf).trans
        ((le_max_right N₀ _).trans hn))) hne
  obtain ⟨N, hN⟩ := hpairs
  obtain ⟨hcard, hmul, hfaith⟩ := hN N le_rfl
  exact ⟨{ carrier := S.model N
           nonempty := hcard
           act := S.map N
           multiplicative := hmul
           separated := hfaith }⟩

/-- Conversely, a countable group with models of every finite table to every
accuracy is sofic.  The models are amplified so that the carriers diverge. -/
theorem isSofic_of_tableModels [Countable G] [Nonempty G]
    (h : ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (TableModel G F ε)) :
    IsSofic G := by
  classical
  obtain ⟨enum, henum⟩ : ∃ e : ℕ → G, Function.Surjective e :=
    exists_surjective_nat G
  set F : ℕ → Finset G := fun n ↦ (Finset.range (n + 1)).image enum with hF
  have hmono : ∀ m n : ℕ, m ≤ n → F m ⊆ F n := by
    intro m n hmn
    apply Finset.image_subset_image
    exact Finset.range_mono (Nat.add_le_add_right hmn 1)
  have hmem : ∀ g : G, ∃ N : ℕ, ∀ n ≥ N, g ∈ F n := by
    intro g
    obtain ⟨i, rfl⟩ := henum g
    refine ⟨i, fun n hn ↦ ?_⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩
  set eps : ℕ → ℝ := fun n ↦ 1 / (n + 2) with heps
  have heps_pos : ∀ n, 0 < eps n := by
    intro n
    simp only [heps]
    positivity
  -- `(h (F n) (eps n) _).some` is a model of the `n`-th table; amplify it by `n+1`
  refine ⟨{
    model := fun n ↦ ((h (F n) (eps n) (heps_pos n)).some.amplify (n + 1)
      (Nat.succ_pos n)).carrier
    map := fun n g ↦ ((h (F n) (eps n) (heps_pos n)).some.amplify (n + 1)
      (Nat.succ_pos n)).act g
    card_tendsToInfinity := ?_
    asymptoticallyMultiplicative := ?_
    asymptoticallyFaithful := ?_ }⟩
  · intro K
    refine ⟨K, fun n hn ↦ ?_⟩
    have := TableModel.card_amplify (h (F n) (eps n) (heps_pos n)).some (n + 1)
      (Nat.succ_pos n)
    omega
  · intro g hg ε hε
    obtain ⟨N₁, hN₁⟩ := hmem g
    obtain ⟨N₂, hN₂⟩ := hmem hg
    obtain ⟨N₃, hN₃⟩ : ∃ N : ℕ, ∀ n ≥ N, eps n ≤ ε := by
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      refine ⟨k, fun n hn ↦ ?_⟩
      have hle : (1 : ℝ) / (n + 2) ≤ 1 / (k + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (k : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp only [heps]
      linarith [hk]
    refine ⟨max N₁ (max N₂ N₃), fun n hn ↦ ?_⟩
    have h₁ := hN₁ n ((le_max_left _ _).trans hn)
    have h₂ := hN₂ n ((le_max_left N₂ N₃).trans ((le_max_right N₁ _).trans hn))
    have h₃ := hN₃ n ((le_max_right N₂ N₃).trans ((le_max_right N₁ _).trans hn))
    exact lt_of_lt_of_le
      (((h (F n) (eps n) (heps_pos n)).some.amplify (n + 1)
        (Nat.succ_pos n)).multiplicative g h₁ hg h₂) h₃
  · intro g hne ε hε
    obtain ⟨N₁, hN₁⟩ := hmem g
    obtain ⟨N₃, hN₃⟩ : ∃ N : ℕ, ∀ n ≥ N, eps n ≤ ε := by
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      refine ⟨k, fun n hn ↦ ?_⟩
      have hle : (1 : ℝ) / (n + 2) ≤ 1 / (k + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (k : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      simp only [heps]
      linarith [hk]
    refine ⟨max N₁ N₃, fun n hn ↦ ?_⟩
    have h₁ := hN₁ n ((le_max_left _ _).trans hn)
    have h₃ := hN₃ n ((le_max_right N₁ N₃).trans hn)
    have hsep := ((h (F n) (eps n) (heps_pos n)).some.amplify (n + 1)
      (Nat.succ_pos n)).separated g h₁ hne
    linarith

/-- Restricting the table only weakens the requirements on a model. -/
def TableModel.restrict {F F' : Finset G} {ε : ℝ} (M : TableModel G F' ε)
    (hFF : F ⊆ F') : TableModel G F ε where
  carrier := M.carrier
  nonempty := M.nonempty
  act := M.act
  multiplicative g hg h hh := M.multiplicative g (hFF hg) h (hFF hh)
  separated g hg hne := M.separated g (hFF hg) hne

/-- A forbidden table remains forbidden after adjoining more named elements. -/
theorem tableModel_isEmpty_mono {F F' : Finset G} {ε : ℝ}
    (hbad : IsEmpty (TableModel G F ε)) (hFF : F ⊆ F') :
    IsEmpty (TableModel G F' ε) := by
  constructor
  intro M
  exact hbad.false (M.restrict hFF)

/-- **Lemma `lem:models`.**  A countable group fails to be sofic exactly when
some finite table containing `1` admits no sufficiently accurate model. -/
theorem exists_table_obstruction [Countable G] [Nonempty G] (h : ¬ IsSofic G) :
    ∃ (F : Finset G) (ε : ℝ), 1 ∈ F ∧ 0 < ε ∧ IsEmpty (TableModel G F ε) := by
  classical
  by_contra hcon
  push Not at hcon
  apply h
  apply isSofic_of_tableModels
  intro F ε hε
  have hone : (1 : G) ∈ insert (1 : G) F := Finset.mem_insert_self 1 F
  have hnot := hcon (insert 1 F) ε hone hε
  obtain ⟨M⟩ := hnot
  exact ⟨M.restrict (Finset.subset_insert 1 F)⟩

/-! ### The finitely presented cover -/

section Presentation

variable (F : Finset G)

/-- The finite set of group elements named by the table. -/
noncomputable def multiplicationTable : Finset G := by
  classical
  exact F ∪ (F ×ˢ F).image fun x : G × G ↦ x.1 * x.2

noncomputable instance multiplicationTableFintype : Fintype ↥(multiplicationTable F) := by
  classical
  exact Fintype.ofFinset (multiplicationTable F) (fun _ ↦ Iff.rfl)

theorem mem_multiplicationTable_of_mem {g : G} (hg : g ∈ F) :
    g ∈ multiplicationTable F := by
  classical
  simp [multiplicationTable, hg]

theorem mul_mem_multiplicationTable {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    g * h ∈ multiplicationTable F := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩

variable (h₁ : 1 ∈ F)

/-- The relators asserting that the named generators multiply according to the
table, and that the generator named by `1` is trivial. -/
noncomputable def tableRelators :
    Finset (FreeGroup ↥(multiplicationTable F)) := by
  classical
  exact
    {FreeGroup.of ⟨(1 : G), mem_multiplicationTable_of_mem F h₁⟩} ∪
      (F.attach ×ˢ F.attach).image fun x ↦
        FreeGroup.of ⟨x.1.1, mem_multiplicationTable_of_mem F x.1.2⟩ *
          FreeGroup.of ⟨x.2.1, mem_multiplicationTable_of_mem F x.2.2⟩ *
          (FreeGroup.of
            ⟨x.1.1 * x.2.1, mul_mem_multiplicationTable F x.1.2 x.2.2⟩)⁻¹

/-- The finitely presented group defined by the finite multiplication table. -/
noncomputable abbrev tableGroup : Type _ :=
  PresentedGroup
    (tableRelators F h₁ : Set (FreeGroup ↥(multiplicationTable F)))

noncomputable instance tableGroupCountable : Countable (tableGroup F h₁) := by
  exact (PresentedGroup.mk_surjective
    (tableRelators F h₁ : Set (FreeGroup ↥(multiplicationTable F)))).countable

/-- The generator of the table group named by an element of the table. -/
noncomputable def tableGenerator (g : ↥(multiplicationTable F)) :
    tableGroup F h₁ :=
  PresentedGroup.of g

theorem tableGenerator_one :
    tableGenerator F h₁ ⟨(1 : G), mem_multiplicationTable_of_mem F h₁⟩ = 1 := by
  classical
  change PresentedGroup.mk _ (FreeGroup.of _) = 1
  apply PresentedGroup.one_of_mem
  change FreeGroup.of _ ∈ tableRelators F h₁
  simp [tableRelators]

theorem tableGenerator_mul {g h : G} (hg : g ∈ F) (hh : h ∈ F) :
    tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem F hg⟩ *
        tableGenerator F h₁ ⟨h, mem_multiplicationTable_of_mem F hh⟩ =
      tableGenerator F h₁ ⟨g * h, mul_mem_multiplicationTable F hg hh⟩ := by
  classical
  have hrel :
      (FreeGroup.of ⟨g, mem_multiplicationTable_of_mem F hg⟩ *
          FreeGroup.of ⟨h, mem_multiplicationTable_of_mem F hh⟩) *
          (FreeGroup.of ⟨g * h, mul_mem_multiplicationTable F hg hh⟩)⁻¹ ∈
        (tableRelators F h₁ :
          Set (FreeGroup ↥(multiplicationTable F))) := by
    change _ ∈ tableRelators F h₁
    rw [tableRelators]
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨(⟨g, hg⟩, ⟨h, hh⟩), ?_, rfl⟩
    simp
  simpa only [tableGenerator, PresentedGroup.of, map_mul] using
    PresentedGroup.mk_eq_mk_of_mul_inv_mem hrel

/-- Evaluating the generators at the elements they name gives a homomorphism
back to `G`; this is what proves the named elements stay distinct. -/
noncomputable def tableEvaluation : tableGroup F h₁ →* G := by
  classical
  apply PresentedGroup.toGroup (f := fun g : ↥(multiplicationTable F) ↦ g.1)
  intro r hr
  change r ∈ tableRelators F h₁ at hr
  simp only [tableRelators, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_image] at hr
  rcases hr with rfl | ⟨⟨g, h⟩, _, rfl⟩
  · simp
  · simp

@[simp] theorem tableEvaluation_generator (g : ↥(multiplicationTable F)) :
    tableEvaluation F h₁ (tableGenerator F h₁ g) = g.1 := by
  change PresentedGroup.toGroup _ (PresentedGroup.of g) = g.1
  exact PresentedGroup.toGroup.of _

/-- If the table contains a generating set of `G`, evaluation of the presented
table group onto the elements it names is surjective. -/
theorem tableEvaluation_surjective (S : Finset G) (hSF : S ⊆ F)
    (hgen : Subgroup.closure (S : Set G) = ⊤) :
    Function.Surjective (tableEvaluation F h₁) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← hgen]
  rw [Subgroup.closure_le]
  intro g hg
  refine ⟨tableGenerator F h₁
    ⟨g, mem_multiplicationTable_of_mem F (hSF hg)⟩, ?_⟩
  simp

theorem tableGenerator_ne_one {g : G} (hg : g ∈ F) (hne : g ≠ 1) :
    tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem F hg⟩ ≠ 1 := by
  intro h
  apply hne
  simpa using congrArg (tableEvaluation F h₁) h

/-- The finite table inside the table group. -/
noncomputable def tableTestSet : Finset (tableGroup F h₁) := by
  classical
  exact F.attach.image fun g ↦
    tableGenerator F h₁ ⟨g.1, mem_multiplicationTable_of_mem F g.2⟩

theorem tableGenerator_mem_tableTestSet {g : G} (hg : g ∈ F) :
    tableGenerator F h₁ ⟨g, mem_multiplicationTable_of_mem F hg⟩ ∈
      tableTestSet F h₁ := by
  classical
  exact Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩

/-- Pulling a model of the table group back along the naming map produces a
model of the original table. -/
noncomputable def pullbackTableModel {ε : ℝ}
    (M : TableModel (tableGroup F h₁) (tableTestSet F h₁) ε) :
    TableModel G F ε := by
  classical
  refine
    { carrier := M.carrier
      nonempty := M.nonempty
      act := fun g ↦
        if hg : g ∈ multiplicationTable F then
          M.act (tableGenerator F h₁ ⟨g, hg⟩) else 1
      multiplicative := ?_
      separated := ?_ }
  · intro g hg h hh
    rw [dif_pos (mul_mem_multiplicationTable F hg hh),
      dif_pos (mem_multiplicationTable_of_mem F hg),
      dif_pos (mem_multiplicationTable_of_mem F hh),
      ← tableGenerator_mul F h₁ hg hh]
    exact M.multiplicative _ (tableGenerator_mem_tableTestSet F h₁ hg) _
      (tableGenerator_mem_tableTestSet F h₁ hh)
  · intro g hg hne
    rw [dif_pos (mem_multiplicationTable_of_mem F hg)]
    exact M.separated _ (tableGenerator_mem_tableTestSet F h₁ hg)
      (tableGenerator_ne_one F h₁ hg hne)

/-- **Theorem `thm:table`.**  If a finite table of `G` admits no `ε`-accurate
model, then the finitely presented group defined by that table admits no
`ε`-accurate model of its own table, hence is not sofic. -/
theorem tableGroup_no_model {ε : ℝ}
    (hbad : IsEmpty (TableModel G F ε)) :
    IsEmpty (TableModel (tableGroup F h₁) (tableTestSet F h₁) ε) := by
  constructor
  intro M
  exact hbad.false (pullbackTableModel F h₁ M)

theorem tableGroup_not_isSofic [Countable (tableGroup F h₁)] {ε : ℝ}
    (hε : 0 < ε) (hbad : IsEmpty (TableModel G F ε)) :
    ¬ IsSofic (tableGroup F h₁) := by
  intro hsofic
  have := tableModel_of_isSofic hsofic (tableTestSet F h₁) ε hε
  exact (tableGroup_no_model F h₁ hbad).false this.some

end Presentation

/-- **Theorem `thm:C`**: every finitely generated nonsofic group is covered by
a finitely presented nonsofic group, namely the group defined by a forbidden
finite multiplication table enlarged to contain generators of `G`. -/
theorem exists_finitelyPresented_obstruction [Countable G] [Nonempty G] [Group.FG G]
    (h : ¬ IsSofic G) :
    ∃ (F : Finset G) (h₁ : 1 ∈ F) (ε : ℝ), 0 < ε ∧
      IsEmpty (TableModel (tableGroup F h₁) (tableTestSet F h₁) ε) ∧
      ¬ IsSofic (tableGroup F h₁) ∧
      Function.Surjective (tableEvaluation F h₁) := by
  classical
  obtain ⟨F₀, ε, _, hε, hbad⟩ := exists_table_obstruction h
  obtain ⟨_, S, _, hgen⟩ := Group.fg_iff'.mp (inferInstance : Group.FG G)
  let F : Finset G := insert 1 (F₀ ∪ S)
  have h₁ : (1 : G) ∈ F := by simp [F]
  have hF₀ : F₀ ⊆ F := by
    intro g hg
    simp [F, hg]
  have hS : S ⊆ F := by
    intro g hg
    simp [F, hg]
  have hbadF : IsEmpty (TableModel G F ε) := tableModel_isEmpty_mono hbad hF₀
  have hcover : Function.Surjective (tableEvaluation F h₁) :=
    tableEvaluation_surjective F h₁ S hS hgen
  have hbadGroup := tableGroup_no_model F h₁ hbadF
  have hnsofic := tableGroup_not_isSofic F h₁ hε hbadF
  exact ⟨F, h₁, ε, hε, hbadGroup, hnsofic, hcover⟩

end NonsoficGroupsExist
