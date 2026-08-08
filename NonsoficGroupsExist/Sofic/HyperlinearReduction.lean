import NonsoficGroupsExist.Sofic.Hyperlinear
import NonsoficGroupsExist.Sofic.SoficTransfer
import NonsoficGroupsExist.Sofic.LEFSofic

/-!
# Question 3.4 reduces to finitely generated groups

Both soficity and hyperlinearity are defined by quantifying over finite subsets,
so neither can see beyond the subgroup a finite subset generates.  Made precise
that is a reduction of Pestov's Question 3.4 itself: *if every finitely
generated hyperlinear group is sofic, then every hyperlinear group is sofic*.

Two ingredients, both restrictions and nothing more.  Soficity passes along an
injective homomorphism -- that is `isSofic_of_injective` of `SoficTransfer` --
and it is *local*: a model of a subgroup extends to the ambient group by sending
everything outside the image to the identity.  The guard has to be membership in
the image rather than in the finite test set, since the multiplicativity
condition names `g * h`, which need not lie in the test set but does lie in the
image.

Given a finite `F ⊆ G`, the subgroup it generates is finitely generated, and
hyperlinear by `isHyperlinear_of_injective`; the hypothesis makes it sofic; and
locality carries a model back to `G`.  So nothing is lost by restricting
Question 3.4 to finitely generated groups, which is where its known candidates
live in any case.

This does not decide the question.  It says the general case follows from the
finitely generated one.
-/

namespace NonsoficGroupsExist

open scoped Pointwise

variable {G : Type} [Group G]

/-- **Soficity is local**, by the same extension as for hyperlinearity. -/
theorem isSofic_of_local
    (h : ∀ F : Finset G, ∃ (H : Type) (_ : Group H) (ι : H →* G),
      Function.Injective ι ∧ IsSofic H ∧ ∀ g ∈ F, g ∈ Set.range ι) :
    IsSofic G := by
  classical
  intro F ε hε
  obtain ⟨H, _, ι, hinj, hH, hcov⟩ := h F
  set ψ : G → H := Function.invFun ι with hψ
  have hψι : ∀ x : H, ψ (ι x) = x := fun x ↦ Function.leftInverse_invFun hinj x
  have hιψ : ∀ g ∈ Set.range ι, ι (ψ g) = g := by
    rintro g ⟨x, rfl⟩
    rw [hψι]
  set F' : Finset H := F.image ψ with hF'
  obtain ⟨M⟩ := hH F' ε hε
  have hmemF' : ∀ g ∈ F, ψ g ∈ F' := fun g hg ↦ Finset.mem_image_of_mem ψ hg
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := fun g ↦ if g ∈ Set.range ι then M.map (ψ g) else 1
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h hh
    have hgr : g ∈ Set.range ι := hcov g hg
    have hhr : h ∈ Set.range ι := hcov h hh
    have hghr : g * h ∈ Set.range ι := by
      obtain ⟨a, rfl⟩ := hgr
      obtain ⟨b, rfl⟩ := hhr
      exact ⟨a * b, by rw [map_mul]⟩
    have hpsi : ψ (g * h) = ψ g * ψ h := by
      apply hinj
      rw [hιψ _ hghr, map_mul, hιψ _ hgr, hιψ _ hhr]
    simp only [if_pos hgr, if_pos hhr, if_pos hghr, hpsi]
    exact M.multiplicative _ (hmemF' g hg) _ (hmemF' h hh)
  · intro g hg h hh hne
    have hgr : g ∈ Set.range ι := hcov g hg
    have hhr : h ∈ Set.range ι := hcov h hh
    simp only [if_pos hgr, if_pos hhr]
    refine M.separated _ (hmemF' g hg) _ (hmemF' h hh) ?_
    intro hcon
    exact hne (by rw [← hιψ _ hgr, ← hιψ _ hhr, hcon])

/-- **Question 3.4 reduces to finitely generated groups.**  If every finitely
generated hyperlinear group is sofic, then every hyperlinear group is sofic. -/
theorem isSofic_of_isHyperlinear_of_fg_case
    (hfg : ∀ (H : Type) (_ : Group H), Group.FG H → IsHyperlinear H → IsSofic H)
    (hG : IsHyperlinear G) : IsSofic G := by
  classical
  refine isSofic_of_local (fun F ↦ ?_)
  refine ⟨↥(Subgroup.closure (F : Set G)), inferInstance,
    (Subgroup.closure (F : Set G)).subtype, Subgroup.subtype_injective _, ?_, ?_⟩
  · refine hfg _ _ ?_ (isHyperlinear_of_injective _
      (Subgroup.subtype_injective _) hG)
    rw [Group.fg_iff]
    refine ⟨((↑) : Subgroup.closure (F : Set G) → G) ⁻¹' (F : Set G), ?_, ?_⟩
    · exact Subgroup.closure_closure_coe_preimage
    · exact Set.Finite.preimage
        (Set.injOn_of_injective (Subgroup.subtype_injective _)) F.finite_toSet
  · intro g hg
    exact ⟨⟨g, Subgroup.subset_closure hg⟩, rfl⟩


/-! ## The two useful forms of the reduction

The reduction is worth stating twice more, because the forms one reaches for are
different from the form one proves.

As an *equivalence*: Question 3.4 holds in general exactly when it holds for
finitely generated groups.  One direction is the reduction; the other is
immediate, a finitely generated group being a group.

As a statement about *counterexamples*: a counterexample exists exactly when a
finitely generated one does.  This is the contrapositive, and it is the form a
search would use -- it says a hunt may restrict to finitely generated groups
without loss, which is not obvious from the definitions since neither property is
visibly inherited upward.
-/

/-- **Question 3.4 is equivalent to its finitely generated case.** -/
theorem isHyperlinear_imp_isSofic_iff_fg :
    (∀ (H : Type) (_ : Group H), Group.FG H → IsHyperlinear H → IsSofic H)
      ↔ (∀ (H : Type) (_ : Group H), IsHyperlinear H → IsSofic H) := by
  constructor
  · intro hfg H _ hH
    exact isSofic_of_isHyperlinear_of_fg_case hfg hH
  · intro hall H _ _ hH
    exact hall H inferInstance hH

/-- **A counterexample exists exactly when a finitely generated one does.**  The
contrapositive of the reduction: a search for a hyperlinear nonsofic group may
restrict to finitely generated groups without loss. -/
theorem exists_counterexample_iff_exists_fg :
    (∃ (H : Type) (_ : Group H), IsHyperlinear H ∧ ¬ IsSofic H)
      ↔ (∃ (H : Type) (_ : Group H), Group.FG H ∧ IsHyperlinear H
          ∧ ¬ IsSofic H) := by
  constructor
  · rintro ⟨G, hG, hhyp, hnsofic⟩
    by_contra hcon
    refine hnsofic (isSofic_of_isHyperlinear_of_fg_case ?_ hhyp)
    intro H hH hfg hhypH
    by_contra hns
    exact hcon ⟨H, hH, hfg, hhypH, hns⟩
  · rintro ⟨H, hH, _, hhyp, hns⟩
    exact ⟨H, hH, hhyp, hns⟩

/-! ## The profile of a counterexample

Assembling what is already proved, a hyperlinear nonsofic group -- if one exists
-- is constrained on several sides at once, and the constraints are worth having
in one place.

It may be taken finitely generated, by the reduction above.  It is not locally
embeddable into finite groups, since `isSofic_of_isLEF` would make it sofic; a
fortiori it is not residually finite, by `isLEF_of_residuallyFinite`; and it is
infinite, a finite group being residually finite.  What it must *also* be is
non-amenable, since amenable groups are sofic -- that step is quoted, not proved
here, and it is the one that puts the known candidate constructions out of reach.
-/

/-- Residual finiteness implies soficity, through local embeddability. -/
theorem isSofic_of_residuallyFinite [Group.ResiduallyFinite G] : IsSofic G :=
  isSofic_of_isLEF isLEF_of_residuallyFinite

/-- **A counterexample is not locally embeddable into finite groups**, hence not
residually finite. -/
theorem not_isLEF_of_hyperlinear_not_isSofic (hns : ¬ IsSofic G) : ¬ IsLEF G :=
  fun hlef ↦ hns (isSofic_of_isLEF hlef)

/-- **A counterexample may be taken finitely generated and non-residually-finite.**
The full profile in one statement: the reduction supplies the generation
hypothesis, and residual finiteness would supply soficity. -/
theorem exists_counterexample_iff_exists_fg_not_residuallyFinite :
    (∃ (H : Type) (_ : Group H), IsHyperlinear H ∧ ¬ IsSofic H)
      ↔ (∃ (H : Type) (_ : Group H), Group.FG H ∧ IsHyperlinear H
          ∧ ¬ IsSofic H ∧ ¬ IsLEF H) := by
  rw [exists_counterexample_iff_exists_fg]
  constructor
  · rintro ⟨H, hH, hfg, hhyp, hns⟩
    exact ⟨H, hH, hfg, hhyp, hns, not_isLEF_of_hyperlinear_not_isSofic hns⟩
  · rintro ⟨H, hH, hfg, hhyp, hns, _⟩
    exact ⟨H, hH, hfg, hhyp, hns⟩

/-! ## Monotonicity in the accuracy

Both local definitions quantify over all positive `ε`, and both model types get
weaker as `ε` grows -- multiplicativity is an upper bound on the defect and
separation a lower bound of the form `1 - ε` or `2 - ε`.  So a model at one
accuracy is a model at every worse accuracy, and it is enough to test the
definitions on any set of accuracies accumulating at `0`.

Cheap, but worth having: without it the definitions look as though they might
depend on which `ε` are tested, and several arguments below quietly need that
they do not.
-/

/-- A sofic model is a model at any worse accuracy. -/
def SoficModel.mono {F : Finset G} {ε ε' : ℝ} (h : ε ≤ ε')
    (M : SoficModel G F ε) : SoficModel G F ε' where
  carrier := M.carrier
  nonempty := M.nonempty
  map := M.map
  multiplicative := fun g hg h' hh ↦ le_trans (M.multiplicative g hg h' hh) h
  separated := fun g hg h' hh hne ↦
    le_trans (by linarith) (M.separated g hg h' hh hne)

/-- A hyperlinear model is a model at any worse accuracy. -/
def HyperlinearModel.mono {F : Finset G} {ε ε' : ℝ} (h : ε ≤ ε')
    (M : HyperlinearModel G F ε) : HyperlinearModel G F ε' where
  carrier := M.carrier
  nonempty := M.nonempty
  map := M.map
  isUnitary := M.isUnitary
  multiplicative := fun g hg h' hh ↦ le_trans (M.multiplicative g hg h' hh) h
  separated := fun g hg h' hh hne ↦
    le_trans (by linarith) (M.separated g hg h' hh hne)

/-- **Soficity may be tested on any accuracies accumulating at `0`.** -/
theorem isSofic_of_forall_small (h : ∀ (F : Finset G) (n : ℕ),
    Nonempty (SoficModel G F (1 / (n + 1 : ℝ)))) : IsSofic G := by
  intro F ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  obtain ⟨M⟩ := h F n
  refine ⟨M.mono ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hn0]
  rw [div_lt_iff₀ hε] at hn
  nlinarith [hn, hε]

/-- **Hyperlinearity may be tested on any accuracies accumulating at `0`.** -/
theorem isHyperlinear_of_forall_small (h : ∀ (F : Finset G) (n : ℕ),
    Nonempty (HyperlinearModel G F (1 / (n + 1 : ℝ)))) : IsHyperlinear G := by
  intro F ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  obtain ⟨M⟩ := h F n
  refine ⟨M.mono ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hn0]
  rw [div_lt_iff₀ hε] at hn
  nlinarith [hn, hε]

/-! ## The textbook convention for hyperlinearity

`isSofic_iff_productRestricted` records that requiring multiplicativity for all
pairs in the test set is the same as requiring it only when the product remains
in the set -- the textbook convention -- because one may enlarge `F` by `F * F`.
The hyperlinear side had no such statement, and it should, since the manuscript's
results are stated against the unrestricted convention while the literature uses
the restricted one.

The argument is the sofic one verbatim: nothing about the metric enters, only
that enlarging the test set makes the hypothesis stronger and the products
available.
-/

/-- The textbook local hyperlinear model, with multiplicativity required only
when the tested product remains in the finite test set. -/
structure ProductRestrictedHyperlinearModel (G : Type*) [Group G]
    (F : Finset G) (ε : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Matrix carrier carrier ℂ
  isUnitary : ∀ g, map g ∈ Matrix.unitaryGroup carrier ℂ
  multiplicative : ∀ g ∈ F, ∀ h ∈ F, g * h ∈ F →
    hsDistSq carrier (map (g * h)) (map g * map h) ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    2 - ε ≤ hsDistSq carrier (map g) (map h)

/-- Hyperlinearity in the product-restricted textbook convention. -/
def IsHyperlinearProductRestricted (G : Type*) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε →
    Nonempty (ProductRestrictedHyperlinearModel G F ε)

/-- **The two conventions agree**, by the same enlargement that settles the
sofic case. -/
theorem isHyperlinear_iff_productRestricted (G : Type*) [Group G] :
    IsHyperlinear G ↔ IsHyperlinearProductRestricted G := by
  classical
  constructor
  · intro h F ε hε
    obtain ⟨M⟩ := h F ε hε
    exact ⟨{
      carrier := M.carrier
      nonempty := M.nonempty
      map := M.map
      isUnitary := M.isUnitary
      multiplicative := fun g hg h hh _ ↦ M.multiplicative g hg h hh
      separated := M.separated }⟩
  · intro h F ε hε
    let T : Finset G := F ∪ F * F
    obtain ⟨M⟩ := h T ε hε
    refine ⟨{
      carrier := M.carrier
      nonempty := M.nonempty
      map := M.map
      isUnitary := M.isUnitary
      multiplicative := ?_
      separated := ?_ }⟩
    · intro g hg h hh
      exact M.multiplicative g (by simp [T, hg]) h (by simp [T, hh])
        (Finset.mem_union_right F (Finset.mul_mem_mul hg hh))
    · intro g hg h hh hgh
      exact M.separated g (by simp [T, hg]) h (by simp [T, hh]) hgh

/-- A closed witness, so `IsHyperlinearProductRestricted` is not a certificate
nothing satisfies: the trivial group. -/
theorem isHyperlinearProductRestricted_trivial :
    IsHyperlinearProductRestricted (PUnit : Type) :=
  (isHyperlinear_iff_productRestricted (PUnit : Type)).mp
    (isHyperlinear_of_finite (PUnit : Type))

/-! ## The separation constant: where the two sides part

The other convention is the separation constant.  On the sofic side it is
immaterial: `isSofic_iff_weak` shows that pinning separation at any fixed
`δ ∈ (0,1)` gives the same class, tensor powers driving a fixed separation to the
maximum while multiplying the defect only by the number of factors.

On the unitary side only one direction is available here, and that is not an
omission.  The easy direction is below.  Its converse is exactly what
amplification would supply, and `tensorPow_phase_collapse` shows amplification
cannot: `1` and `i·1` are unitary, maximally separated, and have equal fourth
tensor powers, so the tensor power does not preserve separation of unitaries at
all.  The converse does hold -- by Rădulescu's theorem, via the embedding of the
group von Neumann algebra into `R^ω` -- but that is a von Neumann algebra
theorem, quoted and not proved here.

So the definitional API is asymmetric, and the asymmetry is the one this
development is about: the multiplicativity convention is immaterial on both
sides, the separation constant is immaterial on the sofic side, and on the
unitary side it is immaterial only by a theorem no elementary argument replaces.
-/

/-- A hyperlinear model with separation pinned at a constant `δ` rather than
driven to the maximum. -/
structure WeakHyperlinearModel (G : Type*) [Group G] (F : Finset G) (δ ε : ℝ) where
  carrier : FiniteModel
  nonempty : 0 < Fintype.card carrier
  map : G → Matrix carrier carrier ℂ
  isUnitary : ∀ g, map g ∈ Matrix.unitaryGroup carrier ℂ
  multiplicative : ∀ g ∈ F, ∀ h ∈ F,
    hsDistSq carrier (map (g * h)) (map g * map h) ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    δ ≤ hsDistSq carrier (map g) (map h)

/-- Hyperlinearity with the separation pinned at a constant `δ`. -/
def IsHyperlinearWeak (G : Type*) [Group G] (δ : ℝ) : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (WeakHyperlinearModel G F δ ε)

/-- **The easy direction.**  A model separated to `2 - ε` is separated to any
fixed `δ < 2`, once `ε` is small enough -- and `ε` is ours to shrink. -/
theorem isHyperlinearWeak_of_isHyperlinear {δ : ℝ} (hδ : δ < 2)
    (h : IsHyperlinear G) : IsHyperlinearWeak G δ := by
  intro F ε hε
  obtain ⟨M⟩ := h F (min ε (2 - δ)) (lt_min hε (by linarith))
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := M.map
    isUnitary := M.isUnitary
    multiplicative := fun g hg h' hh ↦
      le_trans (M.multiplicative g hg h' hh) (min_le_left _ _)
    separated := ?_ }⟩
  intro g hg h' hh hne
  refine le_trans ?_ (M.separated g hg h' hh hne)
  have := min_le_right ε (2 - δ)
  linarith

/-- A closed weak model, so `WeakHyperlinearModel` is not a certificate nothing
satisfies: the one-point model of the trivial group, exact on both counts, with
separation vacuous because the test set is a subsingleton. -/
def trivialWeakHyperlinearModel (F : Finset PUnit) (δ : ℝ) :
    WeakHyperlinearModel PUnit F δ 0 where
  carrier := ⟨PUnit, inferInstance, inferInstance⟩
  nonempty := by simp
  map := fun _ ↦ 1
  isUnitary := fun _ ↦ Submonoid.one_mem _
  multiplicative := by
    intro g _ h _
    simp [hsDistSq]
  separated := by
    intro g _ h _ hne
    exact absurd (Subsingleton.elim g h) hne

/-- A closed witness, so `IsHyperlinearWeak` is not a certificate nothing
satisfies. -/
theorem isHyperlinearWeak_trivial_one :
    IsHyperlinearWeak (PUnit : Type) 1 :=
  isHyperlinearWeak_of_isHyperlinear (by norm_num)
    (isHyperlinear_of_finite (PUnit : Type))

end NonsoficGroupsExist
