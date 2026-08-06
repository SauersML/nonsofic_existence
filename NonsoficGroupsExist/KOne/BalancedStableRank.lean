import NonsoficGroupsExist.Leavitt.LeavittDegreeZero
import NonsoficGroupsExist.KOne.StableRankOne

/-!
# Stable rank one inside the balanced subalgebra

The balanced span at depth `n` is the isomorphic image of the scalar
matrix algebra `M_{2ⁿ}(k)` under the prefix-code identification, so
the stable-rank-one pivot of `StableRankOne` transports: a balanced
unimodular pair `a·z₀ + b·z₁ = 1` admits a balanced `t` with `a + b·t`
invertible with balanced inverse.  This produces the invertible pivots
for the residual-class endgame.
-/

namespace NonsoficGroupsExist
namespace LeavittFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] (L : LeavittFamily A)
variable {k : Type*} [Field k] [Algebra k A]

/-- The scalar-matrix embedding at depth `n`. -/
noncomputable def balancedEmbed (n : ℕ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) k →+* A :=
  ((L.prefixMatrixFamily (fullBinaryCode n)
      (L.fullBinaryCode_complete n)).matrixRingEquiv.toRingHom).comp
    (algebraMap k A).mapMatrix

theorem balancedEmbed_mem_span (n : ℕ)
    (C : Matrix (Fin n → Fin 2) (Fin n → Fin 2) k) :
    L.balancedEmbed (k := k) n C ∈
      Submodule.span k (L.levelMonomials n) := by
  show (L.prefixMatrixFamily (fullBinaryCode n)
      (L.fullBinaryCode_complete n)).matrixRingEquiv
      ((algebraMap k A).mapMatrix C) ∈ _
  rw [CompleteMatrixFamily.matrixRingEquiv_apply]
  refine Submodule.sum_mem _ fun γ _ ↦ Submodule.sum_mem _ fun δ _ ↦ ?_
  have hterm : (L.prefixMatrixFamily (fullBinaryCode n)
        (L.fullBinaryCode_complete n)).left γ *
        ((algebraMap k A).mapMatrix C γ δ) *
        (L.prefixMatrixFamily (fullBinaryCode n)
          (L.fullBinaryCode_complete n)).right δ =
      C γ δ • (L.wordS (List.ofFn γ) * L.wordT (List.ofFn δ)) := by
    show L.wordS (List.ofFn γ) * (algebraMap k A (C γ δ)) *
      L.wordT (List.ofFn δ) = _
    rw [show L.wordS (List.ofFn γ) * (algebraMap k A (C γ δ)) =
      algebraMap k A (C γ δ) * L.wordS (List.ofFn γ) from
        (Algebra.commutes _ _).symm, mul_assoc, ← Algebra.smul_def]
  rw [hterm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, δ, rfl⟩)

theorem exists_balancedEmbed_eq {n : ℕ} {x : A}
    (hx : x ∈ Submodule.span k (L.levelMonomials n)) :
    ∃ C, L.balancedEmbed (k := k) n C = x := by
  classical
  have hentry : ∀ γ δ : Fin n → Fin 2, ∃ c : k,
      algebraMap k A c = (L.prefixMatrixFamily (fullBinaryCode n)
          (L.fullBinaryCode_complete n)).right γ * x *
        (L.prefixMatrixFamily (fullBinaryCode n)
          (L.fullBinaryCode_complete n)).left δ := by
    intro γ δ
    obtain ⟨c, hc⟩ := L.entry_mem_range_algebraMap n hx γ δ
    exact ⟨c, hc⟩
  choose C hC using hentry
  refine ⟨Matrix.of C, ?_⟩
  have hmat : (algebraMap k A).mapMatrix (Matrix.of C) =
      (L.prefixMatrixFamily (fullBinaryCode n)
        (L.fullBinaryCode_complete n)).matrixRingEquiv.symm x := by
    ext γ δ
    rw [CompleteMatrixFamily.matrixRingEquiv_symm_apply]
    exact hC γ δ
  show (L.prefixMatrixFamily (fullBinaryCode n)
      (L.fullBinaryCode_complete n)).matrixRingEquiv
      ((algebraMap k A).mapMatrix (Matrix.of C)) = x
  rw [hmat, RingEquiv.apply_symm_apply]

theorem balancedEmbed_injective [Nontrivial A] (n : ℕ) :
    Function.Injective (L.balancedEmbed (k := k) n) := by
  intro C D h
  have h2 : (algebraMap k A).mapMatrix C =
      (algebraMap k A).mapMatrix D :=
    (L.prefixMatrixFamily (fullBinaryCode n)
      (L.fullBinaryCode_complete n)).matrixRingEquiv.injective h
  ext γ δ
  have h3 := congrArg (fun M : Matrix (Fin n → Fin 2)
    (Fin n → Fin 2) A ↦ M γ δ) h2
  exact (algebraMap k A).injective h3

/-- **Balanced stable-rank-one pivot**: a balanced unimodular pair
admits a balanced perturbation making it a unit with balanced
inverse. -/
theorem exists_balanced_sr1_pivot [Nontrivial A] {n : ℕ}
    {a b z₀ z₁ : A}
    (ha : a ∈ Submodule.span k (L.levelMonomials n))
    (hb : b ∈ Submodule.span k (L.levelMonomials n))
    (hz₀ : z₀ ∈ Submodule.span k (L.levelMonomials n))
    (hz₁ : z₁ ∈ Submodule.span k (L.levelMonomials n))
    (h : a * z₀ + b * z₁ = 1) :
    ∃ t ∈ Submodule.span k (L.levelMonomials n), ∃ u : Aˣ,
      (u : A) = a + b * t ∧
      ((u⁻¹ : Aˣ) : A) ∈ Submodule.span k (L.levelMonomials n) := by
  obtain ⟨Ca, hCa⟩ := L.exists_balancedEmbed_eq ha
  obtain ⟨Cb, hCb⟩ := L.exists_balancedEmbed_eq hb
  obtain ⟨Cz₀, hCz₀⟩ := L.exists_balancedEmbed_eq hz₀
  obtain ⟨Cz₁, hCz₁⟩ := L.exists_balancedEmbed_eq hz₁
  have hmat : Ca * Cz₀ + Cb * Cz₁ = 1 := by
    apply L.balancedEmbed_injective (k := k) n
    rw [map_add, map_mul, map_mul, map_one, hCa, hCb, hCz₀, hCz₁, h]
  obtain ⟨T, hT⟩ := exists_isUnit_add_mul_of_unimodular Ca Cb Cz₀ Cz₁
    hmat
  refine ⟨L.balancedEmbed n T, L.balancedEmbed_mem_span n T,
    Units.map (L.balancedEmbed (k := k) n).toMonoidHom hT.unit, ?_, ?_⟩
  · show (L.balancedEmbed (k := k) n) (hT.unit : Matrix _ _ k) =
      a + b * L.balancedEmbed n T
    rw [IsUnit.unit_spec, map_add, map_mul, hCa, hCb]
  · rw [← map_inv]
    show (L.balancedEmbed (k := k) n)
      ((hT.unit⁻¹ : (Matrix (Fin n → Fin 2) (Fin n → Fin 2) k)ˣ) :
        Matrix (Fin n → Fin 2) (Fin n → Fin 2) k) ∈ _
    exact L.balancedEmbed_mem_span n _

end LeavittFamily
end NonsoficGroupsExist
