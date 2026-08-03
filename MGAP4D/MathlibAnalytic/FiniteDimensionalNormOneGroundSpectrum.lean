import MGAP4D.MathlibAnalytic.FiniteDimensionalGroundExcitationSupportDecomposition
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- Positivity of the quadratic form makes every Rayleigh quotient
nonnegative. -/
theorem rayleighQuotient_nonneg (x : E) :
    0 ≤ D.operator.rayleighQuotient x := by
  by_cases hx : x = 0
  · simp [hx]
  · change 0 ≤ inner ℝ (D.operator x) x / ‖x‖ ^ 2
    exact div_nonneg (D.quadratic_nonneg x) (sq_nonneg ‖x‖)

/-- For a positive finite-dimensional symmetric operator, the supremum of the
Rayleigh quotient over nonzero vectors is exactly the operator norm. -/
theorem iSup_rayleighQuotient_nonzero_eq_norm
    [Nontrivial E] :
    (⨆ x : {x : E // x ≠ 0}, D.operator.rayleighQuotient x.1) =
      ‖D.operator‖ := by
  letI : Nonempty {x : E // x ≠ 0} := by
    obtain ⟨y, hy⟩ := exists_ne (0 : E)
    exact ⟨⟨y, hy⟩⟩
  have hBddAll :
      BddAbove (Set.range fun x : E => D.operator.rayleighQuotient x) := by
    refine ⟨‖D.operator‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans (D.operator.rayleighQuotient_le_norm x)
  have hBddNonzero :
      BddAbove
        (Set.range fun x : {x : E // x ≠ 0} =>
          D.operator.rayleighQuotient x.1) := by
    refine ⟨‖D.operator‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact (le_abs_self _).trans
      (D.operator.rayleighQuotient_le_norm x.1)
  have hAll_eq_nonzero :
      (⨆ x : E, D.operator.rayleighQuotient x) =
        ⨆ x : {x : E // x ≠ 0}, D.operator.rayleighQuotient x.1 := by
    apply le_antisymm
    · refine ciSup_le ?_
      intro x
      by_cases hx : x = 0
      · subst x
        rw [ContinuousLinearMap.rayleighQuotient_apply_zero]
        let y : {x : E // x ≠ 0} := Classical.choice inferInstance
        exact (D.rayleighQuotient_nonneg y.1).trans
          (le_ciSup hBddNonzero y)
      · exact le_ciSup hBddNonzero ⟨x, hx⟩
    · refine ciSup_le ?_
      intro x
      exact le_ciSup hBddAll x.1
  calc
    (⨆ x : {x : E // x ≠ 0}, D.operator.rayleighQuotient x.1) =
        ⨆ x : E, D.operator.rayleighQuotient x :=
      hAll_eq_nonzero.symm
    _ = ⨆ x : E, |D.operator.rayleighQuotient x| := by
      congr 1
      funext x
      exact (abs_of_nonneg (D.rayleighQuotient_nonneg x)).symm
    _ = ‖D.operator‖ :=
      (D.operator.norm_eq_iSup_rayleighQuotient D.symmetric).symm

/-- A norm-one finite-dimensional symmetric positive contraction has at least
one canonical eigenmode with transfer eigenvalue one. -/
theorem nonempty_groundSpectralIndex_of_norm_eq_one
    [Nontrivial E]
    (hnorm : ‖D.operator‖ = 1) :
    Nonempty D.GroundSpectralIndex := by
  have htop :
      (⨆ x : {x : E // x ≠ 0}, D.operator.rayleighQuotient x.1) = 1 := by
    rw [D.iSup_rayleighQuotient_nonzero_eq_norm, hnorm]
  have heigen : Module.End.HasEigenvalue D.operator.toLinearMap (1 : ℝ) := by
    have h := D.symmetric.hasEigenvalue_iSup_of_finiteDimensional
    rw [htop] at h
    exact h
  obtain ⟨i, hi⟩ :=
    D.symmetric.exists_eigenvalues_eq (by rfl) heigen
  exact ⟨⟨i, by simpa [eigenvalue] using hi⟩⟩

/-- Norm one therefore gives a nonzero ground vector synthesized in the
original Hilbert space. -/
theorem exists_nonzero_groundSpectralSynthesis_of_norm_eq_one
    [Nontrivial E]
    (hnorm : ‖D.operator‖ = 1) :
    ∃ x : D.GroundSpectralSpace,
      D.groundSpectralSynthesis x ≠ 0 := by
  let i : D.GroundSpectralIndex :=
    Classical.choice (D.nonempty_groundSpectralIndex_of_norm_eq_one hnorm)
  let x : D.GroundSpectralSpace :=
    WithLp.toLp 2 (Pi.single i (1 : ℝ))
  refine ⟨x, ?_⟩
  intro hx
  have hzero : x = 0 :=
    D.groundSpectralSynthesis_injective
      (show D.groundSpectralSynthesis x = D.groundSpectralSynthesis 0 by
        simpa using hx)
  have hi := congrArg (fun z : D.GroundSpectralSpace => z i) hzero
  simpa [x] using hi

end FiniteDimensionalSymmetricPositiveContractionData

end

end MathlibAnalytic
end MGAP4D
