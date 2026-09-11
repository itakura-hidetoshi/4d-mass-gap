import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCommutingIdempotentAnnihilatingPolynomialL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The scalar falling factorial associated with the operator polynomial

`T (T - I) ... (T - n I)`

when `T` acts on an eigenvector of eigenvalue `lam`. -/
def realFallingFactorialEigenvalueL2 (lam : ℝ) : ℕ → ℝ
  | 0 => lam
  | n + 1 =>
      (lam - ((n + 1 : ℕ) : ℝ)) * realFallingFactorialEigenvalueL2 lam n

@[simp]
theorem realFallingFactorialEigenvalueL2_zero
    (lam : ℝ) :
    realFallingFactorialEigenvalueL2 lam 0 = lam := by
  rfl

@[simp]
theorem realFallingFactorialEigenvalueL2_succ
    (lam : ℝ)
    (n : ℕ) :
    realFallingFactorialEigenvalueL2 lam (n + 1) =
      (lam - ((n + 1 : ℕ) : ℝ)) *
        realFallingFactorialEigenvalueL2 lam n := by
  rfl

/-- On an eigenvector, the operator falling factorial is exactly scalar
multiplication by the corresponding scalar falling factorial. -/
theorem continuousLinearMapFallingFactorialL2_apply_of_eigenvector
    (T : V →L[ℝ] V)
    {lam : ℝ}
    {f : V}
    (hEigen : T f = lam • f)
    (n : ℕ) :
    continuousLinearMapFallingFactorialL2 T n f =
      realFallingFactorialEigenvalueL2 lam n • f := by
  induction n with
  | zero =>
      simpa [continuousLinearMapFallingFactorialL2,
        realFallingFactorialEigenvalueL2] using hEigen
  | succ n ih =>
      rw [continuousLinearMapFallingFactorialL2_succ_apply, ih,
        map_smul, hEigen, realFallingFactorialEigenvalueL2_succ,
        smul_smul, smul_smul]
      module

/-- The real roots of the degree-`n + 1` scalar falling factorial are exactly
`0, 1, ..., n`. -/
theorem realFallingFactorialEigenvalueL2_eq_zero_iff
    (lam : ℝ)
    (n : ℕ) :
    realFallingFactorialEigenvalueL2 lam n = 0 ↔
      ∃ k : ℕ, k ≤ n ∧ lam = (k : ℝ) := by
  induction n with
  | zero =>
      rw [realFallingFactorialEigenvalueL2_zero]
      constructor
      · intro hZero
        exact ⟨0, Nat.zero_le 0, by simpa using hZero⟩
      · rintro ⟨k, hk, hLam⟩
        have hkZero : k = 0 := by omega
        simpa [hkZero] using hLam
  | succ n ih =>
      rw [realFallingFactorialEigenvalueL2_succ, mul_eq_zero, ih]
      constructor
      · rintro (hLast | ⟨k, hk, hLam⟩)
        · refine ⟨n + 1, Nat.le_refl (n + 1), ?_⟩
          exact sub_eq_zero.mp hLast
        · exact ⟨k, Nat.le_trans hk (Nat.le_succ n), hLam⟩
      · rintro ⟨k, hk, hLam⟩
        by_cases hLast : k = n + 1
        · left
          rw [hLam, hLast]
          exact sub_self _
        · right
          refine ⟨k, ?_, hLam⟩
          omega

/-- If the degree-`n + 1` operator falling factorial annihilates an
endomorphism, every genuine real eigenvalue is a natural number between zero
and `n`.  No finite-dimensionality or compactness is required. -/
theorem continuousLinearMapFallingFactorialL2_eigenvalue_eq_nat_cast_le
    (T : V →L[ℝ] V)
    (n : ℕ)
    (hAnnihilates : continuousLinearMapFallingFactorialL2 T n = 0)
    {lam : ℝ}
    {f : V}
    (hf : f ≠ 0)
    (hEigen : T f = lam • f) :
    ∃ k : ℕ, k ≤ n ∧ lam = (k : ℝ) := by
  have hApply : continuousLinearMapFallingFactorialL2 T n f = 0 := by
    rw [hAnnihilates]
    rfl
  rw [continuousLinearMapFallingFactorialL2_apply_of_eigenvector
      T hEigen n] at hApply
  have hNormProduct :
      ‖realFallingFactorialEigenvalueL2 lam n‖ * ‖f‖ = 0 := by
    have hNorm := congrArg norm hApply
    simpa [norm_smul] using hNorm
  have hfNormPos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hScalarNorm : ‖realFallingFactorialEigenvalueL2 lam n‖ = 0 :=
    (mul_eq_zero.mp hNormProduct).resolve_right (ne_of_gt hfNormPos)
  have hScalar : realFallingFactorialEigenvalueL2 lam n = 0 :=
    norm_eq_zero.mp hScalarNorm
  exact
    (realFallingFactorialEigenvalueL2_eq_zero_iff lam n).mp hScalar

/-- The finite real grid of possible heat-bath point-spectrum values supplied
by the degree-`325` annihilating polynomial. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 :
    Set ℝ :=
  Set.range fun k : Fin 325 => (k.1 : ℝ)

/-- Every actual beta-zero heat-bath point-spectrum value is an integer between
zero and `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_nat_cast_le_324
    {lam : ℝ}
    (hlam : lam ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2) :
    ∃ k : ℕ, k ≤ 324 ∧ lam = (k : ℝ) := by
  change ∃ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    f ≠ 0 ∧
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f =
        lam • f at hlam
  rcases hlam with ⟨f, hf, hEigen⟩
  exact
    continuousLinearMapFallingFactorialL2_eigenvalue_eq_nat_cast_le
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
      324
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_fallingFactorial_324_eq_zero
      hf hEigen

/-- The actual beta-zero heat-bath point spectrum is contained in the finite
integer grid `{0, 1, ..., 324}`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_subset_allowed_integer_grid :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 ⊆
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 := by
  intro lam hlam
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_nat_cast_le_324
        hlam with
    ⟨k, hk, hLam⟩
  change ∃ j : Fin 325, (j.1 : ℝ) = lam
  refine ⟨⟨k, ?_⟩, hLam.symm⟩
  omega

/-- Every nonzero actual beta-zero heat-bath point-spectrum value is a positive
integer between one and `324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nonzero_heatBathPointSpectrumL2_eq_nat_cast_between_one_and_324
    {lam : ℝ}
    (hlam : lam ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 \
        ({0} : Set ℝ)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 324 ∧ lam = (k : ℝ) := by
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_eq_nat_cast_le_324
        hlam.1 with
    ⟨k, hk, hLam⟩
  have hLamNe : lam ≠ 0 := by
    intro hZero
    apply hlam.2
    simpa [hZero]
  have hkPos : 1 ≤ k := by
    by_contra hkNot
    have hkZero : k = 0 := by omega
    apply hLamNe
    simpa [hkZero] using hLam
  exact ⟨k, hkPos, hk, hLam⟩

/-- The finite affine grid of possible centered random-scan point-spectrum
values inherited from the heat-bath integer grid. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedCenteredRandomScanPointSpectrumL2 :
    Set ℝ :=
  {rho | ∃ k : ℕ,
    1 ≤ k ∧ k ≤ 324 ∧ rho = 1 - (k : ℝ) / 324}

/-- Every actual centered beta-zero random-scan point-spectrum value belongs to
`{1 - k / 324 | 1 ≤ k ≤ 324}`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_subset_allowed_affine_integer_grid :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 ⊆
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedCenteredRandomScanPointSpectrumL2 := by
  intro rho hrho
  have hHeatBath :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_to_nonzero_heatBathPointSpectrumL2
      hrho
  rcases
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_nonzero_heatBathPointSpectrumL2_eq_nat_cast_between_one_and_324
        hHeatBath with
    ⟨k, hkPos, hkBound, hAffine⟩
  refine ⟨k, hkPos, hkBound, ?_⟩
  nlinarith

/-- Compact receipt for the finite integer-grid containment of the actual
beta-zero heat-bath and centered random-scan point spectra. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroPointSpectrumIntegerGridL2Receipt :
    Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathPointSpectrumL2 ⊆
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedHeatBathPointSpectrumL2 ∧
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.centeredRandomScanPointSpectrumL2 ⊆
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroAllowedCenteredRandomScanPointSpectrumL2

/-- The actual beta-zero point-spectrum integer-grid receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroPointSpectrumIntegerGridL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroPointSpectrumIntegerGridL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathPointSpectrumL2_subset_allowed_integer_grid,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeredRandomScanPointSpectrumL2_subset_allowed_affine_integer_grid⟩

end

end MathlibAnalytic
end MGAP4D
