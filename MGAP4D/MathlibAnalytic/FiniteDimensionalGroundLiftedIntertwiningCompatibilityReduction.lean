import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricPositiveContractionGroundLiftedDefect
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- The finite-dimensional ground-sector correction added to the ordinary
transfer defect.  By definition

`groundLiftedDefect = (I - operator) + groundLiftCorrection`.

Modewise this correction is the identity on transfer-fixed modes and zero on
strictly excited and null modes. -/
noncomputable def groundLiftCorrection : E →L[ℝ] E :=
  D.groundLiftedDefect -
    (ContinuousLinearMap.id ℝ E - D.operator)

/-- Exact basis-free splitting of the ground-lifted defect into ordinary
transfer defect plus the ground-sector correction. -/
theorem groundLiftedDefect_eq_transferDefect_add_groundLiftCorrection :
    D.groundLiftedDefect =
      (ContinuousLinearMap.id ℝ E - D.operator) + D.groundLiftCorrection := by
  apply ContinuousLinearMap.ext
  intro x
  simp [groundLiftCorrection]

/-- On every fixed transfer eigenmode the correction is exactly the identity. -/
theorem groundLiftCorrection_apply_ground
    (i : D.GroundSpectralIndex) :
    D.groundLiftCorrection (D.eigenbasis i.1) = D.eigenbasis i.1 := by
  change
    D.groundLiftedDefect (D.eigenbasis i.1) -
        (D.eigenbasis i.1 - D.operator (D.eigenbasis i.1)) =
      D.eigenbasis i.1
  have hOp :
      D.operator (D.eigenbasis i.1) = D.eigenbasis i.1 := by
    simpa [i.2] using D.operator_apply_eigenbasis i.1
  rw [D.groundLiftedDefect_apply_ground i, hOp]
  simp

/-- On every strictly excited mode the ground correction vanishes. -/
theorem groundLiftCorrection_apply_excited
    (i : D.ExcitedSpectralIndex) :
    D.groundLiftCorrection (D.eigenbasis i.1) = 0 := by
  change
    D.groundLiftedDefect (D.eigenbasis i.1) -
        (D.eigenbasis i.1 - D.operator (D.eigenbasis i.1)) = 0
  exact sub_eq_zero.mpr (D.groundLiftedDefect_apply_excited i)

/-- On every null mode the ground correction also vanishes. -/
theorem groundLiftCorrection_apply_null
    (i : D.NullSpectralIndex) :
    D.groundLiftCorrection (D.eigenbasis i.1) = 0 := by
  change
    D.groundLiftedDefect (D.eigenbasis i.1) -
        (D.eigenbasis i.1 - D.operator (D.eigenbasis i.1)) = 0
  exact sub_eq_zero.mpr (D.groundLiftedDefect_apply_null i)

/-- Audit-visible spectral characterization of the correction: it is one on
the ground sector and zero on the excited and null sectors. -/
structure GroundLiftCorrectionPackage where
  correction : E →L[ℝ] E
  correction_eq : correction = D.groundLiftCorrection
  decomposition :
    D.groundLiftedDefect =
      (ContinuousLinearMap.id ℝ E - D.operator) + correction
  ground : ∀ i : D.GroundSpectralIndex,
    correction (D.eigenbasis i.1) = D.eigenbasis i.1
  excited : ∀ i : D.ExcitedSpectralIndex,
    correction (D.eigenbasis i.1) = 0
  null : ∀ i : D.NullSpectralIndex,
    correction (D.eigenbasis i.1) = 0

/-- Construct the exact ground-correction spectral receipt. -/
noncomputable def groundLiftCorrectionPackage :
    D.GroundLiftCorrectionPackage where
  correction := D.groundLiftCorrection
  correction_eq := rfl
  decomposition := D.groundLiftedDefect_eq_transferDefect_add_groundLiftCorrection
  ground := D.groundLiftCorrection_apply_ground
  excited := D.groundLiftCorrection_apply_excited
  null := D.groundLiftCorrection_apply_null

end FiniteDimensionalSymmetricPositiveContractionData

/-- Cross-carrier residual for the original transfer operators. -/
noncomputable def finiteDimensionalTransferIntertwiningResidualLinearMap
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  Df.operator.toLinearMap.comp J - J.comp Dc.operator.toLinearMap

/-- Cross-carrier residual for the ground-sector correction operators. -/
noncomputable def finiteDimensionalGroundCorrectionIntertwiningResidualLinearMap
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  Df.groundLiftCorrection.toLinearMap.comp J -
    J.comp Dc.groundLiftCorrection.toLinearMap

/-- Cross-carrier residual for the ground-lifted defects. -/
noncomputable def finiteDimensionalGroundLiftedIntertwiningResidualLinearMap
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  Df.groundLiftedDefect.toLinearMap.comp J -
    J.comp Dc.groundLiftedDefect.toLinearMap

/-- Exact compatibility reduction for ground-lifted defects.  Their strong
cross-carrier residual is the negative transfer residual plus the residual of
the ground-sector correction.  No separate vanishing of either summand is
assumed. -/
theorem finiteDimensionalGroundLiftedIntertwiningResidual_decomposition
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) :
    finiteDimensionalGroundLiftedIntertwiningResidualLinearMap Df Dc J =
      - finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J +
        finiteDimensionalGroundCorrectionIntertwiningResidualLinearMap
          Df Dc J := by
  apply LinearMap.ext
  intro x
  change
    Df.groundLiftedDefect (J x) - J (Dc.groundLiftedDefect x) =
      -(Df.operator (J x) - J (Dc.operator x)) +
        (Df.groundLiftCorrection (J x) -
          J (Dc.groundLiftCorrection x))
  have hf := congrArg
    (fun L : Ef →L[ℝ] Ef => L (J x))
    Df.groundLiftedDefect_eq_transferDefect_add_groundLiftCorrection
  have hc := congrArg
    (fun L : Ec →L[ℝ] Ec => L x)
    Dc.groundLiftedDefect_eq_transferDefect_add_groundLiftCorrection
  change
    Df.groundLiftedDefect (J x) =
      (J x - Df.operator (J x)) + Df.groundLiftCorrection (J x) at hf
  change
    Dc.groundLiftedDefect x =
      (x - Dc.operator x) + Dc.groundLiftCorrection x at hc
  rw [hf, hc, map_add, map_sub]
  module

/-- Pointwise form of the exact transfer-plus-ground-correction reduction. -/
theorem finiteDimensionalGroundLiftedIntertwiningResidual_decomposition_apply
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (x : Ec) :
    finiteDimensionalGroundLiftedIntertwiningResidualLinearMap Df Dc J x =
      - finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J x +
        finiteDimensionalGroundCorrectionIntertwiningResidualLinearMap
          Df Dc J x := by
  exact LinearMap.congr_fun
    (finiteDimensionalGroundLiftedIntertwiningResidual_decomposition Df Dc J) x

/-- Vanishing of both concrete compatibility residuals is a sufficient
condition for exact ground-lifted intertwining.  The converse is deliberately
not asserted because the two residuals may cancel without additional geometry. -/
theorem finiteDimensionalGroundLiftedIntertwiningResidual_eq_zero_of_components
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hTransfer :
      finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J = 0)
    (hGround :
      finiteDimensionalGroundCorrectionIntertwiningResidualLinearMap
        Df Dc J = 0) :
    finiteDimensionalGroundLiftedIntertwiningResidualLinearMap Df Dc J = 0 := by
  rw [finiteDimensionalGroundLiftedIntertwiningResidual_decomposition
    Df Dc J, hTransfer, hGround]
  simp

/-- Audit-visible generic compatibility reduction package. -/
structure FiniteDimensionalGroundLiftedCompatibilityReductionPackage
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) where
  transferResidual : Ec →ₗ[ℝ] Ef
  transferResidual_eq :
    transferResidual =
      finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J
  groundCorrectionResidual : Ec →ₗ[ℝ] Ef
  groundCorrectionResidual_eq :
    groundCorrectionResidual =
      finiteDimensionalGroundCorrectionIntertwiningResidualLinearMap Df Dc J
  groundLiftedResidual : Ec →ₗ[ℝ] Ef
  groundLiftedResidual_eq :
    groundLiftedResidual =
      finiteDimensionalGroundLiftedIntertwiningResidualLinearMap Df Dc J
  decomposition :
    groundLiftedResidual = - transferResidual + groundCorrectionResidual
  componentsSuffice :
    transferResidual = 0 → groundCorrectionResidual = 0 →
      groundLiftedResidual = 0

/-- Construct the complete generic compatibility reduction receipt. -/
noncomputable def finiteDimensionalGroundLiftedCompatibilityReductionPackage
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [InnerProductSpace ℝ Ef]
    [FiniteDimensional ℝ Ef]
    [NormedAddCommGroup Ec]
    [InnerProductSpace ℝ Ec]
    [FiniteDimensional ℝ Ec]
    (Df : FiniteDimensionalSymmetricPositiveContractionData Ef)
    (Dc : FiniteDimensionalSymmetricPositiveContractionData Ec)
    (J : Ec →ₗ[ℝ] Ef) :
    FiniteDimensionalGroundLiftedCompatibilityReductionPackage Df Dc J where
  transferResidual :=
    finiteDimensionalTransferIntertwiningResidualLinearMap Df Dc J
  transferResidual_eq := rfl
  groundCorrectionResidual :=
    finiteDimensionalGroundCorrectionIntertwiningResidualLinearMap Df Dc J
  groundCorrectionResidual_eq := rfl
  groundLiftedResidual :=
    finiteDimensionalGroundLiftedIntertwiningResidualLinearMap Df Dc J
  groundLiftedResidual_eq := rfl
  decomposition :=
    finiteDimensionalGroundLiftedIntertwiningResidual_decomposition Df Dc J
  componentsSuffice :=
    finiteDimensionalGroundLiftedIntertwiningResidual_eq_zero_of_components
      Df Dc J

end

end MathlibAnalytic
end MGAP4D
