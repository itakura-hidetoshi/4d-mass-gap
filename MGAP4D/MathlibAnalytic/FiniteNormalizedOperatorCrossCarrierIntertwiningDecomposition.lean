import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricPositiveContractionGroundLiftedDefectDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Raw cross-carrier residual for two continuous linear operators and an
arbitrary linear comparison map. -/
noncomputable def continuousLinearOperatorCrossCarrierResidualLinearMap
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (Af : Ef →L[ℝ] Ef)
    (Ac : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  Af.toLinearMap.comp J - J.comp Ac.toLinearMap

/-- Residual after independently rescaling the fine and coarse operators. -/
noncomputable def scaledContinuousLinearOperatorCrossCarrierResidualLinearMap
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (af ac : ℝ)
    (Af : Ef →L[ℝ] Ef)
    (Ac : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  (af • Af.toLinearMap).comp J - J.comp (ac • Ac.toLinearMap)

/-- Exact algebraic decomposition of a rescaled cross-carrier residual:

`R(af Af, ac Ac) = af R(Af,Ac) + (af-ac) J Ac`.

This separates the raw operator mismatch from the independent mismatch of the
two normalization scalars. -/
theorem scaledContinuousLinearOperatorCrossCarrierResidual_decomposition
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (af ac : ℝ)
    (Af : Ef →L[ℝ] Ef)
    (Ac : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef) :
    scaledContinuousLinearOperatorCrossCarrierResidualLinearMap
        af ac Af Ac J =
      af • continuousLinearOperatorCrossCarrierResidualLinearMap Af Ac J +
        (af - ac) • (J.comp Ac.toLinearMap) := by
  apply LinearMap.ext
  intro x
  change
    af • Af (J x) - J (ac • Ac x) =
      af • (Af (J x) - J (Ac x)) +
        (af - ac) • J (Ac x)
  rw [map_smul]
  module

/-- Pointwise form of the exact rescaling decomposition. -/
theorem scaledContinuousLinearOperatorCrossCarrierResidual_decomposition_apply
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (af ac : ℝ)
    (Af : Ef →L[ℝ] Ef)
    (Ac : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (x : Ec) :
    scaledContinuousLinearOperatorCrossCarrierResidualLinearMap
        af ac Af Ac J x =
      af • continuousLinearOperatorCrossCarrierResidualLinearMap Af Ac J x +
        (af - ac) • J (Ac x) := by
  exact LinearMap.congr_fun
    (scaledContinuousLinearOperatorCrossCarrierResidual_decomposition
      af ac Af Ac J) x

/-- Canonical operator-norm normalization scalar. -/
noncomputable def continuousLinearOperatorNormalizationScalar
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (A : E →L[ℝ] E) : ℝ := ‖A‖⁻¹

/-- Cross-carrier residual of the independently operator-norm-normalized raw
operators. -/
noncomputable def normalizedContinuousLinearOperatorCrossCarrierResidualLinearMap
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (Rf : Ef →L[ℝ] Ef)
    (Rc : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  scaledContinuousLinearOperatorCrossCarrierResidualLinearMap
    (continuousLinearOperatorNormalizationScalar Rf)
    (continuousLinearOperatorNormalizationScalar Rc)
    Rf Rc J

/-- Exact normalized/raw decomposition.  The second summand is the pure
normalization mismatch, and therefore cannot be hidden inside a kernel
intertwining statement. -/
theorem normalizedContinuousLinearOperatorCrossCarrierResidual_decomposition
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (Rf : Ef →L[ℝ] Ef)
    (Rc : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef) :
    normalizedContinuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J =
      ‖Rf‖⁻¹ •
          continuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J +
        (‖Rf‖⁻¹ - ‖Rc‖⁻¹) • (J.comp Rc.toLinearMap) := by
  exact scaledContinuousLinearOperatorCrossCarrierResidual_decomposition
    ‖Rf‖⁻¹ ‖Rc‖⁻¹ Rf Rc J

/-- If the raw operators intertwine and their normalization scalars agree,
then the independently normalized operators intertwine. -/
theorem normalizedContinuousLinearOperatorCrossCarrierResidual_eq_zero_of_raw_and_norm
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (Rf : Ef →L[ℝ] Ef)
    (Rc : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hRaw : continuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J = 0)
    (hNorm : ‖Rf‖ = ‖Rc‖) :
    normalizedContinuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J = 0 := by
  rw [normalizedContinuousLinearOperatorCrossCarrierResidual_decomposition,
    hRaw, hNorm]
  simp

/-- Conversely, under raw intertwining, normalized intertwining is exactly the
vanishing of the normalization-mismatch term.  No injectivity or nonzero
assumption on the comparison map is silently introduced. -/
theorem normalizedContinuousLinearOperatorCrossCarrierResidual_eq_zero_iff_normalizationTerm_of_raw
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (Rf : Ef →L[ℝ] Ef)
    (Rc : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hRaw : continuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J = 0) :
    normalizedContinuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J = 0 ↔
      (‖Rf‖⁻¹ - ‖Rc‖⁻¹) • (J.comp Rc.toLinearMap) = 0 := by
  rw [normalizedContinuousLinearOperatorCrossCarrierResidual_decomposition,
    hRaw]
  simp

/-- Audit-visible package separating raw cross-carrier compatibility from the
normalization-scalar obstruction. -/
structure NormalizedCrossCarrierIntertwiningDecompositionPackage
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (Rf : Ef →L[ℝ] Ef)
    (Rc : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef) where
  rawResidual : Ec →ₗ[ℝ] Ef
  rawResidual_eq : rawResidual =
    continuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J
  normalizedResidual : Ec →ₗ[ℝ] Ef
  normalizedResidual_eq : normalizedResidual =
    normalizedContinuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J
  normalizationTerm : Ec →ₗ[ℝ] Ef
  normalizationTerm_eq : normalizationTerm =
    (‖Rf‖⁻¹ - ‖Rc‖⁻¹) • (J.comp Rc.toLinearMap)
  decomposition :
    normalizedResidual = ‖Rf‖⁻¹ • rawResidual + normalizationTerm

/-- Construct the complete generic normalized-residual receipt. -/
noncomputable def normalizedCrossCarrierIntertwiningDecompositionPackage
    {Ef Ec : Type*}
    [NormedAddCommGroup Ef]
    [NormedSpace ℝ Ef]
    [NormedAddCommGroup Ec]
    [NormedSpace ℝ Ec]
    (Rf : Ef →L[ℝ] Ef)
    (Rc : Ec →L[ℝ] Ec)
    (J : Ec →ₗ[ℝ] Ef) :
    NormalizedCrossCarrierIntertwiningDecompositionPackage Rf Rc J where
  rawResidual := continuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J
  rawResidual_eq := rfl
  normalizedResidual := normalizedContinuousLinearOperatorCrossCarrierResidualLinearMap Rf Rc J
  normalizedResidual_eq := rfl
  normalizationTerm := (‖Rf‖⁻¹ - ‖Rc‖⁻¹) • (J.comp Rc.toLinearMap)
  normalizationTerm_eq := rfl
  decomposition := normalizedContinuousLinearOperatorCrossCarrierResidual_decomposition Rf Rc J

end

end MathlibAnalytic
end MGAP4D
