import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterClosedBox
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventFiniteParameterObservableClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Canonical OS complete closed-box convergence of an observed joint
coordinate mixed derivative for arbitrary joint nets. -/
theorem VacuumSemigroupGapSlope.canonicalJointCoordinateMixedResponse_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    (κ : Fin n → Option (Fin m)) {β : Type*} {f : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau f G.admissibleRescaledDefectTimeFilter) (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse φ m n
          (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
            p.center p.target (degree b))) H z κ -
        continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse φ m n
          (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) H z κ‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse] using
    G.canonicalFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q φ (m + 1) n
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
      (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n κ)
      tau degree htau hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS complete closed-box convergence of a fixed observed joint
Taylor-Dyson coefficient for arbitrary joint nets. -/
theorem VacuumSemigroupGapSlope.canonicalJointTaylorResponse_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (parameterOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ) {β : Type*} {f : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau f G.admissibleRescaledDefectTimeFilter) (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ parameterOrder m
          (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
            p.center p.target (degree b))) H z 0 ds 0 h -
        continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ parameterOrder m
          (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) H z 0 ds 0 h‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse,
    continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonCoefficient] using
    G.canonicalFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q φ parameterOrder (m + 1)
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
      (continuousLinearMapJointSpectralOperatorParameter m ds h)
      tau degree htau hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS complete closed-box convergence of the finite observed joint
Taylor-Dyson jet for arbitrary joint nets. -/
theorem VacuumSemigroupGapSlope.canonicalJointTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (parameterOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ) {β : Type*} {f : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau f G.admissibleRescaledDefectTimeFilter) (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ n : Fin (parameterOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ n.1 m
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
              p.center p.target (degree b))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ n.1 m
            (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) H z 0 ds 0 h‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse,
    continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonCoefficient] using
    G.canonicalFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
      T hP hInnerSymmetric hSelf J Q φ parameterOrder (m + 1)
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
      (continuousLinearMapJointSpectralOperatorParameter m ds h)
      tau degree htau hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS closed-box convergence of a fixed basis-independent joint
trace Taylor-Dyson coefficient. -/
theorem VacuumSemigroupGapSlope.canonicalJointTaylorTrace_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V)) (ds : ℝ)
    (h : Fin m → ℝ) {β : Type*} {f : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau f G.admissibleRescaledDefectTimeFilter) (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      |continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient V parameterOrder m
          (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
            p.center p.target (degree b))) H z 0 ds 0 h -
        continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient V parameterOrder m
          (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) H z 0 ds 0 h| < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient,
    Real.norm_eq_abs] using
    G.canonicalJointTaylorResponse_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q (continuousLinearMapTrace (V := V))
      parameterOrder m H ds h tau degree htau hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
