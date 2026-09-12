import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterClosedBox
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventFiniteParameterObservableClosedBoxDiagonal
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

/-- Canonical OS diagonal no-rate convergence of an observed joint
coordinate mixed derivative. -/
theorem VacuumSemigroupGapSlope.canonicalJointCoordinateMixedResponse_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    (κ : Fin n → Option (Fin m)) (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse φ m n
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
              p.center p.target (degree tau))) H z κ -
          continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse φ m n
            (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) H z κ‖ < epsilon := by
  exact
    G.canonicalJointCoordinateMixedResponse_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q φ m n H κ (fun tau => tau) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of a fixed observed joint
Taylor-Dyson coefficient. -/
theorem VacuumSemigroupGapSlope.canonicalJointTaylorResponse_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (parameterOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ parameterOrder m
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
              p.center p.target (degree tau))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ parameterOrder m
            (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) H z 0 ds 0 h‖ < epsilon := by
  exact
    G.canonicalJointTaylorResponse_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q φ parameterOrder m H ds h
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the complete finite observed
joint Taylor-Dyson jet. -/
theorem VacuumSemigroupGapSlope.canonicalJointTaylorResponse_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (parameterOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ n : Fin (parameterOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ n.1 m
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
              p.center p.target (degree tau))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ n.1 m
            (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) H z 0 ds 0 h‖ < epsilon := by
  exact
    G.canonicalJointTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
      T hP hInnerSymmetric hSelf J Q φ parameterOrder m H ds h
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of a basis-independent joint
trace Taylor-Dyson coefficient. -/
theorem VacuumSemigroupGapSlope.canonicalJointTaylorTrace_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V)) (ds : ℝ)
    (h : Fin m → ℝ) (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient V parameterOrder m
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
              p.center p.target (degree tau))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient V parameterOrder m
            (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) H z 0 ds 0 h| < epsilon := by
  exact
    G.canonicalJointTaylorTrace_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q parameterOrder m H ds h
      (fun tau => tau) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
