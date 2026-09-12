import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetOperatorNormClosedBox
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventStabilityClosedBox
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

/-- Canonical OS complete closed-box convergence of the full joint Fréchet
multilinear carrier for arbitrary admissible-time and Taylor-degree nets. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearCarrier_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V)) {β : Type*} {f : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau f G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
              p.center p.target (degree b))) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target)) z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q m n H tau degree htau hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS complete closed-box convergence of the finite full-carrier jet
for arbitrary joint nets. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearCarrier_tendsto_uniform_closedBox_of_joint_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V)) {β : Type*} {f : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau f G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ n : Fin (mixedOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n.1 H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
                p.center p.target (degree b))) z) -
          continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n.1 H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q mixedOrder m H tau degree htau hdegree box Z margin
      hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS complete closed-box convergence of a Banach-valued full
multilinear response carrier. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearResponseCarrier_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    {β : Type*} {f : Filter β} (tau : β → G.AdmissibleRescaledDefectTime)
    (degree : β → ℕ) (htau : Tendsto tau f G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent φ m n H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
              p.center p.target (degree b))) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent φ m n H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target)) z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventJointMultilinearResponseCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q φ m n H tau degree htau hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Canonical OS complete closed-box convergence of the basis-independent full
trace carrier. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearTraceCarrier_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V)) {β : Type*} {f : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau f G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent V m n H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
              p.center p.target (degree b))) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent V m n H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target)) z)‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventJointMultilinearTraceCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q m n H tau degree htau hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
