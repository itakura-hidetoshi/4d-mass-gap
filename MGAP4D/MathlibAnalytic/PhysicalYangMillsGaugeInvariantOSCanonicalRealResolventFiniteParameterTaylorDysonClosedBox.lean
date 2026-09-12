import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterTaylorDysonClosedBox
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventOperatorDysonClosedBox
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

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Canonical OS closed-box convergence of a fixed finite-parameter
Taylor-Dyson coefficient for arbitrary joint admissible-time and ambient
Taylor-degree nets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2)) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient parameterOrder
          parameterDimension (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
            p.center p.target (degree b))) H z 0 h -
        continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient parameterOrder
          parameterDimension (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    G.canonicalRescaledDefectTaylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      T hP hInnerSymmetric hSelf J Q parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      tau degree htau hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS closed-box convergence of the complete finite parameter
Taylor-Dyson jet for arbitrary joint admissible-time and ambient Taylor-degree
nets. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2)) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m,
      ∀ n : Fin (parameterOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient n.1
            parameterDimension (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
              p.center p.target (degree b))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient n.1
            parameterDimension (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    G.canonicalRescaledDefectTaylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
      T hP hInnerSymmetric hSelf J Q parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      tau degree htau hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
