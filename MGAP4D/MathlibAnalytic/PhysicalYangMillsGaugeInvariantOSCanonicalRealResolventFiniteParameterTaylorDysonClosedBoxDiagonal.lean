import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterTaylorDysonClosedBoxDiagonal
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventOperatorDysonClosedBoxDiagonal
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

/-- Diagonal canonical OS closed-box convergence of a fixed finite-parameter
Taylor-Dyson coefficient, with no admissible-time/ambient-Taylor-degree rate
relation. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2)) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient parameterOrder
            parameterDimension (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
              p.center p.target (degree tau))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient parameterOrder
            parameterDimension (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    G.admissibleRescaledDefectTaylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
      T hP hInnerSymmetric hSelf J Q parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      degree hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal canonical OS closed-box convergence of the complete finite
parameter Taylor-Dyson jet, with no rate relation. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2)) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ n : Fin (parameterOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient n.1
            parameterDimension (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
              p.center p.target (degree tau))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient n.1
            parameterDimension (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    G.admissibleRescaledDefectTaylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
      T hP hInnerSymmetric hSelf J Q parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      degree hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
