import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalContinuousSpectralObservableClosedBoxAlgebraic
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

variable {V W : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

section DiagonalClosedBox

variable (T : P.StronglyContinuousPhysicalSemigroup)
variable (G : T.VacuumSemigroupGapSlope)
variable (hP : P.IsNormalized)
variable (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
variable (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
variable (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
variable (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
variable (degree : G.AdmissibleRescaledDefectTime → ℕ)
variable (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
variable (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))

/-- Diagonal canonical OS form for every continuous observable: the Taylor
degree may depend arbitrarily on admissible time with no speed relation. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_tendsto_degree
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
        ∀ p, box.Contains p →
          ‖Phi (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (G.admissibleRescaledDefectTaylorResolvent
                    T hInnerSymmetric tau) p.center p.target (degree tau))) -
            Phi (continuousLinearMapCompression J Q
                (G.vacuumOrthogonalContinuumTaylorResolvent
                  T hP hInnerSymmetric hSelf p.target))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q Phi hPhi degree hdegree box

end DiagonalClosedBox

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
