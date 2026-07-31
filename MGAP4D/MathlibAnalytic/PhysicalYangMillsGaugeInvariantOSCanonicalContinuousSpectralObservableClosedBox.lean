import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalContinuousSpectralObservableCompactAlgebraic
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

section JointClosedBox

variable (T : P.StronglyContinuousPhysicalSemigroup)
variable (G : T.VacuumSemigroupGapSlope)
variable (hP : P.IsNormalized)
variable (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
variable (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
variable (J : V →L[ℝ] P.VacuumOrthogonalHilbert)
variable (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)

/-- Arbitrary continuous observables converge uniformly on a complete closed
half-mass Taylor box for every joint admissible-time/Taylor-degree net. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectTaylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_continuum_uniform_closedBox_of_joint
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi)
    {β : Type*} {m : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (htau : Tendsto tau m G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2)) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p →
      ‖Phi (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (G.admissibleRescaledDefectTaylorResolvent
                T hInnerSymmetric (tau b)) p.center p.target (degree b))) -
        Phi (continuousLinearMapCompression J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target))‖ < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData
      T hP hInnerSymmetric hSelf).taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData
          T hInnerSymmetric)
        (G.vacuumOrthogonalContinuumOpenResolventNormBoundData
          T hP hInnerSymmetric hSelf)
        rfl rfl J Q Phi hPhi tau degree htau hdegree box

end JointClosedBox

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
