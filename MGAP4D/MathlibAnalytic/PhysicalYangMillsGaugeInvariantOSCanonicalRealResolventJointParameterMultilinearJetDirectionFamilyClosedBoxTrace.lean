import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterMultilinearJetDirectionFamilyClosedBoxResponse
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
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Canonical OS complete closed-box convergence of the basis-independent trace
jet when approximation time, Taylor degree, and all directions vary jointly. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearTraceCarrierJet_tendsto_uniform_closedBox_of_joint_directionFamily_sup
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (mixedOrder m : ℕ) {β : Type*} {f : Filter β}
    (tau : β → G.AdmissibleRescaledDefectTime) (degree : β → ℕ)
    (H : β → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (htau : Tendsto tau f G.admissibleRescaledDefectTimeFilter)
    (hdegree : Tendsto degree f atTop) (hH : Tendsto H f (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapJointMultilinearCarrierJetSupDistance (V := V) (W := ℝ)
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder (H b) (continuousLinearMapCompressedTaylorPartialSumRealResolventAt J Q
            (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric (tau b))
            p.center p.target (degree b) z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder H0 (continuousLinearMapCompressedRealResolventAt J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target) z)) < epsilon := by
  exact
    (G.canonicalRescaledDefectTaylorStrongLimitData T hP hInnerSymmetric hSelf).taylorPartialSum_realResolventJointMultilinearTraceCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_sup
      (G.admissibleRescaledDefectOpenResolventNormBoundFamilyData T hInnerSymmetric)
      (G.vacuumOrthogonalContinuumOpenResolventNormBoundData T hP hInnerSymmetric hSelf)
      rfl rfl J Q mixedOrder m tau degree H H0 htau hdegree hH box Z margin hmargin
      hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
