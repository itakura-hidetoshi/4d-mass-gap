import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterMultilinearJetSupClosedBox
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

/-- Canonical OS diagonal no-rate convergence of the entire finite joint
Fréchet carrier jet in one maximum component norm. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearCarrierJet_tendsto_uniform_closedBox_of_tendsto_degree_sup
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        continuousLinearMapJointMultilinearCarrierJetSupDistance
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
            m (mixedOrder + 1) H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
                p.center p.target (degree tau))) z))
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
            m (mixedOrder + 1) H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) z)) < epsilon := by
  exact
    G.canonicalJointMultilinearCarrierJet_tendsto_uniform_closedBox_of_joint_sup
      T hP hInnerSymmetric hSelf J Q mixedOrder m H (fun tau => tau) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the entire finite
Banach-valued response jet in one maximum component norm. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearResponseCarrierJet_tendsto_uniform_closedBox_of_tendsto_degree_sup
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (mixedOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V))
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        continuousLinearMapJointMultilinearCarrierJetSupDistance
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
            φ m mixedOrder H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
                p.center p.target (degree tau))) z))
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
            φ m mixedOrder H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) z)) < epsilon := by
  exact
    G.canonicalJointMultilinearResponseCarrierJet_tendsto_uniform_closedBox_of_joint_sup
      T hP hInnerSymmetric hSelf J Q φ mixedOrder m H (fun tau => tau) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the entire finite
basis-independent trace jet in one maximum component norm. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearTraceCarrierJet_tendsto_uniform_closedBox_of_tendsto_degree_sup
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        continuousLinearMapJointMultilinearCarrierJetSupDistance
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
            V m mixedOrder H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
                p.center p.target (degree tau))) z))
          (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
            V m mixedOrder H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (G.vacuumOrthogonalContinuumTaylorResolvent
                T hP hInnerSymmetric hSelf p.target)) z)) < epsilon := by
  exact
    G.canonicalJointMultilinearTraceCarrierJet_tendsto_uniform_closedBox_of_joint_sup
      T hP hInnerSymmetric hSelf J Q mixedOrder m H (fun tau => tau) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D
