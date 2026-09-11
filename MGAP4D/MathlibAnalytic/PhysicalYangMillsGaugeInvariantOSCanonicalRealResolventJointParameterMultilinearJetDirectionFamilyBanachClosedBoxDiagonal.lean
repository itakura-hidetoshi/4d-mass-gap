import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalRealResolventJointParameterMultilinearJetDirectionFamilyBanachClosedBox
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

/-- Canonical OS diagonal no-rate convergence of the complete carrier jet in
its actual finite dependent-product norm. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearCarrierJet_tendsto_uniform_closedBox_of_tendsto_degree_directionFamily_norm
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (mixedOrder m : ℕ) (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (H : G.AdmissibleRescaledDefectTime → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V))
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (hH : Tendsto H G.admissibleRescaledDefectTimeFilter (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) (H tau) (continuousLinearMapCompressedTaylorPartialSumRealResolventAt
            J Q (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
              p.center p.target (degree tau) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) H0 (continuousLinearMapCompressedRealResolventAt J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target) z)‖ < epsilon := by
  exact G.canonicalJointMultilinearCarrierJet_tendsto_uniform_closedBox_of_joint_directionFamily_norm
    T hP hInnerSymmetric hSelf J Q mixedOrder m (fun tau => tau) degree H H0
    tendsto_id hdegree hH box Z margin hmargin hlimitMargin M hM hlimitNorm

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Canonical OS diagonal no-rate convergence of every Banach-valued response
jet in its actual finite dependent-product norm. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearResponseCarrierJet_tendsto_uniform_closedBox_of_tendsto_degree_directionFamily_norm
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (mixedOrder m : ℕ)
    (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (H : G.AdmissibleRescaledDefectTime → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V))
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (hH : Tendsto H G.admissibleRescaledDefectTimeFilter (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder (H tau) (continuousLinearMapCompressedTaylorPartialSumRealResolventAt
            J Q (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
              p.center p.target (degree tau) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder H0 (continuousLinearMapCompressedRealResolventAt J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target) z)‖ < epsilon := by
  exact G.canonicalJointMultilinearResponseCarrierJet_tendsto_uniform_closedBox_of_joint_directionFamily_norm
    T hP hInnerSymmetric hSelf J Q φ mixedOrder m (fun tau => tau) degree H H0
    tendsto_id hdegree hH box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Canonical OS diagonal no-rate convergence of the basis-independent trace
jet in its actual finite dependent-product norm. -/
theorem VacuumSemigroupGapSlope.canonicalJointMultilinearTraceCarrierJet_tendsto_uniform_closedBox_of_tendsto_degree_directionFamily_norm
    (T : P.StronglyContinuousPhysicalSemigroup) (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized) (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (J : V →L[ℝ] P.VacuumOrthogonalHilbert) (Q : P.VacuumOrthogonalHilbert →L[ℝ] V)
    (mixedOrder m : ℕ) (degree : G.AdmissibleRescaledDefectTime → ℕ)
    (H : G.AdmissibleRescaledDefectTime → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V))
    (hdegree : Tendsto degree G.admissibleRescaledDefectTimeFilter atTop)
    (hH : Tendsto H G.admissibleRescaledDefectTimeFilter (𝓝 H0))
    (box : ContinuousLinearMapClosedTaylorParameterBox (G.mass / 2))
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (G.vacuumOrthogonalContinuumTaylorResolvent T hP hInnerSymmetric hSelf p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ tau in G.admissibleRescaledDefectTimeFilter,
      ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder (H tau) (continuousLinearMapCompressedTaylorPartialSumRealResolventAt
            J Q (G.admissibleRescaledDefectTaylorResolvent T hInnerSymmetric tau)
              p.center p.target (degree tau) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder H0 (continuousLinearMapCompressedRealResolventAt J Q
            (G.vacuumOrthogonalContinuumTaylorResolvent
              T hP hInnerSymmetric hSelf p.target) z)‖ < epsilon := by
  exact G.canonicalJointMultilinearTraceCarrierJet_tendsto_uniform_closedBox_of_joint_directionFamily_norm
    T hP hInnerSymmetric hSelf J Q mixedOrder m (fun tau => tau) degree H H0
    tendsto_id hdegree hH box Z margin hmargin hlimitMargin M hM hlimitNorm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData
end MathlibAnalytic
end MGAP4D
