import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventGlobalShape
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictAbsoluteMonotonicityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- On the actual one-step physical spectral support, every level of the
nonzero resolvent-quadratic derivative hierarchy is strictly increasing on
the full symmetric finite-volume coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
    (hv : v ≠ 0)
    (n : ℕ) :
    StrictMonoOn
      (iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v))
      (Set.Ioo
        (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta))
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)) := by
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  change StrictMonoOn (iteratedDeriv n q) (Set.Ioo (-c) c)
  have hdpos : ∀ lambda ∈ Set.Ioo (-c) c,
      0 < deriv (iteratedDeriv n q) lambda := by
    intro lambda hlambda
    have hnext :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv (n + 1) lambda
        (by simpa [c] using (abs_lt.mpr hlambda))
    simpa only [iteratedDeriv_succ] using hnext
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-c) c)
  · intro lambda hlambda
    exact
      (differentiableAt_of_deriv_ne_zero (hdpos lambda hlambda).ne').continuousAt.continuousWithinAt
  · simpa only [interior_Ioo] using hdpos

/-- The nonzero physical support-resolvent quadratic amplitude is strictly
increasing throughout the full symmetric finite-volume coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_strictMonoOn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
    (hv : v ≠ 0) :
    StrictMonoOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v)
      (Set.Ioo
        (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta))
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)) := by
  simpa only [iteratedDeriv_zero] using
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
      H N hN beta hbeta v hv 0)

/-- Hence a nonzero physical support-resolvent quadratic amplitude identifies
the spectral parameter uniquely inside the full symmetric coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_injOn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
    (hv : v ≠ 0) :
    Set.InjOn
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v)
      (Set.Ioo
        (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta))
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_strictMonoOn
    H N hN beta hbeta v hv).injOn

/-- The nonzero physical support-resolvent quadratic amplitude is strictly
convex on the full symmetric finite-volume coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_strictConvexOn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
    (hv : v ≠ 0) :
    StrictConvexOn ℝ
      (Set.Ioo
        (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta))
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v) := by
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  change StrictConvexOn ℝ (Set.Ioo (-c) c) q
  have hderivMono : StrictMonoOn (deriv q) (Set.Ioo (-c) c) := by
    simpa only [iteratedDeriv_one] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
        H N hN beta hbeta v hv 1)
  have hderivMonoInterior :
      StrictMonoOn (deriv q) (interior (Set.Ioo (-c) c)) := by
    simpa only [interior_Ioo] using hderivMono
  have hcont : ContinuousOn q (Set.Ioo (-c) c) := by
    intro lambda hlambda
    have hfirst :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv 1 lambda
        (by simpa [c] using (abs_lt.mpr hlambda))
    have hdpos : 0 < deriv q lambda := by
      simpa only [iteratedDeriv_one] using hfirst
    exact
      (differentiableAt_of_deriv_ne_zero hdpos.ne').continuousAt.continuousWithinAt
  exact hderivMonoInterior.strictConvexOn_of_deriv (convex_Ioo (-c) c) hcont

end

end MathlibAnalytic
end MGAP4D
