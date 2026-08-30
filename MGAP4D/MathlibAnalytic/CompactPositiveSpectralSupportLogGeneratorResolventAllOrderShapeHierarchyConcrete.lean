import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventAllOrderShapeHierarchy
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventGlobalShapeConcrete
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- On the actual one-step physical spectral support, every derivative level
of every nonzero resolvent quadratic amplitude is strictly convex on the full
symmetric finite-volume coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_strictConvexOn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
    (hv : v ≠ 0)
    (n : ℕ) :
    StrictConvexOn ℝ
      (Set.Ioo
        (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta))
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta))
      (iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v)) := by
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let qn := iteratedDeriv n q
  change StrictConvexOn ℝ (Set.Ioo (-c) c) qn
  have hderivMono : StrictMonoOn (deriv qn) (Set.Ioo (-c) c) := by
    have hnext :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
        H N hN beta hbeta v hv (n + 1)
    simpa only [qn, q, iteratedDeriv_succ] using hnext
  have hderivMonoInterior :
      StrictMonoOn (deriv qn) (interior (Set.Ioo (-c) c)) := by
    simpa only [interior_Ioo] using hderivMono
  have hcont : ContinuousOn qn (Set.Ioo (-c) c) := by
    intro lambda hlambda
    have hnext :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv (n + 1) lambda
        (by simpa [c] using (abs_lt.mpr hlambda))
    have hdpos : 0 < deriv qn lambda := by
      simpa only [qn, q, iteratedDeriv_succ] using hnext
    exact
      (differentiableAt_of_deriv_ne_zero hdpos.ne').continuousAt.continuousWithinAt
  exact hderivMonoInterior.strictConvexOn_of_deriv (convex_Ioo (-c) c) hcont

/-- Every derivative level of the physical response identifies the spectral
parameter uniquely throughout the full symmetric coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_injOn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
    (hv : v ≠ 0)
    (n : ℕ) :
    Set.InjOn
      (iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v))
      (Set.Ioo
        (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta))
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_strictMonoOn
    H N hN beta hbeta v hv n).injOn

/-- Physical three-point form: at every derivative order, adjacent secant
slopes strictly increase across any `x < y < z` inside the full coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_slope_strict_mono_adjacent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (v :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)
    (hv : v ≠ 0)
    (n : ℕ)
    {x y z : ℝ}
    (hx : x ∈ Set.Ioo
      (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
      (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
    (hz : z ∈ Set.Ioo
      (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
      (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
    (hxy : x < y)
    (hyz : y < z) :
    ((iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v)) y -
      (iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v)) x) / (y - x) <
    ((iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v)) z -
      (iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
          H N hN beta hbeta v)) y) / (z - y) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_strictConvexOn
      H N hN beta hbeta v hv n).slope_strict_mono_adjacent hx hz hxy hyz

end

end MathlibAnalytic
end MGAP4D
