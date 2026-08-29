import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventQuadraticAbsoluteMonotonicity
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorNormCoercive
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorRangeSurjective
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 800000

local instance osBoundaryExcitationSupportResolventAbsoluteMonotonicitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationSupportResolventAbsoluteMonotonicitySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationSupportResolventAbsoluteMonotonicitySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationSupportResolventAbsoluteMonotonicitySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationSupportResolventAbsoluteMonotonicitySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationSupportResolventAbsoluteMonotonicitySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationSupportResolventAbsoluteMonotonicitySpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationSupportResolventAbsoluteMonotonicityPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Canonical spelling of the actual positive spectral-support Hilbert carrier.
This is definitionally the same carrier as the long physical support alias, but
keeps Mathlib's native submodule Hilbert instances visible to typeclass search. -/
abbrev periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :=
  realHilbertZeroEigenspaceSupport
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)

local instance osBoundaryExcitationSupportResolventAbsoluteMonotonicityCarrierComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
        H N hN beta hbeta) :=
  (realHilbertZeroEigenspaceSupport_isClosed
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)).completeSpace_coe

/-- The actual unbounded logarithmic Hamiltonian on the canonical spelling of
the completed positive spectral support. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
        H N hN beta hbeta →ₗ.[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
        H N hN beta hbeta :=
  realHilbertCompactPositiveZeroSupportLogGenerator
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num))
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1)

/-- The finite-volume coercive support gap used by the canonical resolvent. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : ℝ :=
  2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
    H N hN beta hbeta

@[simp]
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
      H N hN beta hbeta := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
  exact mul_pos (by norm_num)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
      H N hN beta hbeta)

/-- Native-carrier form of the whole-domain quadratic coercive receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_quadratic_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
      H N hN beta hbeta).domain) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
          H N hN beta hbeta *
        ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
          H N hN beta hbeta)‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
          H N hN beta hbeta x)
        (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
          H N hN beta hbeta) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
    using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
        H N hN beta hbeta x)

/-- Native-carrier form of the graph-norm coercive receipt. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_norm_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
      H N hN beta hbeta).domain) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
          H N hN beta hbeta *
        ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
          H N hN beta hbeta)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
          H N hN beta hbeta x‖ := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
    using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
        H N hN beta hbeta x)

/-- The native-carrier logarithmic generator has trivial kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_eq_zero_of_apply_eq_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
      H N hN beta hbeta).domain)
    (hx : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
      H N hN beta hbeta x = 0) :
    x = 0 := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
    using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_eq_zero_of_apply_eq_zero
        H N hN beta hbeta x hx)

/-- The native-carrier logarithmic generator is onto the completed positive
spectral support. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_surjective
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Function.Surjective
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
        H N hN beta hbeta).toFun := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport]
    using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_surjective
        H N hN beta hbeta)

/-- The actual support logarithmic generator is self-adjoint on the native
Hilbert carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
  exact
    realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1)

/-- Canonical bounded ambient resolvent of the physical support logarithmic
Hamiltonian. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventFamily
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
        H N hN beta hbeta :=
  realLinearPMapAmbientResolventFamily_of_norm_lower_bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap_pos
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_norm_lower_bound
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_eq_zero_of_apply_eq_zero
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_surjective
      H N hN beta hbeta)
    lambda

/-- Diagonal scalar amplitude of the canonical physical support resolvent. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventQuadraticAmplitude
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
      H N hN beta hbeta) : ℝ → ℝ :=
  realLinearPMapAmbientResolventQuadraticAmplitude
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap_pos
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_norm_lower_bound
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_eq_zero_of_apply_eq_zero
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_surjective
      H N hN beta hbeta)
    u

/-- Every power of the canonical bounded physical support resolvent has
nonnegative quadratic form throughout the full symmetric gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventFamily_pow_inner_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (lambda : ℝ)
    (hlambda :
      |lambda| <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
          H N hN beta hbeta)
    (n : ℕ)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
      H N hN beta hbeta) :
    0 ≤ inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventFamily
        H N hN beta hbeta lambda ^ n) u)
      u := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventFamily
  exact
    realLinearPMapAmbientResolventFamily_pow_inner_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap_pos
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_norm_lower_bound
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_eq_zero_of_apply_eq_zero
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_surjective
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_isSelfAdjoint
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_quadratic_lower_bound
        H N hN beta hbeta)
      lambda hlambda n u

/-- Exact all-order derivative formula for the physical support-resolvent
quadratic amplitude. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
      H N hN beta hbeta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda :
      |lambda| <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
          H N hN beta hbeta) :
    iteratedDeriv n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventQuadraticAmplitude
          H N hN beta hbeta u)
        lambda =
      (n.factorial : ℝ) * inner ℝ
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventFamily
          H N hN beta hbeta lambda ^ (n + 1)) u)
        u := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventQuadraticAmplitude
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventFamily
  exact
    realLinearPMapAmbientResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap_pos
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_norm_lower_bound
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_eq_zero_of_apply_eq_zero
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventLogGenerator_surjective
        H N hN beta hbeta)
      u n lambda hlambda

/-- Absolute monotonicity of the physical support-resolvent quadratic
amplitude: every ordinary derivative is nonnegative throughout the full
finite-volume symmetric gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventQuadraticAmplitude_iteratedDeriv_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventCarrier
      H N hN beta hbeta)
    (n : ℕ)
    (lambda : ℝ)
    (hlambda :
      |lambda| <
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventGap
          H N hN beta hbeta) :
    0 ≤ iteratedDeriv n
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventQuadraticAmplitude
        H N hN beta hbeta u)
      lambda := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventQuadraticAmplitude_iteratedDeriv_eq_factorial
    H N hN beta hbeta u n lambda hlambda]
  exact mul_nonneg (by positivity)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationTransferOneSupportResolventFamily_pow_inner_nonneg
      H N hN beta hbeta lambda hlambda (n + 1) u)

end

end MathlibAnalytic
end MGAP4D
