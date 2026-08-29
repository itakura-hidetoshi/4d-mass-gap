import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorQuadraticCoercive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

universe u

/-- Cauchy--Schwarz converts a nonnegative quadratic-form lower bound into
an operator-norm lower bound.  This abstract receipt is independent of the
spectral realization and is reusable for unbounded operators represented by
vectors in their natural domains. -/
theorem realHilbert_norm_lower_bound_of_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (c : ℝ)
    (hc : 0 ≤ c)
    (u v : E)
    (hquad : c * ‖v‖ ^ 2 ≤ inner ℝ u v) :
    c * ‖v‖ ≤ ‖u‖ := by
  have hcs : inner ℝ u v ≤ ‖u‖ * ‖v‖ :=
    le_trans (le_abs_self (inner ℝ u v)) (abs_real_inner_le_norm u v)
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  have hu : 0 ≤ ‖u‖ := norm_nonneg u
  nlinarith

local instance osBoundaryExcitationLogGeneratorNormCoerciveSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorNormCoerciveSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorNormCoerciveSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorNormCoerciveSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorNormCoerciveSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorNormCoerciveSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorNormCoerciveSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorNormCoercivePairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The whole-domain quadratic gap controls the graph norm of the completed
one-step logarithmic Hamiltonian from below.  This is the quantitative
injectivity estimate needed before constructing an inverse on its range. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta).domain) :
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta *
        ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta x‖ := by
  apply realHilbert_norm_lower_bound_of_quadratic_lower_bound
  · have hr :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta
    positivity
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
        H N hN beta hbeta x

/-- The completed one-step support logarithmic Hamiltonian has trivial kernel
on its natural domain. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_injective
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    {x y : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta).domain}
    (hxy :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta x =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta y) :
    x = y := by
  let A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta
  let z : A.domain := x - y
  have hzA : A z = 0 := by
    dsimp [z, A]
    rw [map_sub, hxy, sub_self]
  have hnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_norm_lower_bound
      H N hN beta hbeta z
  have hr :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
      H N hN beta hbeta
  have hzNorm :
      ‖(z : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ = 0 := by
    rw [hzA, norm_zero] at hnorm
    have hcoef :
        0 < 2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta := by
      positivity
    have hznonneg :
        0 ≤ ‖(z : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta)‖ := norm_nonneg _
    nlinarith
  have hz :
      (z : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) = 0 := norm_eq_zero.mp hzNorm
  apply Subtype.ext
  have :
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) -
        (y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) = 0 := by
    simpa [z, A] using hz
  exact sub_eq_zero.mp this

end

end MathlibAnalytic
end MGAP4D
