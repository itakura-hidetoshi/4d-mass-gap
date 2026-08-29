import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalQuadraticCoercive
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorGap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace lp LinearPMap

noncomputable section

set_option maxHeartbeats 800000

universe u

local instance spectralSupportLogGeneratorQuadraticCoerciveComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- A uniform lower bound on all logarithmic support energies lifts from the
coordinate Hilbert sum to the full natural domain of the actual-support
logarithmic Hamiltonian. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_quadratic_lower_bound
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (c : ℝ)
    (hLower : ∀ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
      c ≤ realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
    (x : (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).domain) :
    c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ^ 2 ≤
      inner ℝ
        (realHilbertCompactPositiveZeroSupportLogGenerator
          T hCompact hPositive x)
        (x : realHilbertZeroEigenspaceSupport T) := by
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let A := realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
    T hCompact hPositive
  let y : A.domain :=
    ⟨U (x : realHilbertZeroEigenspaceSupport T), x.property⟩
  have hCoord :=
    realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
      T hCompact hPositive x
  have hQuad :=
    realHilbertSumWeightedDiagonalLinearPMap_quadratic_lower_bound
      (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)
      c hLower y
  calc
    c * ‖(x : realHilbertZeroEigenspaceSupport T)‖ ^ 2 =
        c * ‖U (x : realHilbertZeroEigenspaceSupport T)‖ ^ 2 := by
      rw [U.norm_map]
    _ ≤ inner ℝ (A y) (U (x : realHilbertZeroEigenspaceSupport T)) := by
      simpa [A, y] using hQuad
    _ = inner ℝ
        (U (realHilbertCompactPositiveZeroSupportLogGenerator
          T hCompact hPositive x))
        (U (x : realHilbertZeroEigenspaceSupport T)) := by
      rw [hCoord]
    _ = inner ℝ
        (realHilbertCompactPositiveZeroSupportLogGenerator
          T hCompact hPositive x)
        (x : realHilbertZeroEigenspaceSupport T) := by
      exact
        realHilbertCompactPositive_zeroSupportHilbertSumEquiv_inner_map_map
          T hCompact hPositive _ _

local instance osBoundaryExcitationLogGeneratorQuadraticCoerciveSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationLogGeneratorQuadraticCoerciveSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationLogGeneratorQuadraticCoerciveSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationLogGeneratorQuadraticCoerciveSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationLogGeneratorQuadraticCoerciveSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationLogGeneratorQuadraticCoerciveSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationLogGeneratorQuadraticCoerciveSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationLogGeneratorQuadraticCoercivePairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The completed one-step logarithmic Hamiltonian is coercive on its entire
natural domain, with lower bound twice the finite-volume one-slab decay rate.
This upgrades the eigenspace-wise gap from the previous stage to a genuine
quadratic-form lower bound for every vector in the unbounded operator domain. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta).domain) :
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta *
        ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta)‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta x)
        (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy]
    using
      (realHilbertCompactPositiveZeroSupportLogGenerator_quadratic_lower_bound
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
          H N hN beta hbeta 1 (by norm_num))
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
          H N hN beta hbeta 1)
        (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy_ge_two_mul_finiteVolumeDecayRate
          H N hN beta hbeta)
        x)

/-- Since the finite-volume decay rate is strictly positive, the whole-domain
quadratic lower bound is a strictly positive spectral-support Hamiltonian gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_positive_of_ne_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta).domain)
    (hx : (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) ≠ 0) :
    0 < inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta x)
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  have hr :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
      H N hN beta hbeta
  have hnorm :
      0 < ‖(x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)‖ ^ 2 := by
    positivity
  have hLower :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator_quadratic_lower_bound
      H N hN beta hbeta x
  nlinarith

end

end MathlibAnalytic
end MGAP4D