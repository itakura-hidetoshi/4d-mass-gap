import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFiniteLiteralWilsonRawExcitationDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finiteLiteralWilsonSpectralPackageTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finiteLiteralWilsonSpectralPackageCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finiteLiteralWilsonSpectralPackageSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finiteLiteralWilsonSpectralPackageMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finiteLiteralWilsonSpectralPackageBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finiteLiteralWilsonSpectralPackageSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Audit-visible finite-volume package joining the literal adjacent-slab
Wilson Haar path to the physical transfer power and then to the normalized
excitation-sector exponential decay.

The raw path retains the exact physical top-transfer scale; the normalized
path has the pure finite-volume exponential factor. -/
structure PeriodicHypercubicEvenSpecialUnitaryFiniteLiteralWilsonSpectralDecayPackage
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (h + 1) N hN beta hbeta) : Prop where
  slabCount :
    periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) = h + 2
  finiteVolumeRatePositive :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      (h + 1) N hN beta hbeta
  literalPathPhysicalPower :
    periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
        h N beta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
          (h + 1) N hN beta hbeta
          (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (h + 1) N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)
  transferNormalizedExcitation :
    periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude
        h N hN beta hbeta f g =
      inner ℝ
        (((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderExcitationTransferOperator
          (h + 1) N hN beta hbeta f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              (h + 1) N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (h + 1) N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)
  normalizedExponentialDecay :
    ‖periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude
        h N hN beta hbeta f g‖ ≤
      (Real.exp
        (-(((h + 2 : ℕ) : ℝ)) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖
  rawExponentialDecay :
    ‖periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
        h N beta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (h + 1) N hN beta hbeta‖ ^ (h + 2) *
        ((Real.exp
          (-(((h + 2 : ℕ) : ℝ)) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              (h + 1) N hN beta hbeta) * ‖f‖) * ‖g‖)

/-- Construct the complete finite-volume literal-Wilson/spectral-decay package
from the canonical full-path, normalized-excitation, and raw-path bridges. -/
theorem periodicHypercubicEvenSpecialUnitaryFiniteLiteralWilsonSpectralDecayPackage
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      (h + 1) N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryFiniteLiteralWilsonSpectralDecayPackage
      h N hN beta hbeta f g := by
  refine
    { slabCount := ?_
      finiteVolumeRatePositive := ?_
      literalPathPhysicalPower := ?_
      transferNormalizedExcitation := ?_
      normalizedExponentialDecay := ?_
      rawExponentialDecay := ?_ }
  · simp [periodicHypercubicEvenPositiveHalfCylinderSlabCount]
  · exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        (h + 1) N hN beta hbeta
  · exact
      periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude_eq_physicalPositiveHalfCylinderTransfer_inner
        h N hN beta hbeta
        (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (h + 1) N)
  · exact
      periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_eq_excitationTransfer_inner
        h N hN beta hbeta f g
  · exact
      periodicHypercubicEvenSpecialUnitaryTransferNormalizedLiteralTwoEndedWilsonAmplitude_norm_le_exp_h_add_two
        h N hN beta hbeta f g
  · exact
      periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude_norm_le_physicalNormPow_mul_exp_h_add_two
        h N hN beta hbeta f g

end

end MathlibAnalytic
end MGAP4D
