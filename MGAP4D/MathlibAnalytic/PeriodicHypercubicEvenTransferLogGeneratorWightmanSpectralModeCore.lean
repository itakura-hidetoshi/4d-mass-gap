import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorWightmanSpectralModeCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace LinearPMap

noncomputable section

local instance spectralModePhysicalSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance spectralModePhysicalSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance spectralModePhysicalSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance spectralModePhysicalSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance spectralModePhysicalSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance spectralModePhysicalSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance spectralModePhysicalPairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Mode-wise transfer/Wightman data for the actual one-step SU(N) physical
excitation-pair transfer.  The only hard operator data are a dense realization
of the canonical positive-transfer spectral core into Wightman `Ω⊥`, and the
exact Wightman logarithmic-energy equation on each actual transfer eigenmode. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanSpectralModeData
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) :=
  CompactPositiveTransferLogGeneratorWightmanSpectralModeData
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num))
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1)
    M

/-- Actual mode-wise data generate the existing hard physical
transfer/Wightman intertwining interface. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanSpectralModeData.toIntertwining
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanSpectralModeData
      H N hN beta hbeta M) :
    PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
      H N hN beta hbeta M := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  let hCompact : IsCompactOperator T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num)
  let hPositive : T.IsPositive :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1
  have I :
      RealLinearPMapUnitaryIntertwining
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
        M.canonicalVacuumOrthogonalHamiltonian := by
    exact
      (show CompactPositiveTransferLogGeneratorWightmanSpectralModeData
          T hCompact hPositive M from D).toUnitaryIntertwining
  refine ⟨?_⟩
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    T, hCompact, hPositive] using I

/-- Hence the terminal physical transfer/Wightman point-spectrum equality is a
consequence of mode-wise logarithmic-energy identities, not a separately
supplied global operator equivalence. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman_of_spectralModes
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanSpectralModeData
      H N hN beta hbeta M) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta =
      M.canonicalVacuumOrthogonalPointSpectrum :=
  periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
    H N hN beta hbeta M (D.toIntertwining H N hN beta hbeta M)

end

end MathlibAnalytic
end MGAP4D
