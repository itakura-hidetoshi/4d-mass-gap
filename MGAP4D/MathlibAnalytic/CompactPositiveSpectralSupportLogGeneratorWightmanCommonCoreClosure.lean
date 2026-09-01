import MGAP4D.MathlibAnalytic.RealLinearPMapCommonCoreClosureIntertwining
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorWightmanIntertwining
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter Function
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

local instance commonCoreClosureSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance commonCoreClosureSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance commonCoreClosureSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance commonCoreClosureSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance commonCoreClosureSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance commonCoreClosureSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance commonCoreClosurePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete H N hN beta hbeta

/-- The transfer spectral support is closed inside the stable physical pair
Hilbert carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_isClosed
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsClosed
      ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta :
        Set (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta))) :=
  realHilbertZeroEigenspaceSupport_isClosed
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)

/-- The reconstructed non-vacuum sector `Ω⊥` is a closed Hilbert subspace. -/
theorem ExplicitWightmanOSReconstructedModel.vacuumOrthogonal_isClosed
    (M : ExplicitWightmanOSReconstructedModel) :
    IsClosed (M.vacuumOrthogonal : Set M.H) := by
  simpa [ExplicitWightmanOSReconstructedModel.vacuumOrthogonal] using
    M.vacuumLine.isClosed_orthogonal

/-- Model-facing common-core closure hypothesis at the actual transfer/Wightman
frontier.

Unlike `PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining`,
this does not contain a global Hilbert equivalence, global domain transport, or
an all-domain intertwining identity. The common algebraic core is realized in
the stable ambient physical pair Hilbert carrier and in the reconstructed
Wightman Hilbert carrier, and is corestricted only at the final closed-subspace
step. This follows the Mathlib closed-subspace route and avoids fragile direct
`NormedSpace` synthesis on the spectral-support subtype. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCommonCoreClosure
    (C : Type) [NormedAddCommGroup C] [NormedSpace ℝ C]
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) :=
  RealLinearPMapClosedSubspaceCommonCoreClosureIntertwining
    (C := C)
    (S := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta)
    (T := M.vacuumOrthogonal)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport_isClosed
      H N hN beta hbeta)
    M.vacuumOrthogonal_isClosed
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta)
    M.canonicalVacuumOrthogonalHamiltonian

/-- Common algebraic operator-core closure data generate the exact global
transfer/Wightman generator intertwining structure used by the spectral bridge. -/
noncomputable def PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCommonCoreClosure.toIntertwining
    {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {H N : ℕ} {hN : 0 < N} {beta : ℝ} {hbeta : 0 ≤ beta}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCommonCoreClosure
      C H N hN beta hbeta M) :
    PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
      H N hN beta hbeta M :=
  ⟨D.toUnitaryIntertwining⟩

/-- Consequently common-core closure data already identify the actual nonzero
point energies of the transfer support log-generator with the reconstructed
Wightman Hamiltonian point spectrum on `Ω⊥`. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman_of_commonCoreClosure
    {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C]
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCommonCoreClosure
      C H N hN beta hbeta M) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta =
      M.canonicalVacuumOrthogonalPointSpectrum :=
  periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
    H N hN beta hbeta M D.toIntertwining

/-- The Wightman `Ω⊥` point-spectrum lower bound therefore follows from
common-core closure data rather than a generator-level intertwining assumption. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_wightmanPointSpectrum_inf_ge_two_mul_finiteVolumeDecayRate_of_commonCoreClosure
    {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C]
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCommonCoreClosure
      C H N hN beta hbeta M)
    (hSupport : ∃ v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta, v ≠ 0) :
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta ≤
      sInf M.canonicalVacuumOrthogonalPointSpectrum :=
  periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_wightmanPointSpectrum_inf_ge_two_mul_finiteVolumeDecayRate
    H N hN beta hbeta M D.toIntertwining hSupport

end

end MathlibAnalytic
end MGAP4D
