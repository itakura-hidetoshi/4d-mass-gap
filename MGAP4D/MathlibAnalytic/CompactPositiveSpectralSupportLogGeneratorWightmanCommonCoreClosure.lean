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
local instance commonCoreClosureSpectralSupportNormedSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  infer_instance
local instance commonCoreClosureSpectralSupportComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact (realHilbertZeroEigenspaceSupport_isClosed
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)).completeSpace_coe

/-- Model-facing common-core closure hypothesis at the actual transfer/Wightman
frontier.

Unlike `PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining`,
this does not contain a global Hilbert equivalence, global domain transport, or
an all-domain intertwining identity.  It asks only for two dense isometric
realizations of one normed algebraic core, Mathlib `HasCore` receipts for the
two closed operators after canonical pullback, and equality of their actions on
that core. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCommonCoreClosure
    (C : Type) [NormedAddCommGroup C] [NormedSpace ℝ C]
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) :=
  RealLinearPMapCommonCoreClosureIntertwining (C := C)
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
