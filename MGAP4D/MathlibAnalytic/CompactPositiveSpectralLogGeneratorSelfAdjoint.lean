import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace lp

noncomputable section

universe u

/-- The intrinsic logarithmic generator of a compact positive real-Hilbert
operator, written in the Hilbert sum of the strictly-positive support
eigenspaces, is self-adjoint on its maximal weighted `ℓ²` domain. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_isSelfAdjoint
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    IsSelfAdjoint
      (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive) := by
  exact
    realHilbertSumWeightedDiagonalLinearPMap_isSelfAdjoint
      (G := fun mu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
      (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)

/-- Hence the intrinsic logarithmic support generator is closed. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_isClosed
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
      T hCompact hPositive).IsClosed :=
  (realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_isSelfAdjoint
    T hCompact hPositive).isClosed

/-- Its maximal weighted domain is dense in the intrinsic support spectral
coordinate Hilbert space. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_dense_domain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    Dense
      (((realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
        T hCompact hPositive).domain :
        Submodule ℝ
          (lp
            (fun mu : Eigenvalues
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
              eigenspace
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
            2)) :
        Set
          (lp
            (fun mu : Eigenvalues
              (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
              eigenspace
                (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
                  Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
            2)) := by
  exact
    realHilbertSumWeightedDiagonalLinearPMap_dense_domain
      (G := fun mu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
      (fun mu => realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu)

local instance osBoundaryExcitationSpectralLogGeneratorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationSpectralLogGeneratorSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationSpectralLogGeneratorSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationSpectralLogGeneratorSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationSpectralLogGeneratorSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationSpectralLogGeneratorSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationSpectralLogGeneratorSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationSpectralLogGeneratorPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The actual completed one-step pair-transfer Hamiltonian in intrinsic
strictly-positive spectral coordinates.  No eigenvalue enumeration is chosen:
the index is Mathlib's `Eigenvalues` subtype of the support restriction. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    lp
        (fun mu : Eigenvalues
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
            H N hN beta hbeta :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
                H N hN beta hbeta)) =>
          eigenspace
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
              H N hN beta hbeta :
              Module.End ℝ
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
                  H N hN beta hbeta)) mu)
        2 →ₗ.[ℝ]
      lp
        (fun mu : Eigenvalues
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
            H N hN beta hbeta :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
                H N hN beta hbeta)) =>
          eigenspace
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
              H N hN beta hbeta :
              Module.End ℝ
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
                  H N hN beta hbeta)) mu)
        2 :=
  realHilbertSumWeightedDiagonalLinearPMap
    (G := fun mu : Eigenvalues
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta)) =>
      eigenspace
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
          H N hN beta hbeta :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
              H N hN beta hbeta)) mu)
    (fun mu =>
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
        H N hN beta hbeta mu)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates
      H N hN beta hbeta).domain)
    (mu : Eigenvalues
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta))) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates
        H N hN beta hbeta x mu =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
          H N hN beta hbeta mu •
        ((x : (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates
          H N hN beta hbeta).domain) :
          lp
            (fun nu : Eigenvalues
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
                H N hN beta hbeta :
                Module.End ℝ
                  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
                    H N hN beta hbeta)) =>
              eigenspace
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
                  H N hN beta hbeta :
                  Module.End ℝ
                    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
                      H N hN beta hbeta)) nu)
            2) mu := by
  exact
    realHilbertSumWeightedDiagonalLinearPMap_apply
      (G := fun nu : Eigenvalues
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
          H N hN beta hbeta :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
              H N hN beta hbeta)) =>
        eigenspace
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
            H N hN beta hbeta :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
                H N hN beta hbeta)) nu)
      (fun nu =>
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
          H N hN beta hbeta nu) x mu

/-- The concrete intrinsic spectral-coordinate Hamiltonian is self-adjoint. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates_isSelfAdjoint
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates
        H N hN beta hbeta) := by
  exact
    realHilbertSumWeightedDiagonalLinearPMap_isSelfAdjoint
      (G := fun mu : Eigenvalues
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
          H N hN beta hbeta :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
              H N hN beta hbeta)) =>
        eigenspace
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
            H N hN beta hbeta :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
                H N hN beta hbeta)) mu)
      (fun mu =>
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogEnergy
          H N hN beta hbeta mu)

/-- The concrete intrinsic spectral-coordinate Hamiltonian is closed. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates_isClosed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates
      H N hN beta hbeta).IsClosed :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates_isSelfAdjoint
    H N hN beta hbeta).isClosed

/-- Audit-visible package for the first genuine unbounded self-adjoint
Hamiltonian attached to the completed one-step pair transfer on its correct
strictly-positive support spectral carrier. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairSpectralLogGeneratorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  selfAdjoint :
    IsSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates
        H N hN beta hbeta)
  closed :
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates
      H N hN beta hbeta).IsClosed

/-- Construct the concrete spectral logarithmic generator package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedPairSpectralLogGeneratorPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairSpectralLogGeneratorPackage
      H N hN beta hbeta :=
  ⟨periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates_isSelfAdjoint
      H N hN beta hbeta,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates_isClosed
      H N hN beta hbeta⟩

end

end MathlibAnalytic
end MGAP4D