import MGAP4D.MathlibAnalytic.HilbertSumWeightedDiagonalSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace lp

noncomputable section

universe u

/-- Reinstall completeness of the zero-eigenspace support locally in this
module.  The defining support module keeps its own instance local, so imports
do not carry that instance forward. -/
local instance spectralLogSupportComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- Eigenspaces of the bounded support restriction are complete because they
are closed subspaces of the complete support Hilbert space. -/
local instance spectralLogSupportEigenspaceComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    CompleteSpace
      (eigenspace
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :=
  (ContinuousLinearMap.isClosed_eigenspace
    (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric)
    (mu : ℝ)).completeSpace_coe

/-- Install the official `lp` normed-space instance explicitly for the
dependent spectral-coordinate carrier. -/
local instance spectralLogCoordinateNormedSpace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    NormedSpace ℝ
      (lp
        (fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        2) :=
  lp.instNormedSpace

/-- Install the official Hilbert-sum inner product explicitly, avoiding a
large dependent-instance search when constructing the unbounded adjoint. -/
local instance spectralLogCoordinateInnerProductSpace
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    InnerProductSpace ℝ
      (lp
        (fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        2) :=
  lp.instInnerProductSpace

/-- Install completeness of the dependent `ℓ²` spectral-coordinate carrier
explicitly, before self-adjointness asks for the `LinearPMap` star operation. -/
local instance spectralLogCoordinateComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    CompleteSpace
      (lp
        (fun mu : Eigenvalues
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
          eigenspace
            (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
              Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
        2) :=
  lp.completeSpace

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
strictly-positive spectral coordinates.  It is the generic compact-positive
support logarithm specialized to the actual completed transfer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralLogGeneratorCoordinates
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :=
  realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num))
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1)

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
    realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_isSelfAdjoint
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1)

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