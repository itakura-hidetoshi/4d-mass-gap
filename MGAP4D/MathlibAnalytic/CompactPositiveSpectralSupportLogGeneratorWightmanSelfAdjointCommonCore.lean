import MGAP4D.MathlibAnalytic.RealLinearPMapClosedSubspaceSelfAdjointCommonCoreIntertwining
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorSelfAdjoint
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorWightmanIntertwining
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Module End
open scoped InnerProductSpace LinearPMap

noncomputable section

local instance compactPositiveWightmanSupportComplete
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- Model-facing common-core data for a compact positive transfer operator and
an explicit Wightman reconstruction.

The source is the actual strictly-positive spectral support of `T`; the target
is the reconstructed Wightman vacuum-orthogonal sector.  Both realizations of
the common normed core are given on stable ambient Hilbert carriers and then
canonically corestricted.

Crucially, this package contains neither a global Hilbert-space equivalence nor
a global domain-transport/intertwining assumption, and it does not assume
self-adjointness.  Source self-adjointness follows from the intrinsic compact
positive logarithmic-generator theorem, while target self-adjointness follows
from the canonical Wightman restriction theorem.  Only one Mathlib `HasCore`
receipt, on the transfer side, remains together with exact action agreement on
the algebraic core. -/
structure CompactPositiveTransferLogGeneratorWightmanCommonCoreData
    {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (M : ExplicitWightmanOSReconstructedModel) where
  source :
    RealHilbertClosedSubspaceDenseCoreRealization (C := C)
      (realHilbertZeroEigenspaceSupport T)
  target :
    RealHilbertClosedSubspaceDenseCoreRealization (C := C)
      M.vacuumOrthogonal
  source_hasCore :
    (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).HasCore
      (LinearMap.range
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict source).toLinearMap)
  target_mem : ∀ c : C,
    RealHilbertClosedSubspaceDenseCoreRealization.corestrict target c ∈
      M.canonicalVacuumOrthogonalHamiltonian.domain
  core_intertwines : ∀ c : C,
    M.canonicalVacuumOrthogonalHamiltonian
        ⟨RealHilbertClosedSubspaceDenseCoreRealization.corestrict target c,
          target_mem c⟩ =
      realHilbertDenseCoreLinearIsometryEquiv
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict source)
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange source)
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict target)
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange target)
        (realHilbertCompactPositiveZeroSupportLogGenerator
          T hCompact hPositive
          ⟨RealHilbertClosedSubspaceDenseCoreRealization.corestrict source c,
            source_hasCore.le_domain ⟨c, rfl⟩⟩)

/-- Compact-positive transfer/Wightman common-core data instantiate the generic
closed-subspace self-adjoint common-core theorem.  Self-adjointness on both
physical sectors is generated, not supplied. -/
noncomputable def
    CompactPositiveTransferLogGeneratorWightmanCommonCoreData.toClosedSubspaceSelfAdjointCommonCore
    {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanCommonCoreData
      (C := C) T hCompact hPositive M) :
    RealLinearPMapClosedSubspaceSelfAdjointCommonCoreIntertwining
      (C := C)
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
      M.canonicalVacuumOrthogonalHamiltonian where
  source := D.source
  target := D.target
  source_selfAdjoint :=
    realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
      T hCompact hPositive
  target_selfAdjoint :=
    explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isSelfAdjoint M
  source_hasCore := D.source_hasCore
  target_mem := D.target_mem
  core_intertwines := D.core_intertwines

/-- One transfer-side operator core and exact core action agreement generate the
full unitary equivalence, exact domain transport, and operator intertwining
between the positive-support logarithmic generator and the reconstructed
Wightman Hamiltonian on `Ω⊥`. -/
noncomputable def
    CompactPositiveTransferLogGeneratorWightmanCommonCoreData.toUnitaryIntertwining
    {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanCommonCoreData
      (C := C) T hCompact hPositive M) :
    RealLinearPMapUnitaryIntertwining
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
      M.canonicalVacuumOrthogonalHamiltonian :=
  D.toClosedSubspaceSelfAdjointCommonCore.toUnitaryIntertwining

/-- Consequently the actual nonzero point energies of the transfer logarithmic
generator and the Wightman `Ω⊥` Hamiltonian agree without assuming spectral
identity or a global operator-level bridge. -/
theorem compactPositiveTransferLogGenerator_pointEnergySet_eq_wightman
    {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : CompactPositiveTransferLogGeneratorWightmanCommonCoreData
      (C := C) T hCompact hPositive M) :
    realLinearPMapPointEnergySet
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive) =
      realLinearPMapPointEnergySet M.canonicalVacuumOrthogonalHamiltonian :=
  realLinearPMapPointEnergySet_eq_of_unitaryIntertwining
    (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
    M.canonicalVacuumOrthogonalHamiltonian
    D.toUnitaryIntertwining

/-- The generic common-core package can therefore be consumed anywhere a full
operator-level transfer/Wightman bridge is expected, after a concrete transfer
operator is substituted. -/
noncomputable def
    compactPositiveTransferLogGeneratorWightmanIntertwining_of_commonCore
    {C : Type} [NormedAddCommGroup C] [NormedSpace ℝ C]
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : CompactPositiveTransferLogGeneratorWightmanCommonCoreData
      (C := C) T hCompact hPositive M) :
    RealLinearPMapUnitaryIntertwining
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
      M.canonicalVacuumOrthogonalHamiltonian :=
  D.toUnitaryIntertwining

end

end MathlibAnalytic
end MGAP4D
