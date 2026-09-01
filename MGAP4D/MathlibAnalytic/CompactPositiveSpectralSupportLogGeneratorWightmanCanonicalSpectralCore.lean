import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorSpectralCore
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorWightmanSelfAdjointCommonCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Module End MeasureTheory Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

local instance canonicalSpectralCoreSupportComplete
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- The canonical source realization used by the transfer/Wightman bridge is
just inclusion of the intrinsic algebraic spectral core into the strictly
positive transfer support. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive
      →ₗᵢ[ℝ] realHilbertZeroEigenspaceSupport T where
  toLinearMap :=
    (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
      T hPositive).subtype
  norm_map' := by
    intro x
    rfl

/-- The canonical spectral-core inclusion has dense range.  This is exactly the
carrier-density theorem proved from the intrinsic Hilbert-sum expansion. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion_denseRange
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    DenseRange
      (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
        T hPositive) := by
  rw [DenseRange, dense_iff_closure_eq]
  have hRange :
      Set.range
          (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
            T hPositive) =
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
          T hPositive : Set (realHilbertZeroEigenspaceSupport T)) := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact c.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hRange, ← Submodule.topologicalClosure_coe,
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore_topologicalClosure_eq_top
      T hCompact hPositive]
  rfl

/-- As a linear submodule, the range of the canonical inclusion is literally
the intrinsic algebraic spectral core. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion_range
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    LinearMap.range
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
          T hPositive).toLinearMap =
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
        T hPositive := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact c.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Hence the `HasCore` receipt required by self-adjoint maximality is no longer
model-facing: it is generated canonically from compact-positive spectral
theory. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_hasCore_canonicalSpectralCoreRange
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).HasCore
      (LinearMap.range
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
          T hPositive).toLinearMap) := by
  rw [realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion_range]
  exact
    realHilbertCompactPositiveZeroSupportLogGenerator_hasCore_spectralCore
      T hCompact hPositive

/-- Reduced model-facing data for transfer/Wightman identification.

The common core is fixed canonically to the algebraic span of actual positive
transfer eigenspaces.  Therefore there is no source realization field and no
source `HasCore` field.  The only remaining geometric realization is the map of
that canonical transfer core into reconstructed Wightman `Ω⊥`, together with
Wightman-domain membership and exact Hamiltonian action agreement on the core.
-/
structure CompactPositiveTransferLogGeneratorWightmanCanonicalSpectralCoreData
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (M : ExplicitWightmanOSReconstructedModel) where
  target :
    RealHilbertClosedSubspaceDenseCoreRealization
      (C := realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
        T hPositive)
      M.vacuumOrthogonal
  target_mem : ∀ c :
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive,
    RealHilbertClosedSubspaceDenseCoreRealization.corestrict target c ∈
      M.canonicalVacuumOrthogonalHamiltonian.domain
  core_intertwines : ∀ c :
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive,
    M.canonicalVacuumOrthogonalHamiltonian
        ⟨RealHilbertClosedSubspaceDenseCoreRealization.corestrict target c,
          target_mem c⟩ =
      realHilbertDenseCoreLinearIsometryEquiv
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
          T hPositive)
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion_denseRange
          T hCompact hPositive)
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict target)
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange target)
        (realHilbertCompactPositiveZeroSupportLogGenerator
          T hCompact hPositive
          ⟨realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
              T hPositive c,
            (realHilbertCompactPositiveZeroSupportLogGenerator_hasCore_canonicalSpectralCoreRange
              T hCompact hPositive).le_domain ⟨c, rfl⟩⟩)

/-- The reduced canonical-spectral-core package instantiates the generic
self-adjoint common-core maximality theorem with no source-side hard input. -/
noncomputable def
    CompactPositiveTransferLogGeneratorWightmanCanonicalSpectralCoreData.toSelfAdjointCommonCore
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanCanonicalSpectralCoreData
      T hCompact hPositive M) :
    RealLinearPMapSelfAdjointCommonCoreIntertwining
      (C := realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
        T hPositive)
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
      M.canonicalVacuumOrthogonalHamiltonian where
  source :=
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
      T hPositive
  target :=
    RealHilbertClosedSubspaceDenseCoreRealization.corestrict D.target
  source_dense :=
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion_denseRange
      T hCompact hPositive
  target_dense :=
    RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange D.target
  source_selfAdjoint :=
    realHilbertCompactPositiveZeroSupportLogGenerator_isSelfAdjoint
      T hCompact hPositive
  target_selfAdjoint :=
    explicit_wightman_os_canonical_vacuum_orthogonal_hamiltonian_isSelfAdjoint M
  source_hasCore :=
    realHilbertCompactPositiveZeroSupportLogGenerator_hasCore_canonicalSpectralCoreRange
      T hCompact hPositive
  target_mem := D.target_mem
  core_intertwines := D.core_intertwines

/-- Canonical spectral-core realization data generate the full transfer ↔
Wightman unitary intertwining. -/
noncomputable def
    CompactPositiveTransferLogGeneratorWightmanCanonicalSpectralCoreData.toUnitaryIntertwining
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanCanonicalSpectralCoreData
      T hCompact hPositive M) :
    RealLinearPMapUnitaryIntertwining
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
      M.canonicalVacuumOrthogonalHamiltonian :=
  D.toSelfAdjointCommonCore.toUnitaryIntertwining

/-- The actual nonzero point-energy sets therefore agree from Wightman-side
realization/action data alone. -/
theorem compactPositiveTransferLogGenerator_pointEnergySet_eq_wightman_of_canonicalSpectralCore
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : CompactPositiveTransferLogGeneratorWightmanCanonicalSpectralCoreData
      T hCompact hPositive M) :
    realLinearPMapPointEnergySet
        (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive) =
      realLinearPMapPointEnergySet M.canonicalVacuumOrthogonalHamiltonian :=
  realLinearPMapPointEnergySet_eq_of_unitaryIntertwining
    (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
    M.canonicalVacuumOrthogonalHamiltonian
    D.toUnitaryIntertwining

local instance canonicalSpectralCoreSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance canonicalSpectralCoreSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance canonicalSpectralCoreSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance canonicalSpectralCoreSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance canonicalSpectralCoreSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance canonicalSpectralCoreSpatialSliceHaarSFinite
    (H N : ℕ) : SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance canonicalSpectralCorePairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Reduced common-core data specialized to the actual one-step SU(N) physical
excitation-pair transfer.  The source core, its density, its operator-core
property, compactness, positivity, and both self-adjointness receipts are all
canonical consequences rather than fields. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCanonicalSpectralCoreData
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) :=
  CompactPositiveTransferLogGeneratorWightmanCanonicalSpectralCoreData
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta 1 (by norm_num))
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1)
    M

/-- The physical transfer/Wightman operator bridge follows from the canonical
transfer spectral core and Wightman-side realization/action data alone. -/
noncomputable def
    PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCanonicalSpectralCoreData.toIntertwining
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCanonicalSpectralCoreData
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
      (show CompactPositiveTransferLogGeneratorWightmanCanonicalSpectralCoreData
          T hCompact hPositive M from D).toUnitaryIntertwining
  refine ⟨?_⟩
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator,
    T, hCompact, hPositive] using I

/-- The terminal transfer/Wightman point-spectrum equality is now generated
without any source-core realization or `HasCore` assumption. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman_of_canonicalSpectralCore
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanCanonicalSpectralCoreData
      H N hN beta hbeta M) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta =
      M.canonicalVacuumOrthogonalPointSpectrum :=
  periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
    H N hN beta hbeta M (D.toIntertwining H N hN beta hbeta M)

end

end MathlibAnalytic
end MGAP4D
