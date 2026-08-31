import MGAP4D.MathlibAnalytic.DenseLinearIsometryCompletionEquiv
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorWightmanExactGapCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function MeasureTheory Set Module End Filter
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

/-- Two dense isometric realizations of one common real normed core determine a
canonical linear-isometric equivalence between the two complete Hilbert
carriers.  The equivalence is obtained by identifying both carriers with
Mathlib's canonical completion of the common core. -/
noncomputable def realHilbertDenseCoreLinearIsometryEquiv
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (source : C →ₗᵢ[ℝ] E) (source_dense : DenseRange source)
    (target : C →ₗᵢ[ℝ] F) (target_dense : DenseRange target) :
    E ≃ₗᵢ[ℝ] F :=
  (denseLinearIsometryCompletionEquiv source source_dense).symm.trans
    (denseLinearIsometryCompletionEquiv target target_dense)

/-- The induced carrier equivalence agrees exactly with the two original dense
core realizations. -/
@[simp] theorem realHilbertDenseCoreLinearIsometryEquiv_apply_source
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (source : C →ₗᵢ[ℝ] E) (source_dense : DenseRange source)
    (target : C →ₗᵢ[ℝ] F) (target_dense : DenseRange target)
    (x : C) :
    realHilbertDenseCoreLinearIsometryEquiv
        source source_dense target target_dense (source x) =
      target x := by
  change
    denseLinearIsometryCompletionEquiv target target_dense
        ((denseLinearIsometryCompletionEquiv source source_dense).symm
          (source x)) =
      target x
  rw [← denseLinearIsometryCompletionEquiv_apply_coe source source_dense x]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  exact denseLinearIsometryCompletionEquiv_apply_coe target target_dense x

/-- Dense-core input for unitary intertwining of partially-defined real-linear
operators.

Compared with `RealLinearPMapUnitaryIntertwining`, the global carrier
`equiv` and its norm preservation are no longer supplied as independent data.
They are generated canonically from the two dense linear isometries of one
common core.  The remaining operator-specific obligations are exactly domain
transport and operator intertwining for that generated equivalence. -/
structure RealLinearPMapDenseCoreIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F) where
  source : C →ₗᵢ[ℝ] E
  target : C →ₗᵢ[ℝ] F
  source_dense : DenseRange source
  target_dense : DenseRange target
  domain_iff : ∀ x : E,
    x ∈ A.domain ↔
      realHilbertDenseCoreLinearIsometryEquiv
        source source_dense target target_dense x ∈ B.domain
  intertwines : ∀ x : A.domain,
    B ⟨realHilbertDenseCoreLinearIsometryEquiv
          source source_dense target target_dense (x : E),
        (domain_iff (x : E)).1 x.property⟩ =
      realHilbertDenseCoreLinearIsometryEquiv
        source source_dense target target_dense (A x)

/-- Common dense-core data automatically generate the previous operator-level
unitary intertwining structure. -/
noncomputable def RealLinearPMapDenseCoreIntertwining.toUnitaryIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapDenseCoreIntertwining A B) :
    RealLinearPMapUnitaryIntertwining A B := by
  let U := realHilbertDenseCoreLinearIsometryEquiv
    D.source D.source_dense D.target D.target_dense
  exact
    { equiv := U.toLinearEquiv
      norm_map := U.norm_map
      domain_iff := D.domain_iff
      intertwines := D.intertwines }

/-- Consequently, equality of point-energy sets follows from dense-core
intertwining without separately postulating a global Hilbert equivalence. -/
theorem realLinearPMapPointEnergySet_eq_of_denseCoreIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F)
    (D : RealLinearPMapDenseCoreIntertwining A B) :
    realLinearPMapPointEnergySet A = realLinearPMapPointEnergySet B :=
  realLinearPMapPointEnergySet_eq_of_unitaryIntertwining
    A B D.toUnitaryIntertwining

local instance denseCoreWightmanSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance denseCoreWightmanSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance denseCoreWightmanSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance denseCoreWightmanSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance denseCoreWightmanSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance denseCoreWightmanSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance denseCoreWightmanPairHilbertSectorComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta
local instance denseCoreWightmanSpectralSupportNormedSpace
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  infer_instance
local instance denseCoreWightmanSpectralSupportComplete
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
  exact
    (realHilbertZeroEigenspaceSupport_isClosed
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)).completeSpace_coe

/-- Dense-core form of the present transfer-log-generator/Wightman frontier.

The common core is deliberately abstract here: the next model-facing step may
instantiate it by the algebraic physical excitation tensor core after proving
that its OS state realization lands densely in the strictly-positive transfer
support and in the reconstructed vacuum-orthogonal Hilbert space. -/
structure PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanDenseCoreIntertwining
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) where
  Core : Type
  [coreNormedAddCommGroup : NormedAddCommGroup Core]
  [coreNormedSpace : NormedSpace ℝ Core]
  denseCoreIntertwining :
    RealLinearPMapDenseCoreIntertwining
      (C := Core)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta)
      M.canonicalVacuumOrthogonalHamiltonian

attribute [instance]
  PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanDenseCoreIntertwining.coreNormedAddCommGroup
  PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanDenseCoreIntertwining.coreNormedSpace

/-- A common dense-core realization discharges the global carrier-equivalence
part of the existing OS/Wightman operator bridge automatically. -/
noncomputable def PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanDenseCoreIntertwining.toIntertwining
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanDenseCoreIntertwining
      H N hN beta hbeta M) :
    PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
      H N hN beta hbeta M :=
  { unitaryIntertwining := D.denseCoreIntertwining.toUnitaryIntertwining }

/-- The transfer and Wightman point-energy sets therefore agree directly from
common dense-core data. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman_of_denseCore
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanDenseCoreIntertwining
      H N hN beta hbeta M) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta =
      M.canonicalVacuumOrthogonalPointSpectrum :=
  periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
    H N hN beta hbeta M (D.toIntertwining H N hN beta hbeta M)

/-- Dense-core data can be fed directly into the terminal mass-gap certificate;
no independently chosen global unitary equivalence is needed. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate_of_denseCore
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ)
    (D : PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanDenseCoreIntertwining
      H N hN beta hbeta M)
    (P : ExplicitWightmanOSCanonicalPointSpectrumBridge M)
    (hGap : M.HasMassGap m)
    (hMem : m ∈ M.hamiltonianEnergySpectrum) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
      H N hN beta hbeta M m :=
  { operatorIntertwining := D.toIntertwining H N hN beta hbeta M
    wightmanPointSpectrum := P
    massGap := hGap
    gapMem := hMem }

end

end MathlibAnalytic
end MGAP4D
