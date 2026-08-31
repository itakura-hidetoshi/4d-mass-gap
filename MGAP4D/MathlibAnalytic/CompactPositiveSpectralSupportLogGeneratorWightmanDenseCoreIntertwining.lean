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
carriers.  Both carriers are identified with Mathlib's canonical completion of
the common core. -/
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
        source source_dense target target_dense (source x) = target x := by
  change
    denseLinearIsometryCompletionEquiv target target_dense
        ((denseLinearIsometryCompletionEquiv source source_dense).symm
          (source x)) = target x
  rw [← denseLinearIsometryCompletionEquiv_apply_coe source source_dense x]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  exact denseLinearIsometryCompletionEquiv_apply_coe target target_dense x

/-- Dense-core input for unitary intertwining of partially-defined real-linear
operators.  The global carrier equivalence and its norm preservation are not
fields: they are generated canonically from `source` and `target`. -/
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
    (D : RealLinearPMapDenseCoreIntertwining (C := C) A B) :
    RealLinearPMapUnitaryIntertwining A B := by
  let U : E ≃ₗᵢ[ℝ] F :=
    realHilbertDenseCoreLinearIsometryEquiv
      D.source D.source_dense D.target D.target_dense
  exact
    { equiv := U.toLinearEquiv
      norm_map := U.norm_map
      domain_iff := D.domain_iff
      intertwines := D.intertwines }

/-- Equality of point-energy sets follows from dense-core intertwining without
separately postulating a global Hilbert equivalence. -/
theorem realLinearPMapPointEnergySet_eq_of_denseCoreIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F)
    (D : RealLinearPMapDenseCoreIntertwining (C := C) A B) :
    realLinearPMapPointEnergySet A = realLinearPMapPointEnergySet B :=
  realLinearPMapPointEnergySet_eq_of_unitaryIntertwining A B
    (D.toUnitaryIntertwining (C := C) (E := E) (F := F) (A := A) (B := B))

/-- Physical specialization of the dense-core reduction.

The support-space `NormedSpace` and completeness instances are explicit binders
here.  This keeps the theorem independent of the definitional instance path of
the closed spectral-support subtype while still allowing the repository's
canonical instances to discharge them at use sites. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman_of_denseCore
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    {Core : Type}
    [NormedAddCommGroup Core] [NormedSpace ℝ Core]
    [NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)]
    [CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)]
    (D : RealLinearPMapDenseCoreIntertwining
      (C := Core)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta)
      M.canonicalVacuumOrthogonalHamiltonian) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta = M.canonicalVacuumOrthogonalPointSpectrum := by
  exact realLinearPMapPointEnergySet_eq_of_denseCoreIntertwining
    (C := Core)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
      H N hN beta hbeta)
    M.canonicalVacuumOrthogonalHamiltonian D

/-- Dense-core data generate the existing physical OS/Wightman operator bridge.
No independently chosen global unitary equivalence or norm-preservation field
is required. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining_of_denseCore
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    {Core : Type}
    [NormedAddCommGroup Core] [NormedSpace ℝ Core]
    [NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)]
    [CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)]
    (D : RealLinearPMapDenseCoreIntertwining
      (C := Core)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta)
      M.canonicalVacuumOrthogonalHamiltonian) :
    PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
      H N hN beta hbeta M :=
  { unitaryIntertwining :=
      D.toUnitaryIntertwining
        (C := Core)
        (E := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta)
        (F := M.VacuumOrthogonalHilbert) }

/-- Dense-core data can be fed directly into the terminal mass-gap certificate.
The global Hilbert equivalence is theorem-generated from the common core. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate_of_denseCore
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ)
    {Core : Type}
    [NormedAddCommGroup Core] [NormedSpace ℝ Core]
    [NormedSpace ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)]
    [CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta)]
    (D : RealLinearPMapDenseCoreIntertwining
      (C := Core)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta)
      M.canonicalVacuumOrthogonalHamiltonian)
    (P : ExplicitWightmanOSCanonicalPointSpectrumBridge M)
    (hGap : M.HasMassGap m)
    (hMem : m ∈ M.hamiltonianEnergySpectrum) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
      H N hN beta hbeta M m :=
  { operatorIntertwining :=
      periodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining_of_denseCore
        H N hN beta hbeta M D
    wightmanPointSpectrum := P
    massGap := hGap
    gapMem := hMem }

end

end MathlibAnalytic
end MGAP4D
