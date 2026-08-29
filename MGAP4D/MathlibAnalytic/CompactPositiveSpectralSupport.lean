import MGAP4D.MathlibAnalytic.CompactSelfAdjointEigenspaceHilbertSum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace TensorProduct lp

noncomputable section

universe u

/-- The spectral support of a bounded real-Hilbert endomorphism: the
orthogonal complement of its zero eigenspace.  This is the correct carrier for
a logarithmic generator when zero may remain in the compact spectrum. -/
noncomputable def realHilbertZeroEigenspaceSupport
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) : Submodule ℝ E :=
  (eigenspace (T : Module.End ℝ E) 0)ᗮ

/-- The spectral support is closed, hence complete when the ambient Hilbert
space is complete. -/
theorem realHilbertZeroEigenspaceSupport_isClosed
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) :
    IsClosed ((realHilbertZeroEigenspaceSupport T : Submodule ℝ E) : Set E) := by
  exact (eigenspace (T : Module.End ℝ E) 0).isClosed_orthogonal

local instance realHilbertZeroEigenspaceSupportComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- Symmetry makes the zero-eigenspace support invariant. -/
theorem realHilbertZeroEigenspaceSupport_invariant
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric)
    {x : E}
    (hx : x ∈ realHilbertZeroEigenspaceSupport T) :
    T x ∈ realHilbertZeroEigenspaceSupport T := by
  exact hSymm.invariant_orthogonalComplement_eigenspace 0 x hx

/-- Restrict a symmetric bounded operator to the orthogonal complement of its
zero eigenspace. -/
noncomputable def realHilbertZeroEigenspaceSupportRestriction
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric) :
    realHilbertZeroEigenspaceSupport T →L[ℝ]
      realHilbertZeroEigenspaceSupport T :=
  ((T.comp (realHilbertZeroEigenspaceSupport T).subtypeL).codRestrict
    (realHilbertZeroEigenspaceSupport T)
    (fun x => realHilbertZeroEigenspaceSupport_invariant T hSymm x.property))

@[simp] theorem realHilbertZeroEigenspaceSupportRestriction_coe
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric)
    (x : realHilbertZeroEigenspaceSupport T) :
    ((realHilbertZeroEigenspaceSupportRestriction T hSymm x :
        realHilbertZeroEigenspaceSupport T) : E) = T (x : E) := rfl

/-- Symmetry descends to the spectral-support restriction. -/
theorem realHilbertZeroEigenspaceSupportRestriction_isSymmetric
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric) :
    (realHilbertZeroEigenspaceSupportRestriction T hSymm).IsSymmetric := by
  intro x y
  change inner ℝ (T (x : E)) (y : E) = inner ℝ (x : E) (T (y : E))
  exact hSymm _ _

/-- Positivity descends to the spectral-support restriction. -/
theorem realHilbertZeroEigenspaceSupportRestriction_isPositive
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    ((realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        realHilbertZeroEigenspaceSupport T →L[ℝ]
          realHilbertZeroEigenspaceSupport T) :
      realHilbertZeroEigenspaceSupport T →ₗ[ℝ]
        realHilbertZeroEigenspaceSupport T).IsPositive := by
  refine ⟨?_, ?_⟩
  · exact realHilbertZeroEigenspaceSupportRestriction_isSymmetric T hPositive.isSymmetric
  · intro x
    change 0 ≤ RCLike.re (inner ℝ (T (x : E)) (x : E))
    exact hPositive.re_inner_nonneg_left (x : E)

/-- Compactness descends to the invariant closed spectral support. -/
theorem realHilbertZeroEigenspaceSupportRestriction_isCompact
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric)
    (hCompact : IsCompactOperator T) :
    IsCompactOperator (realHilbertZeroEigenspaceSupportRestriction T hSymm) := by
  let K := realHilbertZeroEigenspaceSupport T
  have hpre : IsCompactOperator (T.comp K.subtypeL) :=
    hCompact.comp_clm K.subtypeL
  have hclosed : IsClosed (K : Set E) := by
    simpa [K] using realHilbertZeroEigenspaceSupport_isClosed T
  have hcod := hpre.codRestrict
    (fun x => realHilbertZeroEigenspaceSupport_invariant T hSymm x.property)
    hclosed
  simpa [realHilbertZeroEigenspaceSupportRestriction, K] using hcod

/-- By construction the zero eigenspace of the support restriction is trivial.
This is a point-spectrum statement only: zero may still remain in the spectrum
as the accumulation point of nonzero compact eigenvalues. -/
theorem realHilbertZeroEigenspaceSupportRestriction_eigenspace_zero_eq_bot
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric) :
    eigenspace
        (realHilbertZeroEigenspaceSupportRestriction T hSymm :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T))
        0 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hRx : realHilbertZeroEigenspaceSupportRestriction T hSymm x = 0 := by
    have h := mem_eigenspace_iff.mp hx
    simpa using h
  have hTx : T (x : E) = 0 := by
    have h := congrArg
      (fun y : realHilbertZeroEigenspaceSupport T => (y : E)) hRx
    simpa using h
  have hxZero : (x : E) ∈ eigenspace (T : Module.End ℝ E) 0 := by
    rw [mem_eigenspace_iff]
    simpa using hTx
  have hxInf :
      (x : E) ∈
        eigenspace (T : Module.End ℝ E) 0 ⊓
          (eigenspace (T : Module.End ℝ E) 0)ᗮ :=
    ⟨hxZero, x.property⟩
  have hxBot : (x : E) ∈ (⊥ : Submodule ℝ E) := by
    simpa only [(eigenspace (T : Module.End ℝ E) 0).inf_orthogonal_eq_bot] using hxInf
  exact Subtype.ext (by simpa using hxBot)

/-- Equivalently, zero is not an eigenvalue of the spectral-support
restriction. -/
theorem realHilbertZeroEigenspaceSupportRestriction_not_hasEigenvalue_zero
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : T.IsSymmetric) :
    ¬ HasEigenvalue
      (realHilbertZeroEigenspaceSupportRestriction T hSymm :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) 0 := by
  rw [Module.End.hasEigenvalue_iff]
  exact not_ne_iff.mpr
    (realHilbertZeroEigenspaceSupportRestriction_eigenspace_zero_eq_bot T hSymm)

/-- Every eigenvalue of a positive spectral-support restriction is strictly
positive.  This is the exact positivity needed before applying `-log`. -/
theorem realHilbertZeroEigenspaceSupportRestriction_eigenvalue_pos
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T))) :
    0 < (mu : ℝ) := by
  have hNonneg : 0 ≤ (mu : ℝ) :=
    eigenvalue_nonneg_of_nonneg mu.property
      (fun x =>
        (realHilbertZeroEigenspaceSupportRestriction_isPositive T hPositive).re_inner_nonneg_right x)
  have hNe : (mu : ℝ) ≠ 0 := by
    intro hmu
    apply realHilbertZeroEigenspaceSupportRestriction_not_hasEigenvalue_zero T hPositive.isSymmetric
    have hEigen : HasEigenvalue
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) (mu : ℝ) :=
      mu.property
    rw [hmu] at hEigen
    exact hEigen
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- A compact positive operator decomposes, on its spectral support, as a
Hilbert sum indexed entirely by strictly positive eigenvalues. -/
theorem realHilbertCompactPositive_zeroEigenspaceSupport_eigenspaces_isHilbertSum
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    IsHilbertSum ℝ
      (fun mu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) =>
        eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu)
      (fun mu =>
        (eigenspace
          (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
            Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu).subtypeₗᵢ) := by
  exact
    realHilbertCompactSymmetric_eigenspaces_isHilbertSum
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric)
      (realHilbertZeroEigenspaceSupportRestriction_isCompact
        T hPositive.isSymmetric hCompact)
      (realHilbertZeroEigenspaceSupportRestriction_isSymmetric
        T hPositive.isSymmetric)

local instance osBoundaryExcitationPositiveSpectralSupportSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationPositiveSpectralSupportSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationPositiveSpectralSupportSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationPositiveSpectralSupportSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationPositiveSpectralSupportSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationPositiveSpectralSupportSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationPositiveSpectralSupportSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationPositiveSpectralSupportPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Spectral support of the actual completed one-step pair transfer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Submodule ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  realHilbertZeroEigenspaceSupport
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)

/-- Actual one-step transfer restricted to its strictly-positive spectral
support. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta :=
  realHilbertZeroEigenspaceSupportRestriction
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
      H N hN beta hbeta 1).isSymmetric

/-- The concrete support restriction is compact. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_isCompact
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta) := by
  exact
    realHilbertZeroEigenspaceSupportRestriction_isCompact
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1).isSymmetric
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))

/-- The concrete support restriction is positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_isPositive
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta →ₗ[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta).IsPositive := by
  exact
    realHilbertZeroEigenspaceSupportRestriction_isPositive
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1)

/-- Zero is not an eigenvalue on the concrete support carrier. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_not_hasEigenvalue_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ¬ HasEigenvalue
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta)) 0 := by
  exact
    realHilbertZeroEigenspaceSupportRestriction_not_hasEigenvalue_zero
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1).isSymmetric

/-- Every concrete support eigenvalue is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_eigenvalue_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (mu : Eigenvalues
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta))) :
    0 < (mu : ℝ) := by
  exact
    realHilbertZeroEigenspaceSupportRestriction_eigenvalue_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1)
      mu

/-- Audit package: the actual completed one-step transfer has a compact,
positive spectral-support restriction with no zero eigenvalue and only
strictly-positive Hilbert-sum eigenvalue coordinates. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationPositiveSpectralSupportPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  supportCompact :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta)
  supportPositive :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta →ₗ[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta).IsPositive
  zeroNotEigenvalue :
    ¬ HasEigenvalue
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta)) 0
  eigenvaluesPositive :
    ∀ mu : Eigenvalues
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction
        H N hN beta hbeta :
        Module.End ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
            H N hN beta hbeta)),
      0 < (mu : ℝ)

/-- Construct the positive spectral-support package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationPositiveSpectralSupportPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationPositiveSpectralSupportPackage
      H N hN beta hbeta :=
  { supportCompact :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_isCompact
        H N hN beta hbeta
    supportPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_isPositive
        H N hN beta hbeta
    zeroNotEigenvalue :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_not_hasEigenvalue_zero
        H N hN beta hbeta
    eigenvaluesPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportRestriction_eigenvalue_pos
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D