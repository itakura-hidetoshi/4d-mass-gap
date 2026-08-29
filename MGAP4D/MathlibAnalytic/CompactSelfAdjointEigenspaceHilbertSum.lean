import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactSpectrum
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End
open scoped InnerProductSpace TensorProduct lp

noncomputable section

/-- A compact symmetric bounded operator on a complete real Hilbert space is
canonically a Hilbert sum of its eigenspaces.  This is the infinite-dimensional
compact analogue of finite-dimensional eigenspace diagonalization. -/
theorem realHilbertCompactSymmetric_eigenspaces_isHilbertSum
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hSymm : T.IsSymmetric) :
    IsHilbertSum ℝ
      (fun mu : Eigenvalues (T : Module.End ℝ E) =>
        eigenspace (T : Module.End ℝ E) mu)
      (fun mu => (eigenspace (T : Module.End ℝ E) mu).subtypeₗᵢ) := by
  have hOrthogonalComplement :
      (⨆ mu : Eigenvalues (T : Module.End ℝ E),
        eigenspace (T : Module.End ℝ E) mu)ᗮ = ⊥ := by
    show
      (⨆ mu : {mu // eigenspace (T : Module.End ℝ E) mu ≠ ⊥},
        eigenspace (T : Module.End ℝ E) mu)ᗮ = ⊥
    rw [iSup_ne_bot_subtype]
    exact
      ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
        hCompact hSymm
  have hTotal :
      ⊤ ≤
        (⨆ mu : Eigenvalues (T : Module.End ℝ E),
          eigenspace (T : Module.End ℝ E) mu).topologicalClosure := by
    rw [top_le_iff, Submodule.topologicalClosure_eq_top_iff]
    exact hOrthogonalComplement
  letI :
      ∀ mu : Eigenvalues (T : Module.End ℝ E),
        CompleteSpace (eigenspace (T : Module.End ℝ E) mu) :=
    fun _ => by infer_instance
  exact
    IsHilbertSum.mkInternal
      hSymm.orthogonalFamily_eigenspaces'
      hTotal

/-- Intrinsic spectral coordinates for a compact symmetric real-Hilbert
operator.  The index is Mathlib's `Eigenvalues T` subtype, so no arbitrary
natural-number enumeration is introduced. -/
noncomputable def realHilbertCompactSymmetric_eigenspacesHilbertSumEquiv
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hSymm : T.IsSymmetric) :
    E ≃ₗᵢ[ℝ]
      lp
        (fun mu : Eigenvalues (T : Module.End ℝ E) =>
          eigenspace (T : Module.End ℝ E) mu)
        2 :=
  (realHilbertCompactSymmetric_eigenspaces_isHilbertSum
    T hCompact hSymm).linearIsometryEquiv

open Classical in
/-- An elementary Hilbert-sum vector supported in one eigenspace is exactly
the corresponding ambient eigenvector under the inverse spectral coordinate
map. -/
theorem realHilbertCompactSymmetric_eigenspacesHilbertSumEquiv_symm_single
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hSymm : T.IsSymmetric)
    (mu : Eigenvalues (T : Module.End ℝ E))
    (v : eigenspace (T : Module.End ℝ E) mu) :
    (realHilbertCompactSymmetric_eigenspacesHilbertSumEquiv
      T hCompact hSymm).symm (lp.single 2 mu v) = (v : E) := by
  let hSum :=
    realHilbertCompactSymmetric_eigenspaces_isHilbertSum
      T hCompact hSymm
  exact hSum.linearIsometryEquiv_symm_apply_single v

open Classical in
/-- On a single spectral coordinate the compact symmetric operator acts by
its eigenvalue.  This is the exact diagonal-action receipt needed before
replacing the bounded weight `mu` by `-log mu` on the nonzero spectral support. -/
theorem realHilbertCompactSymmetric_apply_eigenspacesHilbertSumEquiv_symm_single
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hSymm : T.IsSymmetric)
    (mu : Eigenvalues (T : Module.End ℝ E))
    (v : eigenspace (T : Module.End ℝ E) mu) :
    T
        ((realHilbertCompactSymmetric_eigenspacesHilbertSumEquiv
          T hCompact hSymm).symm (lp.single 2 mu v)) =
      (mu : ℝ) •
        (realHilbertCompactSymmetric_eigenspacesHilbertSumEquiv
          T hCompact hSymm).symm (lp.single 2 mu v) := by
  rw [realHilbertCompactSymmetric_eigenspacesHilbertSumEquiv_symm_single]
  exact mem_eigenspace_iff.mp v.property

local instance osBoundaryExcitationCompletedPairEigenHilbertSumSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedPairEigenHilbertSumSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedPairEigenHilbertSumSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedPairEigenHilbertSumSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedPairEigenHilbertSumSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedPairEigenHilbertSumSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedPairEigenHilbertSumSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

local instance osBoundaryExcitationCompletedPairEigenHilbertSumPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- The actual completed one-step excitation pair sector is the Hilbert sum of
the eigenspaces of its compact positive transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_eigenspaces_isHilbertSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsHilbertSum ℝ
      (fun mu : Eigenvalues
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1 :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta)) =>
        eigenspace
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1 :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta))
          mu)
      (fun mu =>
        (eigenspace
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1 :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta))
          mu).subtypeₗᵢ) := by
  let T :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
      H N hN beta hbeta 1
  exact
    realHilbertCompactSymmetric_eigenspaces_isHilbertSum
      T
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
        H N hN beta hbeta 1 (by norm_num))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isPositive
        H N hN beta hbeta 1).isSymmetric

/-- Canonical eigenspace Hilbert-sum coordinates for the actual completed
one-step pair transfer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_eigenspacesHilbertSumEquiv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta ≃ₗᵢ[ℝ]
      lp
        (fun mu : Eigenvalues
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1 :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta)) =>
          eigenspace
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
              H N hN beta hbeta 1 :
              Module.End ℝ
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                  H N hN beta hbeta))
            mu)
        2 :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_eigenspaces_isHilbertSum
    H N hN beta hbeta).linearIsometryEquiv

/-- Audit-visible package for the intrinsic spectral Hilbert-sum
identification of the completed one-step pair transfer. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairEigenHilbertSumPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  eigenspacesHilbertSum :
    IsHilbertSum ℝ
      (fun mu : Eigenvalues
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta 1 :
          Module.End ℝ
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
              H N hN beta hbeta)) =>
        eigenspace
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1 :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta))
          mu)
      (fun mu =>
        (eigenspace
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta 1 :
            Module.End ℝ
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
                H N hN beta hbeta))
          mu).subtypeₗᵢ)

/-- Construct the completed pair eigenspace Hilbert-sum package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedPairEigenHilbertSumPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairEigenHilbertSumPackage
      H N hN beta hbeta :=
  ⟨periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_one_eigenspaces_isHilbertSum
      H N hN beta hbeta⟩

end

end MathlibAnalytic
end MGAP4D
