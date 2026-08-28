import MGAP4D.MathlibAnalytic.HilbertTensorCompactCompletion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

/-- A positive power of a compact bounded operator on a complete real Hilbert
space has compact completed tensor square.  Keeping power compactness inside
this generic Hilbert carrier prevents concrete dependent subtypes from being
reduced while the power algebra and compact-operator coercion are elaborated. -/
theorem realHilbertCompact_pow_tensorSquareCompletion_isCompact_of_pos
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (A : E →L[ℝ] E)
    (hA : IsCompactOperator A)
    (n : ℕ)
    (hn : 0 < n) :
    IsCompactOperator ((hilbertTensorMap (A ^ n) (A ^ n)).completion) := by
  have hAn : IsCompactOperator (A ^ n) := by
    cases n with
    | zero => omega
    | succ k =>
        rw [pow_succ']
        exact hA.comp_clm (A ^ k)
  exact realHilbertCompact_tensorSquareCompletion_isCompact (A ^ n) hAn

/-- Compactness is invariant under conjugation by a linear isometry
equivalence.  This is the compactness counterpart of the semigroup
conjugation lemmas used by the completed pair transfer. -/
theorem continuousLinearMapConjugateLinearIsometryEquiv_isCompact
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (U : E ≃ₗᵢ[𝕜] F)
    (A : E →L[𝕜] E)
    (hA : IsCompactOperator A) :
    IsCompactOperator (continuousLinearMapConjugateLinearIsometryEquiv U A) := by
  unfold continuousLinearMapConjugateLinearIsometryEquiv
  exact
    (hA.clm_comp (U : E →L[𝕜] F)).comp_clm
      (U.symm : F →L[𝕜] E)

local instance osBoundaryExcitationCompletedPairCompactnessSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedPairCompactnessSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedPairCompactnessSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedPairCompactnessSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedPairCompactnessSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedPairCompactnessSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedPairCompactnessSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The finite-volume gauge-invariant one-slice physical carrier is complete. -/
local instance osBoundaryExcitationCompletedPairCompactnessPhysicalSliceComplete
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

/-- The orthogonal excitation one-slice carrier is complete as a closed
subspace of the complete physical one-slice Hilbert space. -/
local instance osBoundaryExcitationCompletedPairCompactnessExcitationSliceComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :=
  ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta).isClosed_orthogonal).completeSpace_coe

/-- Keep Mathlib's native Hilbert tensor norm explicit on the algebraic
excitation tensor carrier whose completion is used by the pair semigroup. -/
@[reducible] local instance osBoundaryExcitationCompletedPairCompactnessNormedAddCommGroup
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    NormedAddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instNormedAddCommGroup
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

/-- The matching native tensor inner product. -/
@[reducible] local instance osBoundaryExcitationCompletedPairCompactnessInnerProductSpace
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    InnerProductSpace ℝ
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  TensorProduct.instInnerProductSpace
    (𝕜 := ℝ)
    (E := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (F := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)

/-- The actual normalized one-slice transfer restricted to the full
one-eigenspace orthogonal complement is compact. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_isCompact
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta) := by
  exact
    realHilbertTopEigenspaceOrthogonalRestriction_isCompact
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isCompact
        H N hN beta hbeta)

/-- Every positive-time native completed excitation tensor transfer is compact.
This is the direct concrete specialization of the generic completed Hilbert
tensor-square compactness theorem. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_isCompact_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta n) := by
  let R :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta →L[ℝ]
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  have hR : IsCompactOperator R := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_isCompact
        H N hN beta hbeta
  have hTensor :=
    @realHilbertCompact_pow_tensorSquareCompletion_isCompact_of_pos
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta)
      inferInstance
      (Submodule.innerProductSpace
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H N hN beta hbeta))
      (osBoundaryExcitationCompletedPairCompactnessExcitationSliceComplete
        H N hN beta hbeta)
      R hR n hn
  change
    IsCompactOperator
      ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n).completion)
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_eq_hilbertTensorMap]
  simpa [R] using hTensor

/-- The actual completed transfer on the concrete pair-Hilbert excitation
sector is compact at every positive Euclidean time. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
  exact
    continuousLinearMapConjugateLinearIsometryEquiv_isCompact
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_isCompact_of_pos
        H N hN beta hbeta n hn)

/-- Audit-visible package recording the completed-pair compactness frontier. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactnessPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  oneSliceOrthogonalCompact :
    IsCompactOperator
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta)
  positiveNativeCompletionCompact :
    ∀ n : ℕ, 0 < n →
      IsCompactOperator
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
          H N hN beta hbeta n)
  positivePairSectorCompact :
    ∀ n : ℕ, 0 < n →
      IsCompactOperator
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n)

/-- The finite-volume completed pair transfer satisfies the full compactness
package at every positive Euclidean time. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactnessPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairCompactnessPackage
      H N hN beta hbeta :=
  ⟨periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_isCompact
      H N hN beta hbeta,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_isCompact_of_pos
      H N hN beta hbeta,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_isCompact_of_pos
      H N hN beta hbeta⟩

end

end MathlibAnalytic
end MGAP4D
