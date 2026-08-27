import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairSemigroup
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationNativePairIsometry
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- A bounded real-Hilbert endomorphism whose operator norm is bounded by `C`
has every matrix element bounded by `C * ‖u‖ * ‖v‖`.  This isolates the
Hilbert-space argument from the large dependent physical carrier below. -/
theorem continuousLinearMap_abs_real_inner_apply_le_of_opNorm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E)
    {C : ℝ}
    (hA : ContinuousLinearMap.opNorm A ≤ C)
    (u v : E) :
    |inner ℝ u (A v)| ≤ C * ‖u‖ * ‖v‖ := by
  calc
    |inner ℝ u (A v)| ≤ ‖u‖ * ‖A v‖ :=
      abs_real_inner_le_norm u (A v)
    _ ≤ ‖u‖ * (ContinuousLinearMap.opNorm A * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg u)
    _ ≤ ‖u‖ * (C * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
        (norm_nonneg u)
    _ = C * ‖u‖ * ‖v‖ := by ring

local instance osBoundaryExcitationCompletedBoundaryMatrixElementSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedBoundaryMatrixElementSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedBoundaryMatrixElementSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedBoundaryMatrixElementSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedBoundaryMatrixElementSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedBoundaryMatrixElementSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedBoundaryMatrixElementSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The completed two-endpoint excitation matrix element on the actual shared
Wilson-boundary `L²` carrier.  Both vectors are represented through the exact
closed-sector boundary isometry, while the second vector is evolved by the
completed pair-Hilbert transfer semigroup. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) : ℝ :=
  inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
      H N hN beta hbeta u)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n v))

/-- The Wilson-boundary matrix element is exactly the intrinsic pair-Hilbert
sector matrix element because the boundary realization is a linear isometry. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_eq_pair_inner
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta n u v =
      inner ℝ u
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n v) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
      H N hN beta hbeta).inner_map_map u
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n v)

/-- At Euclidean time zero the completed Wilson-boundary matrix element is the
ordinary Hilbert inner product of the two completed excitation states. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta 0 u v = inner ℝ u v := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_eq_pair_inner]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_zero]
  rfl

/-- Additivity of Euclidean time becomes the exact matrix-element semigroup
law on the completed Wilson-boundary realization. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta (m + n) u v =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta m u
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n v) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_eq_pair_inner]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_add]
  rw [ContinuousLinearMap.comp_apply]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_eq_pair_inner]

/-- The doubled finite-volume transfer bound is therefore a genuine decay
estimate for every completed Wilson-boundary matrix element. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_abs_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta n u v| ≤
      Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) *
        ‖u‖ * ‖v‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_eq_pair_inner]
  exact
    continuousLinearMap_abs_real_inner_apply_le_of_opNorm_le
      (A := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_exp_of_pos
        H N hN beta hbeta n hn)
      u v

/-- Diagonal completed boundary matrix elements satisfy the corresponding
quadratic-norm decay estimate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_self_abs_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta n u u| ≤
      Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) *
        ‖u‖ ^ 2 := by
  simpa [pow_two] using
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_abs_le_exp_of_pos
      H N hN beta hbeta n hn u u

/-- In the concrete pair-`L²` realization, completed evolution on the dense
algebraic image is exactly the already-defined evolved algebraic endpoint-pair
kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding_transfer_apply_algebraic_evolved
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
            H N hN beta hbeta x)) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n x := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding_apply]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_apply_algebraic_pairL2]
  simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbeddingNativeLinearIsometry_apply] using
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativePairIsometry_intertwines
      H N hN beta hbeta n x

/-- After transport to the actual shared Wilson boundary, completed evolution
on the dense algebraic image is exactly the pre-existing algebraic evolved
boundary kernel. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding_transfer_apply_algebraic_evolved
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
            H N hN beta hbeta x)) =
      periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n x := by
  change
    periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
            H N hN beta hbeta x))) =
      periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n x
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding_transfer_apply_algebraic_evolved]
  rfl

/-- The unevolved dense algebraic image has the same exact Wilson-boundary
representative as the time-zero algebraic evolved embedding. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding_apply_algebraic_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta x) =
      periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta 0 x := by
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding_transfer_apply_algebraic_evolved
      H N hN beta hbeta 0 x

/-- Dense algebraic receipt for the completed matrix element: on the canonical
algebraic image it is exactly the inner product of the old time-zero and
time-`n` Wilson-boundary evolved kernels. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_apply_algebraic
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (x y : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta x)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta y) =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta 0 x)
        (periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta n y) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding_apply_algebraic_zero]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding_transfer_apply_algebraic_evolved]

/-- Consequently the pre-existing algebraic Wilson-boundary kernels inherit
the completed full-sector matrix-element decay, with the native tensor norms
on both algebraic arguments. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorMatrixElement_abs_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (x y : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    |inner ℝ
        (periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta 0 x)
        (periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta n y)| ≤
      Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) *
        ‖x‖ * ‖y‖ := by
  calc
    |inner ℝ
        (periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta 0 x)
        (periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta n y)| =
      |periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
        H N hN beta hbeta n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta x)
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta y)| := by
        rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_apply_algebraic]
    _ ≤ Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta x‖ *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta y‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_abs_le_exp_of_pos
        H N hN beta hbeta n hn _ _
    _ = Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) *
        ‖x‖ * ‖y‖ := by
      rw [
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta).norm_map x,
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta).norm_map y]

/-- Audit-visible package for completed Wilson-boundary matrix elements. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedBoundaryMatrixElementPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  zeroTime :
    ∀ u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
          H N hN beta hbeta 0 u v = inner ℝ u v
  addTime :
    ∀ (m n : ℕ)
      (u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
          H N hN beta hbeta (m + n) u v =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
          H N hN beta hbeta m u
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n v)
  doubledMatrixElementDecay :
    ∀ (n : ℕ), 0 < n →
      ∀ u v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta,
        |periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement
            H N hN beta hbeta n u v| ≤
          Real.exp
              (-2 * (n : ℝ) *
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
                  H N hN beta hbeta) *
            ‖u‖ * ‖v‖
  denseBoundaryReceipt :
    ∀ (n : ℕ)
      (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
              H N hN beta hbeta x)) =
        periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta n x

/-- Construct the completed Wilson-boundary matrix-element package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedBoundaryMatrixElementPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedBoundaryMatrixElementPackage
      H N hN beta hbeta :=
  { zeroTime :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_zero
        H N hN beta hbeta
    addTime :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_add
        H N hN beta hbeta
    doubledMatrixElementDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedBoundaryMatrixElement_abs_le_exp_of_pos
        H N hN beta hbeta
    denseBoundaryReceipt :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationBoundaryHilbertSectorEmbedding_transfer_apply_algebraic_evolved
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
