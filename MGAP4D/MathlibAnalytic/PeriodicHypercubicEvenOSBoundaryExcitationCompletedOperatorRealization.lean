import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationCompletedBoundaryMatrixElement
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationHilbertSchmidtOperatorCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance osBoundaryExcitationCompletedOperatorSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedOperatorSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedOperatorSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedOperatorSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedOperatorSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedOperatorSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedOperatorSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Generic norm-one lifting lemma kept separate from the dependent physical
carriers.  This prevents the operator-norm proof from asking definitional
equality to normalize the full Yang--Mills carrier at every point. -/
theorem continuousLinearMap_opNorm_le_one_of_apply_norm_le
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F)
    (hA : ∀ x, ‖A x‖ ≤ ‖x‖) :
    ContinuousLinearMap.opNorm A ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound zero_le_one
  intro x
  rw [one_mul]
  exact hA x

/-- Every completed pair-Hilbert excitation state has a canonical bounded
operator realization on the one-slice real Haar `L²` space.  The construction
uses the exact sector inclusion into pair-`L²` followed by the already
formalized Hilbert--Schmidt kernel-to-operator map. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N) :=
  (realL2HilbertSchmidtRectangularKernelToOperatorContinuousLinearMap
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding
      H N hN beta hbeta).toContinuousLinearMap

/-- Pointwise receipt: a completed state is realized as the Hilbert--Schmidt
operator of its concrete endpoint-pair `L²` kernel. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
        H N hN beta hbeta u =
      realL2HilbertSchmidtRectangularKernelOperator
        (u : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) := by
  rfl

/-- The completed state-to-operator realization is contractive: bounded
operator norm is controlled by the native pair-Hilbert norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_apply_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
        H N hN beta hbeta u‖ ≤ ‖u‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_apply]
  calc
    ‖realL2HilbertSchmidtRectangularKernelOperator
        (u : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)‖ ≤
      ‖(u : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N)‖ :=
        realL2HilbertSchmidtRectangularKernelOperator_norm_le _
    _ = ‖u‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorEmbedding_norm
        H N hN beta hbeta u

/-- Operator norm of the completed state-to-operator map is at most one. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_opNorm_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ContinuousLinearMap.opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
        H N hN beta hbeta) ≤ 1 :=
  continuousLinearMap_opNorm_le_one_of_apply_norm_le
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_apply_norm_le
      H N hN beta hbeta)

/-- Evolve a completed excitation state for `n` Euclidean slabs and then
realize the resulting pair kernel as a bounded one-slice operator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
    H N hN beta hbeta).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
        H N hN beta hbeta n u =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n u) :=
  rfl

/-- Time zero recovers the unevolved completed operator realization. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
        H N hN beta hbeta 0 =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
        H N hN beta hbeta := by
  apply ContinuousLinearMap.ext
  intro u
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_zero]
  rfl

/-- Exact whole-sector Euclidean-time semigroup law after bounded-operator
realization. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
        H N hN beta hbeta (m + n) =
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
        H N hN beta hbeta m).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply,
    ContinuousLinearMap.comp_apply]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_add]
  rfl

/-- The completed evolved operator realization inherits the doubled
finite-volume exponential decay pointwise on every completed excitation
state. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply_norm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (u : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
        H N hN beta hbeta n u‖ ≤
      Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) *
        ‖u‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply]
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n u)‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n u‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_apply_norm_le
        H N hN beta hbeta _
    _ ≤ ContinuousLinearMap.opNorm
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n) * ‖u‖ :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n).le_opNorm u
    _ ≤ Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) *
        ‖u‖ := by
      exact mul_le_mul_of_nonneg_right
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_exp_of_pos
          H N hN beta hbeta n hn)
        (norm_nonneg u)

/-- The same decay is an operator-norm estimate for the bounded linear map from
the entire completed pair-Hilbert sector into bounded one-slice operators. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_opNorm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    ContinuousLinearMap.opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
        H N hN beta hbeta n) ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  change
    ContinuousLinearMap.opNorm
      ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
          H N hN beta hbeta).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n)) ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta)
  have hEmbedding :
      ContinuousLinearMap.opNorm
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
          H N hN beta hbeta) ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_opNorm_le_one
      H N hN beta hbeta
  have hTransfer :
      ContinuousLinearMap.opNorm
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n) ≤
        Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_exp_of_pos
      H N hN beta hbeta n hn
  have hTransferNonneg :
      0 ≤ ContinuousLinearMap.opNorm
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n) := by
    exact norm_nonneg _
  calc
    ContinuousLinearMap.opNorm
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
            H N hN beta hbeta).comp
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n)) ≤
      ContinuousLinearMap.opNorm
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
            H N hN beta hbeta) *
        ContinuousLinearMap.opNorm
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n) := by
      exact
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
          H N hN beta hbeta).opNorm_comp_le
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
              H N hN beta hbeta n)
    _ ≤ 1 * ContinuousLinearMap.opNorm
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n) :=
      mul_le_mul_of_nonneg_right hEmbedding hTransferNonneg
    _ ≤ 1 * Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) :=
      mul_le_mul_of_nonneg_left hTransfer zero_le_one
    _ = Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) := one_mul _

/-- On the dense algebraic image, the completed operator realization is
exactly the pre-existing algebraic Hilbert--Schmidt operator embedding. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_apply_algebraic
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta x) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
        H N hN beta hbeta x := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_apply]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_coe]
  rfl

/-- Evolved dense algebraic receipt: completed transfer followed by the
operator realization agrees exactly with the old algebraic evolved operator
embedding on the whole tensor core. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply_algebraic
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
        H N hN beta hbeta n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta x) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
        H N hN beta hbeta n x := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_apply]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_apply_algebraic_pairL2]
  have hx :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n x =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n x := by
    change
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n).toLinearMap x =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n x
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_toLinearMap]
  rw [hx]
  rfl

/-- Pure tensors therefore recover the exact rank-one Hilbert--Schmidt
operator already constructed on the algebraic spine after completed evolution. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply_algebraic_tmul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
        H N hN beta hbeta n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta (f ⊗ₜ[ℝ] g)) =
      realL2HilbertSchmidtRectangularKernelOperator
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer
          H N hN beta hbeta n f g) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply_algebraic]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_tmul
      H N hN beta hbeta n f g

/-- Audit-visible package for the completed concrete operator realization. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedOperatorRealizationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  contractiveRealization :
    ContinuousLinearMap.opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
        H N hN beta hbeta) ≤ 1
  zeroTime :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
        H N hN beta hbeta 0 =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding
        H N hN beta hbeta
  addTime :
    ∀ m n : ℕ,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
          H N hN beta hbeta (m + n) =
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
          H N hN beta hbeta m).comp
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n)
  doubledOperatorDecay :
    ∀ (n : ℕ), 0 < n →
      ContinuousLinearMap.opNorm
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
          H N hN beta hbeta n) ≤
        Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta)
  denseReceipt :
    ∀ (n : ℕ)
      (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding
          H N hN beta hbeta n
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
            H N hN beta hbeta x) =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
          H N hN beta hbeta n x

/-- Construct the completed operator-realization package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedOperatorRealizationPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedOperatorRealizationPackage
      H N hN beta hbeta :=
  { contractiveRealization :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedOperatorEmbedding_opNorm_le_one
        H N hN beta hbeta
    zeroTime :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_zero
        H N hN beta hbeta
    addTime :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_add
        H N hN beta hbeta
    doubledOperatorDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_opNorm_le_exp_of_pos
        H N hN beta hbeta
    denseReceipt :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationCompletedEvolvedOperatorEmbedding_apply_algebraic
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D