import MGAP4D.MathlibAnalytic.ContinuousLinearMapCompletionFunctor
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationNativeCompletionEquiv
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationNativeHilbertTensorTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open Set Function Topology
open scoped TensorProduct InnerProductSpace

noncomputable section

/-- Conjugate a bounded endomorphism by a linear isometry equivalence.  Keeping
this construction generic prevents the dependent physical carrier parameters
from being unfolded while proving the semigroup and norm statements below. -/
noncomputable def continuousLinearMapConjugateLinearIsometryEquiv
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (U : E ≃ₗᵢ[𝕜] F)
    (A : E →L[𝕜] E) :
    F →L[𝕜] F :=
  ((U : E →L[𝕜] F) ∘L A) ∘L (U.symm : F →L[𝕜] E)

/-- Pointwise form of isometric conjugation. -/
@[simp] theorem continuousLinearMapConjugateLinearIsometryEquiv_apply
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (U : E ≃ₗᵢ[𝕜] F)
    (A : E →L[𝕜] E)
    (y : F) :
    continuousLinearMapConjugateLinearIsometryEquiv U A y =
      U (A (U.symm y)) :=
  rfl

/-- On an element already presented through the isometry, conjugation simply
applies the source operator and maps back. -/
@[simp] theorem continuousLinearMapConjugateLinearIsometryEquiv_apply_image
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (U : E ≃ₗᵢ[𝕜] F)
    (A : E →L[𝕜] E)
    (x : E) :
    continuousLinearMapConjugateLinearIsometryEquiv U A (U x) =
      U (A x) := by
  simp [continuousLinearMapConjugateLinearIsometryEquiv]

/-- Isometric conjugation preserves the identity. -/
@[simp] theorem continuousLinearMapConjugateLinearIsometryEquiv_id
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (U : E ≃ₗᵢ[𝕜] F) :
    continuousLinearMapConjugateLinearIsometryEquiv U
        (ContinuousLinearMap.id 𝕜 E) =
      ContinuousLinearMap.id 𝕜 F := by
  apply ContinuousLinearMap.ext
  intro y
  simp [continuousLinearMapConjugateLinearIsometryEquiv]

/-- Isometric conjugation is multiplicative for composition. -/
theorem continuousLinearMapConjugateLinearIsometryEquiv_comp
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (U : E ≃ₗᵢ[𝕜] F)
    (A B : E →L[𝕜] E) :
    continuousLinearMapConjugateLinearIsometryEquiv U (A ∘L B) =
      continuousLinearMapConjugateLinearIsometryEquiv U A ∘L
        continuousLinearMapConjugateLinearIsometryEquiv U B := by
  apply ContinuousLinearMap.ext
  intro y
  simp [continuousLinearMapConjugateLinearIsometryEquiv]

/-- Conjugation by a linear isometry equivalence transports an operator-norm
upper bound without loss. -/
theorem continuousLinearMapConjugateLinearIsometryEquiv_opNorm_le
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (U : E ≃ₗᵢ[𝕜] F)
    (A : E →L[𝕜] E)
    {C : ℝ}
    (hC : 0 ≤ C)
    (hA : ContinuousLinearMap.opNorm A ≤ C) :
    ContinuousLinearMap.opNorm
        (continuousLinearMapConjugateLinearIsometryEquiv U A) ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound hC
  intro y
  rw [continuousLinearMapConjugateLinearIsometryEquiv_apply, U.norm_map]
  calc
    ‖A (U.symm y)‖ ≤ ContinuousLinearMap.opNorm A * ‖U.symm y‖ :=
      A.le_opNorm (U.symm y)
    _ ≤ C * ‖U.symm y‖ :=
      mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = C * ‖y‖ := by rw [U.symm.norm_map]

local instance osBoundaryExcitationCompletedPairSemigroupSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationCompletedPairSemigroupSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationCompletedPairSemigroupSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationCompletedPairSemigroupSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationCompletedPairSemigroupSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationCompletedPairSemigroupSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationCompletedPairSemigroupSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Mathlib's native Hilbert tensor norm on the algebraic physical excitation
carrier whose completion is evolved below. -/
@[reducible] local instance osBoundaryExcitationCompletedPairSemigroupNormedAddCommGroup
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

/-- Expose the additive group inherited from the chosen native tensor norm
explicitly.  Completion asks for this parent structure before it asks for the
normed structure; naming the parent prevents expensive reconstruction through
the dependent physical tensor alias. -/
@[reducible] local instance osBoundaryExcitationCompletedPairSemigroupAddCommGroup
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    AddCommGroup
      (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta) :=
  (osBoundaryExcitationCompletedPairSemigroupNormedAddCommGroup
    H N hN beta hbeta).toAddCommGroup

/-- The matching native tensor inner product. -/
@[reducible] local instance osBoundaryExcitationCompletedPairSemigroupInnerProductSpace
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

/-- The concrete pair-Hilbert sector remains complete because it is a closed
subspace of pair-`L²`. -/
local instance osBoundaryExcitationCompletedPairSemigroupPairHilbertSectorComplete
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector_complete
    H N hN beta hbeta

/-- Extend the already-bounded native algebraic tensor transfer by Mathlib's
canonical `ContinuousLinearMap.completion`.  No new analytic construction is
introduced: this is exactly the completion functor applied to the #2329
continuous tensor transfer. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    UniformSpace.Completion
        (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta) →L[ℝ]
      UniformSpace.Completion
        (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
          H N hN beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
    H N hN beta hbeta n).completion

/-- On the canonical dense algebraic copy, the completed transfer is exactly
the original native tensor transfer. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_apply_coe
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta n
        (x : UniformSpace.Completion
          (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
            H N hN beta hbeta)) =
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n x :
        UniformSpace.Completion
          (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
            H N hN beta hbeta)) := by
  exact ContinuousLinearMap.completion_apply_coe
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
      H N hN beta hbeta n) x

/-- The completed native tensor transfer starts at the identity. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta 0 =
      ContinuousLinearMap.id ℝ
        (UniformSpace.Completion
          (PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
            H N hN beta hbeta)) := by
  change
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
      H N hN beta hbeta 0).completion = _
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_zero]
  exact continuousLinearMap_completion_id

/-- Completion preserves the exact additive-time semigroup law. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta (m + n) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
          H N hN beta hbeta m ∘L
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
          H N hN beta hbeta n := by
  change
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
      H N hN beta hbeta (m + n)).completion =
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta m).completion ∘L
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n).completion
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_add]
  exact continuousLinearMap_completion_comp _ _

/-- The completion functor transports the doubled finite-volume exponential
operator bound without loss.  We prove this directly on Mathlib's canonical
dense copy, so the statement is phrased in the same explicit `opNorm` carrier
as the pre-existing #2329 estimate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_norm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    ContinuousLinearMap.opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta n) ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact (Real.exp_pos _).le
  · intro y
    refine UniformSpace.Completion.induction_on y ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro x
      simpa using
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer_apply_norm_le_exp_of_pos
          H N hN beta hbeta n hn x

/-- Conjugate the completed native tensor semigroup by the canonical isometric
identification `Completion (K ⊗ K) ≃ H_pair` from #2368.  This is the actual
bounded transfer semigroup on the concrete closed pair-Hilbert excitation
sector. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta →L[ℝ]
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
        H N hN beta hbeta :=
  continuousLinearMapConjugateLinearIsometryEquiv
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
      H N hN beta hbeta n)

/-- Pointwise formula for the conjugated pair-Hilbert sector transfer. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (y : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n y =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
          H N hN beta hbeta n
          ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
            H N hN beta hbeta).symm y)) := by
  exact continuousLinearMapConjugateLinearIsometryEquiv_apply _ _ _

/-- The concrete pair-Hilbert transfer starts at the identity. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 0 =
      ContinuousLinearMap.id ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_zero]
  exact continuousLinearMapConjugateLinearIsometryEquiv_id _

/-- The conjugated transfer is an exact discrete semigroup on the entire
completed concrete pair-Hilbert sector. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta (m + n) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta m ∘L
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_add]
  exact continuousLinearMapConjugateLinearIsometryEquiv_comp _ _ _

/-- Conjugation by the canonical linear isometry equivalence does not weaken
the doubled exponential operator bound. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_exp_of_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n) :
    ContinuousLinearMap.opNorm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n) ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
  exact
    continuousLinearMapConjugateLinearIsometryEquiv_opNorm_le
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer
        H N hN beta hbeta n)
      (Real.exp_pos _).le
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_norm_le_exp_of_pos
        H N hN beta hbeta n hn)

/-- The completed concrete transfer exactly extends the pre-existing algebraic
sector-valued excitation transfer on the canonical dense image. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_apply_algebraic
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta n
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta x) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
          H N hN beta hbeta n x) := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector_apply_coe
      H N hN beta hbeta x]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
  rw [continuousLinearMapConjugateLinearIsometryEquiv_apply_image]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionTransfer_apply_coe]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorCompletionEquivPairHilbertSector_apply_coe]

/-- Ambient pair-`L²` form of the dense algebraic compatibility: after
coercion from the completed sector, evolution is exactly the original
endpoint-pair embedding applied to the native algebraic transfer. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_apply_algebraic_pairL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
            H N hN beta hbeta x) :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) =
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n x) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_apply_algebraic]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry_coe
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
        H N hN beta hbeta n x)

/-- Audit-visible package for the completed two-endpoint excitation dynamics. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairSemigroupPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  transferZero :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
        H N hN beta hbeta 0 =
      ContinuousLinearMap.id ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSector
          H N hN beta hbeta)
  transferAdd :
    ∀ m n : ℕ,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta (m + n) =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta m ∘L
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
            H N hN beta hbeta n
  doubledOperatorDecay :
    ∀ n : ℕ, 0 < n →
      ContinuousLinearMap.opNorm
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n) ≤
        Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta)
  denseAlgebraicIntertwining :
    ∀ (n : ℕ)
      (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer
          H N hN beta hbeta n
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
            H N hN beta hbeta x) =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorToPairHilbertSectorNativeLinearIsometry
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationNativeHilbertTensorTransfer
            H N hN beta hbeta n x)

/-- Construct the completed concrete pair-Hilbert semigroup package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationCompletedPairSemigroupPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationCompletedPairSemigroupPackage
      H N hN beta hbeta :=
  ⟨periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_zero
      H N hN beta hbeta,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_add
      H N hN beta hbeta,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_norm_le_exp_of_pos
      H N hN beta hbeta,
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransfer_apply_algebraic
      H N hN beta hbeta⟩

end

end MathlibAnalytic
end MGAP4D
