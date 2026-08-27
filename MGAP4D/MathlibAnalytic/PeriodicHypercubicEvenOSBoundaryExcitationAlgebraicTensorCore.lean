import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationTensorDecay
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct

noncomputable section

universe u v

/-- Bundle the real `L²` external tensor as a linear map in its right factor. -/
noncomputable def realL2ExternalTensorLinearMapRight
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) :
    Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 (μ.prod ν) where
  toFun := fun g => realL2ExternalTensor f g
  map_add' := fun g₁ g₂ => realL2ExternalTensor_add_right f g₁ g₂
  map_smul' := fun c g => realL2ExternalTensor_smul_right c f g

@[simp] theorem realL2ExternalTensorLinearMapRight_apply
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2ExternalTensorLinearMapRight f g = realL2ExternalTensor f g :=
  rfl

/-- The external tensor is bilinear on the two real `L²` factors. -/
noncomputable def realL2ExternalTensorBilinear
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] :
    Lp ℝ 2 μ →ₗ[ℝ] (Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 (μ.prod ν)) where
  toFun := realL2ExternalTensorLinearMapRight
  map_add' := by
    intro f₁ f₂
    ext g
    exact realL2ExternalTensor_add_left f₁ f₂ g
  map_smul' := by
    intro c f
    ext g
    exact realL2ExternalTensor_smul_left c f g

@[simp] theorem realL2ExternalTensorBilinear_apply
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2ExternalTensorBilinear f g = realL2ExternalTensor f g :=
  rfl

/-- Universal algebraic-tensor realization of the real `L²` external tensor. -/
noncomputable def realL2ExternalTensorLift
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] :
    (Lp ℝ 2 μ ⊗[ℝ] Lp ℝ 2 ν) →ₗ[ℝ] Lp ℝ 2 (μ.prod ν) :=
  TensorProduct.lift realL2ExternalTensorBilinear

@[simp] theorem realL2ExternalTensorLift_tmul
    {α : Type u} {β : Type v}
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν]
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2ExternalTensorLift (f ⊗ₜ[ℝ] g) = realL2ExternalTensor f g :=
  rfl

local instance osBoundaryExcitationAlgebraicTensorCoreSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationAlgebraicTensorCoreSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationAlgebraicTensorCoreSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationAlgebraicTensorCoreSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationAlgebraicTensorCoreSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationAlgebraicTensorCoreSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationAlgebraicTensorCoreSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The algebraic tensor product of the two physical one-slice excitation
sectors.  This is the canonical linear core underlying the pure tensors used
in the preceding boundary-decay theorem. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Type :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta ⊗[ℝ]
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta

/-- Forget the invariant-subspace wrappers as an honest linear map into the
one-slice Haar `L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta →ₗ[ℝ]
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) where
  toFun := periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2 H N hN beta hbeta
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
        H N hN beta hbeta f :=
  rfl

/-- Canonical linear realization of the physical algebraic excitation tensor
core inside the ordered two-spatial-endpoint Haar `L²` carrier. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  realL2ExternalTensorLift.comp
    (TensorProduct.map
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2LinearMap
        H N hN beta hbeta))

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta (f ⊗ₜ[ℝ] g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
        H N hN beta hbeta f g := by
  rfl

/-- Exact cross norm on pure tensors in the algebraic excitation core. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta (f ⊗ₜ[ℝ] g)‖ = ‖f‖ * ‖g‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2_norm
    H N hN beta hbeta f g

/-- Apply the concrete one-slice excitation transfer power to both factors of
the algebraic tensor core.  Mathlib's `TensorProduct.map` makes this an exact
linear operation before any Hilbert completion is invoked. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta :=
  TensorProduct.map
    (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n).toLinearMap)
    (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n).toLinearMap)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer_tmul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta n (f ⊗ₜ[ℝ] g) =
      (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f) ⊗ₜ[ℝ]
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) g) := by
  rfl

/-- The linear two-endpoint realization after evolving both excitation factors. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
    H N hN beta hbeta).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta n)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_tmul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n (f ⊗ₜ[ℝ] g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer
        H N hN beta hbeta n f g := by
  rfl

/-- Pull the evolved algebraic tensor core linearly to the actual shared Wilson
boundary using the exact boundary/pair `L²` isometry from PR #2290. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryBoundaryHaarL2 H N :=
  (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
      H N).toLinearMap.comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
      H N hN beta hbeta n)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_tmul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n (f ⊗ₜ[ℝ] g) =
      periodicHypercubicEvenSpecialUnitaryBoundaryExcitationTensorTransfer
        H N hN beta hbeta n f g := by
  rfl

/-- The previously pointwise pure-tensor boundary decay is now the restriction
of a canonical linear map from the algebraic excitation tensor core. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_tmul_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta n (f ⊗ₜ[ℝ] g)‖ ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta (f ⊗ₜ[ℝ] g)‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_tmul]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul_norm]
  exact
    periodicHypercubicEvenSpecialUnitaryBoundaryExcitationTensorTransfer_norm_le_exp
      H N hN beta hbeta n hn f g

/-- Audit-visible receipt that the physical two-endpoint excitation construction
has been linearized on the canonical algebraic tensor product.  No claim of
Hilbert-tensor completion or density is made in this layer. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorCorePackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  realizesPureTensors :
    ∀ f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
          H N hN beta hbeta (f ⊗ₜ[ℝ] g) =
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
          H N hN beta hbeta f g
  transferOnPureTensors :
    ∀ (n : ℕ)
      (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n (f ⊗ₜ[ℝ] g) =
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta) ^ n) f) ⊗ₜ[ℝ]
          (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta) ^ n) g)
  boundaryDecayOnPureTensors :
    ∀ (n : ℕ), 0 < n →
      ∀ f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta n (f ⊗ₜ[ℝ] g)‖ ≤
        Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
            H N hN beta hbeta (f ⊗ₜ[ℝ] g)‖

/-- Construct the algebraic excitation-tensor core package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorCorePackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorCorePackage
      H N hN beta hbeta :=
  { realizesPureTensors :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding_tmul
        H N hN beta hbeta
    transferOnPureTensors :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer_tmul
        H N hN beta hbeta
    boundaryDecayOnPureTensors :=
      periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_tmul_norm_le_exp
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
