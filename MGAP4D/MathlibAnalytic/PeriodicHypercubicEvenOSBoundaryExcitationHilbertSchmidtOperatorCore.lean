import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorSemigroup
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperatorLinear
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped TensorProduct InnerProductSpace

noncomputable section

local instance osBoundaryExcitationHilbertSchmidtOperatorCoreSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance osBoundaryExcitationHilbertSchmidtOperatorCoreSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance osBoundaryExcitationHilbertSchmidtOperatorCoreSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance osBoundaryExcitationHilbertSchmidtOperatorCoreSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance osBoundaryExcitationHilbertSchmidtOperatorCoreSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance osBoundaryExcitationHilbertSchmidtOperatorCoreSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance osBoundaryExcitationHilbertSchmidtOperatorCoreSpatialSliceHaarSFinite
    (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The one-slice real Haar `L²` carrier, written locally to keep the operator
statements readable. -/
abbrev PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2
    (H N : ℕ) : Type :=
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

/-- Send the physical algebraic excitation tensor core to bounded operators on
the one-slice Haar `L²` space by first realizing it as the exact endpoint-pair
kernel and then applying the Fréchet--Riesz Hilbert--Schmidt construction. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗ[ℝ]
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N) :=
  (realL2HilbertSchmidtRectangularKernelOperatorContinuousLinearMap
      (μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
      (ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)).toLinearMap.comp
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
      H N hN beta hbeta)

/-- On a pure excitation tensor, the operator-core realization is exactly the
Hilbert--Schmidt operator of the corresponding endpoint-pair kernel. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding_tmul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
        H N hN beta hbeta (f ⊗ₜ[ℝ] g) =
      realL2HilbertSchmidtRectangularKernelOperator
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
          H N hN beta hbeta f g) := by
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding]

/-- Exact rank-one action of a pure physical excitation tensor. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding_tmul_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta)
    (h : PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
        H N hN beta hbeta (f ⊗ₜ[ℝ] g) h =
      (inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
          H N hN beta hbeta f) h) •
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
          H N hN beta hbeta g := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding_tmul]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
  exact
    realL2HilbertSchmidtRectangularKernelOperator_externalTensor_apply
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
        H N hN beta hbeta f)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
        H N hN beta hbeta g)
      h

/-- The pure-tensor operator norm is exactly the Hilbert cross norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding_tmul_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
        H N hN beta hbeta (f ⊗ₜ[ℝ] g)‖ = ‖f‖ * ‖g‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding_tmul]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
  simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2_norm] using
    (realL2HilbertSchmidtRectangularKernelOperator_externalTensor_norm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
        H N hN beta hbeta f)
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
        H N hN beta hbeta g))

/-- Evolve the whole algebraic excitation core and then realize it as a bounded
one-slice Hilbert--Schmidt operator. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
        H N hN beta hbeta →ₗ[ℝ]
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
    H N hN beta hbeta).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta n)

@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
        H N hN beta hbeta 0 =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
        H N hN beta hbeta := by
  apply LinearMap.ext
  intro x
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding]

/-- The operator realization inherits the exact whole-core discrete semigroup
intertwining law proved on the algebraic excitation tensor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
        H N hN beta hbeta (m + n) =
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
        H N hN beta hbeta m).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta n) := by
  apply LinearMap.ext
  intro x
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding]

/-- Pure tensors remain exact rank-one Hilbert--Schmidt operators after the
physical excitation transfer. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_tmul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
        H N hN beta hbeta n (f ⊗ₜ[ℝ] g) =
      realL2HilbertSchmidtRectangularKernelOperator
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer
          H N hN beta hbeta n f g) := by
  rw [show
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
        H N hN beta hbeta n (f ⊗ₜ[ℝ] g) =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n (f ⊗ₜ[ℝ] g)) by rfl]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer_tmul]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding_tmul]
  rfl

/-- Exact operator norm of an evolved pure excitation tensor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_tmul_norm
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
        H N hN beta hbeta n (f ⊗ₜ[ℝ] g)‖ =
      ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f‖ *
        ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) g‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_tmul]
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorTransfer
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairTensorL2
  simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2_norm] using
    (realL2HilbertSchmidtRectangularKernelOperator_externalTensor_norm
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
        H N hN beta hbeta
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f))
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
        H N hN beta hbeta
        (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) g)))

/-- The doubled finite-volume excitation decay is now an operator-norm decay
for exact rank-one realizations of the physical tensor core. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_tmul_norm_le_exp
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (hn : 0 < n)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
        H N hN beta hbeta n (f ⊗ₜ[ℝ] g)‖ ≤
      Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
          H N hN beta hbeta (f ⊗ₜ[ℝ] g)‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding_tmul_norm]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_tmul_norm]
  let r : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  let a : ℝ := -(n : ℝ) * r
  have hf :
      ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f‖ ≤ Real.exp a * ‖f‖ := by
    simpa [a, r] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_exp_of_pos
        H N hN beta hbeta n hn f
  have hg :
      ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) g‖ ≤ Real.exp a * ‖g‖ := by
    simpa [a, r] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_exp_of_pos
        H N hN beta hbeta n hn g
  have hnonnegf : 0 ≤ Real.exp a * ‖f‖ :=
    mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)
  have hmul := mul_le_mul hf hg (norm_nonneg _) hnonnegf
  calc
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f‖ *
        ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) g‖ ≤
      (Real.exp a * ‖f‖) * (Real.exp a * ‖g‖) := hmul
    _ = Real.exp
        (-2 * (n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * (‖f‖ * ‖g‖) := by
      rw [show Real.exp a * ‖f‖ * (Real.exp a * ‖g‖) =
        (Real.exp a * Real.exp a) * (‖f‖ * ‖g‖) by ring]
      rw [← Real.exp_add]
      congr 2
      dsimp [a, r]
      ring

/-- Audit-visible receipt identifying the physical excitation algebraic tensor
with an exact rank-one Hilbert--Schmidt operator core and transporting its
transfer semigroup and finite-volume decay to operator norm. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationHilbertSchmidtOperatorCorePackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  rankOneFormula :
    ∀ (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta)
      (h : PeriodicHypercubicEvenSpecialUnitarySpatialSliceRealL2 H N),
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
          H N hN beta hbeta (f ⊗ₜ[ℝ] g) h =
        (inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
            H N hN beta hbeta f) h) •
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationL2
            H N hN beta hbeta g
  pureTensorNorm :
    ∀ f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
          H N hN beta hbeta (f ⊗ₜ[ℝ] g)‖ = ‖f‖ * ‖g‖
  semigroupIntertwining :
    ∀ m n : ℕ,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
          H N hN beta hbeta (m + n) =
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
          H N hN beta hbeta m).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n)
  pureTensorOperatorDecay :
    ∀ (n : ℕ), 0 < n →
      ∀ f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding
          H N hN beta hbeta n (f ⊗ₜ[ℝ] g)‖ ≤
        Real.exp
          (-2 * (n : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
              H N hN beta hbeta) *
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding
            H N hN beta hbeta (f ⊗ₜ[ℝ] g)‖

/-- Construct the physical Hilbert--Schmidt operator-core package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationHilbertSchmidtOperatorCorePackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationHilbertSchmidtOperatorCorePackage
      H N hN beta hbeta :=
  { rankOneFormula :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding_tmul_apply
        H N hN beta hbeta
    pureTensorNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorOperatorEmbedding_tmul_norm
        H N hN beta hbeta
    semigroupIntertwining :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_add
        H N hN beta hbeta
    pureTensorOperatorDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedOperatorEmbedding_tmul_norm_le_exp
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
