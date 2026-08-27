import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct

noncomputable section

/-- At Euclidean time zero the algebraic two-endpoint excitation transfer is
exactly the identity on the full tensor core. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta 0 = LinearMap.id := by
  apply TensorProduct.ext'
  intro f g
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer]

/-- The two-endpoint excitation transfer is a genuine discrete semigroup on
the whole algebraic tensor core, not merely on decomposable tensors. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta (m + n) =
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta m).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta n) := by
  apply TensorProduct.ext'
  intro f g
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer,
    pow_add]

/-- Pointwise form of the algebraic excitation semigroup law. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer_add_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta (m + n) x =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta m
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n x) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer_add]
  rfl

/-- The pair-`L²` realization at time zero is the unevolved algebraic tensor
embedding. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta 0 =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta := by
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding]

/-- Pair-`L²` realization intertwines addition of Euclidean times with the
algebraic tensor semigroup on the whole core. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta (m + n) =
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta m).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta n) := by
  apply LinearMap.ext
  intro x
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding]

/-- Pointwise pair-`L²` intertwining law. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_add_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta (m + n) x =
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta m
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n x) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_add]
  rfl

/-- The actual Wilson-boundary realization at time zero is the unevolved
algebraic tensor core transported through the exact boundary/pair isometry. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta 0 =
      (periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry
        H N).toLinearMap.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEmbedding
        H N hN beta hbeta) := by
  simp [periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding]

/-- The genuine shared Wilson boundary inherits the same discrete excitation
semigroup law through the exact boundary/pair `L²` isometry. -/
theorem periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_add
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta (m + n) =
      (periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta m).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta n) := by
  apply LinearMap.ext
  intro x
  simp [periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding]

/-- Pointwise Wilson-boundary intertwining law. -/
@[simp] theorem periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_add_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m n : ℕ)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorCore
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta (m + n) x =
      periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
        H N hN beta hbeta m
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n x) := by
  rw [periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_add]
  rfl

/-- Audit-visible receipt that the algebraic excitation tensor core carries an
exact discrete transfer semigroup and that both endpoint-pair and genuine
Wilson-boundary realizations intertwine that semigroup. -/
structure PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorSemigroupPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : Prop where
  transferZero :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
        H N hN beta hbeta 0 = LinearMap.id
  transferAdd :
    ∀ m n : ℕ,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta (m + n) =
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta m).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n)
  pairIntertwinesAdd :
    ∀ m n : ℕ,
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta (m + n) =
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta m).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n)
  boundaryIntertwinesAdd :
    ∀ m n : ℕ,
      periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta (m + n) =
        (periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding
          H N hN beta hbeta m).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer
          H N hN beta hbeta n)

/-- Construct the exact algebraic excitation-tensor semigroup package. -/
theorem periodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorSemigroupPackage
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenOSBoundaryExcitationAlgebraicTensorSemigroupPackage
      H N hN beta hbeta :=
  { transferZero :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer_zero
        H N hN beta hbeta
    transferAdd :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorTransfer_add
        H N hN beta hbeta
    pairIntertwinesAdd :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationAlgebraicTensorEvolvedEmbedding_add
        H N hN beta hbeta
    boundaryIntertwinesAdd :=
      periodicHypercubicEvenSpecialUnitaryBoundaryExcitationAlgebraicTensorEvolvedEmbedding_add
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
