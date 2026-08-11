import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceKernelFeature
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct Matrix.Norms.Frobenius

noncomputable section

/-- Recover a complex matrix from the transposed real/imaginary Euclidean
coordinates of its defining real feature. -/
noncomputable def realFeatureComplexMatrixLinearMap
    (N : ℕ) :
    SpecialUnitaryMatrixRealFeatureSpace N →ₗ[ℝ]
      Matrix (Fin N) (Fin N) ℂ where
  toFun := fun v i j =>
    ⟨v ((j, i), true), v ((j, i), false)⟩
  map_add' := by
    intro v w
    ext i j
    apply Complex.ext <;> simp
  map_smul' := by
    intro r v
    ext i j
    apply Complex.ext <;> simp

/-- Realification followed by reconstruction is exactly the original complex
matrix. -/
@[simp] theorem realFeatureComplexMatrixLinearMap_complexMatrixRealFeature
    (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    realFeatureComplexMatrixLinearMap N (complexMatrixRealFeature N A) = A := by
  ext i j
  apply Complex.ext <;>
    simp [realFeatureComplexMatrixLinearMap, complexMatrixRealFeature]

/-- The defining `SU(N)` matrix feature reconstructs to the underlying matrix. -/
@[simp] theorem realFeatureComplexMatrixLinearMap_specialUnitaryMatrixRealFeature
    (N : ℕ)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    realFeatureComplexMatrixLinearMap N (specialUnitaryMatrixRealFeature N U) =
      (U : Matrix (Fin N) (Fin N) ℂ) := by
  simpa [specialUnitaryMatrixRealFeature] using
    realFeatureComplexMatrixLinearMap_complexMatrixRealFeature N
      (U : Matrix (Fin N) (Fin N) ℂ)

/-- Conjugate transpose is real-linear on complex matrices. -/
noncomputable def complexMatrixConjTransposeRealLinearMap
    (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ]
      Matrix (Fin N) (Fin N) ℂ where
  toFun := Matrix.conjTranspose
  map_add' := by
    intro A B
    simp
  map_smul' := by
    intro r A
    simp

/-- A signed edge feature is converted to the matrix used by the canonical
plaquette word: forward edges are unchanged and backward edges use conjugate
transpose. -/
noncomputable def orientedRealFeatureMatrixLinearMap
    (N : ℕ)
    (o : PeriodicHypercubicOrientation) :
    SpecialUnitaryMatrixRealFeatureSpace N →ₗ[ℝ]
      Matrix (Fin N) (Fin N) ℂ :=
  match o with
  | .forward => realFeatureComplexMatrixLinearMap N
  | .backward =>
      complexMatrixConjTransposeRealLinearMap N ∘ₗ
        realFeatureComplexMatrixLinearMap N

/-- On an `SU(N)` defining feature, the signed real-linear map is exactly the
underlying forward matrix or inverse matrix. -/
@[simp] theorem orientedRealFeatureMatrixLinearMap_specialUnitaryMatrixRealFeature
    (N : ℕ)
    (o : PeriodicHypercubicOrientation)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    orientedRealFeatureMatrixLinearMap N o
        (specialUnitaryMatrixRealFeature N U) =
      match o with
      | .forward => (U : Matrix (Fin N) (Fin N) ℂ)
      | .backward => ((U⁻¹ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
          Matrix (Fin N) (Fin N) ℂ) := by
  cases o with
  | forward =>
      exact realFeatureComplexMatrixLinearMap_specialUnitaryMatrixRealFeature N U
  | backward =>
      change Matrix.conjTranspose
          (realFeatureComplexMatrixLinearMap N
            (specialUnitaryMatrixRealFeature N U)) = _
      rw [realFeatureComplexMatrixLinearMap_specialUnitaryMatrixRealFeature]
      have h := congrArg Subtype.val (Matrix.star_eq_inv U)
      simpa only [Matrix.specialUnitaryGroup.coe_star,
        Matrix.star_eq_conjTranspose] using h

/-- Generic bounded four-leg matrix contraction.  The four legs remain in
`Fin 4` order and each leg is first passed through its canonical orientation
map. -/
noncomputable def orientedFourLegMatrixContraction
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    (SpecialUnitaryMatrixRealFeatureSpace N) [×4]→L[ℝ]
      Matrix (Fin N) (Fin N) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4
      (Matrix (Fin N) (Fin N) ℂ)).compContinuousLinearMap
    (fun k =>
      (orientedRealFeatureMatrixLinearMap N (orientation k)).toContinuousLinearMap)

/-- The canonical primary plaquette orientation is read directly from the
existing signed-boundary API. -/
def periodicHypercubicEvenPrimarySpatialPlaquetteOrientation
    (H : ℕ)
    (k : Fin 4) : PeriodicHypercubicOrientation :=
  (periodicHypercubicBoundaryStep
    (PeriodicHypercubicEvenSideLength H)
    (periodicHypercubicEvenPrimarySpatialPlaquette H) k).orientation

@[simp] theorem periodicHypercubicEvenPrimarySpatialPlaquetteOrientation_zero
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H 0 = .forward := rfl

@[simp] theorem periodicHypercubicEvenPrimarySpatialPlaquetteOrientation_one
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H 1 = .forward := rfl

@[simp] theorem periodicHypercubicEvenPrimarySpatialPlaquetteOrientation_two
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H 2 = .backward := rfl

@[simp] theorem periodicHypercubicEvenPrimarySpatialPlaquetteOrientation_three
    (H : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H 3 = .backward := rfl

/-- The actual primary-spatial four-leg bounded contraction. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFourLegMatrixContraction
    (H N : ℕ) :
    (SpecialUnitaryMatrixRealFeatureSpace N) [×4]→L[ℝ]
      Matrix (Fin N) (Fin N) ℂ :=
  orientedFourLegMatrixContraction N
    (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)

/-- On four `SU(N)` edge features, the bounded contraction is exactly the
canonical naturally oriented plaquette word already used by the Wilson
holonomy API. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourLegMatrixContraction_apply
    (H N : ℕ)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourLegMatrixContraction H N
        (fun k => specialUnitaryMatrixRealFeature N (x k)) =
      ((orientedFourEdgePlaquetteWord x :
          Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) := by
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteFourLegMatrixContraction,
    orientedFourLegMatrixContraction,
    periodicHypercubicEvenPrimarySpatialPlaquetteOrientation,
    orientedFourEdgePlaquetteWord,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, mul_assoc]

/-- Pair two realified edge features and multiply their orientation-correct
matrix representatives. -/
noncomputable def orientedFeaturePairTensorMatrixLinearMap
    (N : ℕ)
    (o₀ o₁ : PeriodicHypercubicOrientation) :
    (SpecialUnitaryMatrixRealFeatureSpace N ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N) →ₗ[ℝ]
      Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.mul' ℝ (Matrix (Fin N) (Fin N) ℂ) ∘ₗ
    TensorProduct.map
      (orientedRealFeatureMatrixLinearMap N o₀)
      (orientedRealFeatureMatrixLinearMap N o₁)

@[simp] theorem orientedFeaturePairTensorMatrixLinearMap_tmul
    (N : ℕ)
    (o₀ o₁ : PeriodicHypercubicOrientation)
    (v₀ v₁ : SpecialUnitaryMatrixRealFeatureSpace N) :
    orientedFeaturePairTensorMatrixLinearMap N o₀ o₁ (v₀ ⊗ₜ[ℝ] v₁) =
      orientedRealFeatureMatrixLinearMap N o₀ v₀ *
        orientedRealFeatureMatrixLinearMap N o₁ v₁ := by
  simp [orientedFeaturePairTensorMatrixLinearMap]

/-- Algebraic four-edge tensor carrier, grouped as `(0,1) ⊗ (2,3)`.  The
inner-product tensor norm is supplied by Mathlib. -/
abbrev SpecialUnitaryFourLegRealFeatureTensorSpace (N : ℕ) :=
  (SpecialUnitaryMatrixRealFeatureSpace N ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N) ⊗[ℝ]
    (SpecialUnitaryMatrixRealFeatureSpace N ⊗[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N)

/-- Canonical pure four-edge tensor in physical edge order. -/
def specialUnitaryFourLegRealFeatureTensor
    (N : ℕ)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    SpecialUnitaryFourLegRealFeatureTensorSpace N :=
  (v 0 ⊗ₜ[ℝ] v 1) ⊗ₜ[ℝ] (v 2 ⊗ₜ[ℝ] v 3)

/-- Linearization of the natural four-edge product on the algebraic four-fold
tensor carrier. -/
noncomputable def orientedFourLegTensorMatrixLinearMap
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    SpecialUnitaryFourLegRealFeatureTensorSpace N →ₗ[ℝ]
      Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.mul' ℝ (Matrix (Fin N) (Fin N) ℂ) ∘ₗ
    TensorProduct.map
      (orientedFeaturePairTensorMatrixLinearMap N (orientation 0) (orientation 1))
      (orientedFeaturePairTensorMatrixLinearMap N (orientation 2) (orientation 3))

@[simp] theorem orientedFourLegTensorMatrixLinearMap_pure
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    orientedFourLegTensorMatrixLinearMap N orientation
        (specialUnitaryFourLegRealFeatureTensor N v) =
      (orientedRealFeatureMatrixLinearMap N (orientation 0) (v 0) *
        orientedRealFeatureMatrixLinearMap N (orientation 1) (v 1)) *
      (orientedRealFeatureMatrixLinearMap N (orientation 2) (v 2) *
        orientedRealFeatureMatrixLinearMap N (orientation 3) (v 3)) := by
  simp [orientedFourLegTensorMatrixLinearMap,
    specialUnitaryFourLegRealFeatureTensor]

/-- Cyclic linearization on the same four-fold tensor carrier.  The pair
`(2,3)` is multiplied before `(0,1)`, producing the existing cyclic Haar word. -/
noncomputable def cyclicFourLegTensorMatrixLinearMap
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    SpecialUnitaryFourLegRealFeatureTensorSpace N →ₗ[ℝ]
      Matrix (Fin N) (Fin N) ℂ :=
  TensorProduct.lift
      (LinearMap.mul ℝ (Matrix (Fin N) (Fin N) ℂ)).flip ∘ₗ
    TensorProduct.map
      (orientedFeaturePairTensorMatrixLinearMap N (orientation 0) (orientation 1))
      (orientedFeaturePairTensorMatrixLinearMap N (orientation 2) (orientation 3))

@[simp] theorem cyclicFourLegTensorMatrixLinearMap_pure
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    cyclicFourLegTensorMatrixLinearMap N orientation
        (specialUnitaryFourLegRealFeatureTensor N v) =
      (orientedRealFeatureMatrixLinearMap N (orientation 2) (v 2) *
        orientedRealFeatureMatrixLinearMap N (orientation 3) (v 3)) *
      (orientedRealFeatureMatrixLinearMap N (orientation 0) (v 0) *
        orientedRealFeatureMatrixLinearMap N (orientation 1) (v 1)) := by
  simp [cyclicFourLegTensorMatrixLinearMap,
    specialUnitaryFourLegRealFeatureTensor]

/-- Hilbert completion of the algebraic four-edge real-feature tensor carrier. -/
abbrev SpecialUnitaryCompletedFourLegRealFeatureTensorSpace (N : ℕ) :=
  UniformSpace.Completion (SpecialUnitaryFourLegRealFeatureTensorSpace N)

/-- Extend the cyclic algebraic tensor contraction continuously to the completed
four-edge carrier.  Frobenius norm is used only to bundle the finite-dimensional
matrix target as a normed algebra; the underlying matrix identity is norm
independent. -/
noncomputable def cyclicCompletedFourLegTensorMatrixContraction
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N →L[ℝ]
      Matrix (Fin N) (Fin N) ℂ :=
  (cyclicFourLegTensorMatrixLinearMap N orientation).toContinuousLinearMap.extend
    UniformSpace.Completion.toComplL

/-- The completed contraction agrees exactly with the algebraic contraction on
the dense algebraic tensor carrier. -/
theorem cyclicCompletedFourLegTensorMatrixContraction_coe
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation)
    (t : SpecialUnitaryFourLegRealFeatureTensorSpace N) :
    cyclicCompletedFourLegTensorMatrixContraction N orientation
        (t : SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N) =
      cyclicFourLegTensorMatrixLinearMap N orientation t := by
  exact ContinuousLinearMap.extend_eq
    (cyclicFourLegTensorMatrixLinearMap N orientation).toContinuousLinearMap
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        (UniformSpace.Completion.denseRange_coe :
          DenseRange fun x : SpecialUnitaryFourLegRealFeatureTensorSpace N =>
            (x : SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N)))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        UniformSpace.Completion.isUniformInducing_coe
          (SpecialUnitaryFourLegRealFeatureTensorSpace N))
    t

/-- For the actual primary-spatial orientation, the completed cyclic
contraction of the four defining edge features is exactly the matrix underlying
the existing cyclic Haar plaquette word. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquette_completedCyclicContraction_apply
    (H N : ℕ)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    cyclicCompletedFourLegTensorMatrixContraction N
        (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)
        ((specialUnitaryFourLegRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N (x k)) :
            SpecialUnitaryFourLegRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N) =
      ((haarFinFourCyclicPlaquetteWord x :
          Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) := by
  rw [cyclicCompletedFourLegTensorMatrixContraction_coe]
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteOrientation,
    haarFinFourCyclicPlaquetteWord_eq, mul_assoc]

/-- Specializing the four inputs to the actual fixed boundary edge coordinates
reconstructs the exact primary spatial boundary cyclic holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquette_completedCyclicContraction_boundary
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    cyclicCompletedFourLegTensorMatrixContraction N
        (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)
        ((specialUnitaryFourLegRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            (b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))) :
            SpecialUnitaryFourLegRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N) =
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H N b :
        Matrix (Fin N) (Fin N) ℂ) := by
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy] using
    periodicHypercubicEvenPrimarySpatialPlaquette_completedCyclicContraction_apply
      H N
      (fun k => b
        (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))

/-- The same completed contraction can be written directly using the four
boundary legs of the canonical temporal companions. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquette_completedCyclicContraction_temporalCompanionBoundaryLegs
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    cyclicCompletedFourLegTensorMatrixContraction N
        (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)
        ((specialUnitaryFourLegRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :
            SpecialUnitaryFourLegRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N) =
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H N b :
        Matrix (Fin N) (Fin N) ℂ) := by
  simp_rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_fiberedBoundaryLeg_eq]
  exact periodicHypercubicEvenPrimarySpatialPlaquette_completedCyclicContraction_boundary
    H N b

/-- Apply the identical completed tensor/contraction architecture to the four
positive-half open paths supplied by the temporal companions. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicMatrixFeature
    (H N : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    Matrix (Fin N) (Fin N) ℂ :=
  cyclicCompletedFourLegTensorMatrixContraction N
    (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)
    ((specialUnitaryFourLegRealFeatureTensor N
      (fun k => specialUnitaryMatrixRealFeature N
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :
        SpecialUnitaryFourLegRealFeatureTensorSpace N) :
      SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N)

/-- Explicit pure-tensor formula for the four temporal-companion open-half
contraction. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicMatrixFeature_eq
    (H N : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicMatrixFeature
        H N x =
      let u : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ := fun k =>
        periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k)
      ((haarFinFourCyclicPlaquetteWord u :
          Matrix.specialUnitaryGroup (Fin N) ℂ) :
        Matrix (Fin N) (Fin N) ℂ) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCyclicMatrixFeature
  simpa using
    periodicHypercubicEvenPrimarySpatialPlaquette_completedCyclicContraction_apply
      H N
      (fun k =>
        periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))

/-- Applying realification after the boundary contraction gives exactly the
defining real matrix feature of the primary cyclic holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquette_completedCyclicContraction_boundary_realFeature
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    complexMatrixRealFeature N
        (cyclicCompletedFourLegTensorMatrixContraction N
          (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)
          ((specialUnitaryFourLegRealFeatureTensor N
            (fun k => specialUnitaryMatrixRealFeature N
              (b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))) :
              SpecialUnitaryFourLegRealFeatureTensorSpace N) :
            SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N)) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H N b) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquette_completedCyclicContraction_boundary]
  rfl

end

end MathlibAnalytic
end MGAP4D
