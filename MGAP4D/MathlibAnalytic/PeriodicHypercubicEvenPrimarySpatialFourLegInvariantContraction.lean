import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceKernelFeature
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct

noncomputable section

/-- Recover a complex matrix from the transposed real/imaginary Euclidean
coordinates of its defining real feature.  This map is deliberately kept
algebraic: no arbitrary matrix norm is introduced into the continuous layer. -/
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

/-- Realification is a real-linear map from complex matrices into the canonical
Euclidean defining-feature space. -/
noncomputable def complexMatrixRealFeatureLinearMap
    (N : ℕ) :
    Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N where
  toFun := complexMatrixRealFeature N
  map_add' := by
    intro A B
    ext q
    rcases q with ⟨⟨i, j⟩, h⟩
    cases h <;> simp [complexMatrixRealFeature]
  map_smul' := by
    intro r A
    ext q
    rcases q with ⟨⟨i, j⟩, h⟩
    cases h <;> simp [complexMatrixRealFeature]

/-- Realification followed by reconstruction is exactly the original complex
matrix. -/
@[simp] theorem realFeatureComplexMatrixLinearMap_complexMatrixRealFeature
    (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    realFeatureComplexMatrixLinearMap N (complexMatrixRealFeature N A) = A := by
  ext i j
  apply Complex.ext <;>
    simp [realFeatureComplexMatrixLinearMap, complexMatrixRealFeature]

/-- Reconstruction followed by realification is exactly the original real
matrix feature. -/
@[simp] theorem complexMatrixRealFeatureLinearMap_realFeatureComplexMatrixLinearMap
    (N : ℕ)
    (v : SpecialUnitaryMatrixRealFeatureSpace N) :
    complexMatrixRealFeatureLinearMap N
        (realFeatureComplexMatrixLinearMap N v) = v := by
  ext q
  rcases q with ⟨⟨i, j⟩, h⟩
  cases h <;>
    simp [complexMatrixRealFeatureLinearMap, complexMatrixRealFeature,
      realFeatureComplexMatrixLinearMap]

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

/-- Orientation on a degree-one real matrix feature.  Forward edges are the
identity; backward edges are reconstructed algebraically, conjugate-transposed,
and realified again. -/
noncomputable def orientedRealFeatureLinearMap
    (N : ℕ)
    (o : PeriodicHypercubicOrientation) :
    SpecialUnitaryMatrixRealFeatureSpace N →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  match o with
  | .forward => LinearMap.id
  | .backward =>
      complexMatrixRealFeatureLinearMap N ∘ₗ
        complexMatrixConjTransposeRealLinearMap N ∘ₗ
          realFeatureComplexMatrixLinearMap N

/-- On an `SU(N)` defining feature, the orientation map is exactly the feature
of the forward or inverse group element. -/
@[simp] theorem orientedRealFeatureLinearMap_specialUnitaryMatrixRealFeature
    (N : ℕ)
    (o : PeriodicHypercubicOrientation)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    orientedRealFeatureLinearMap N o
        (specialUnitaryMatrixRealFeature N U) =
      match o with
      | .forward => specialUnitaryMatrixRealFeature N U
      | .backward => specialUnitaryMatrixRealFeature N U⁻¹ := by
  cases o with
  | forward => rfl
  | backward =>
      change complexMatrixRealFeature N
          (Matrix.conjTranspose
            (realFeatureComplexMatrixLinearMap N
              (specialUnitaryMatrixRealFeature N U))) = _
      rw [realFeatureComplexMatrixLinearMap_specialUnitaryMatrixRealFeature]
      have h := congrArg Subtype.val (Matrix.star_eq_inv U)
      simpa [specialUnitaryMatrixRealFeature,
        Matrix.specialUnitaryGroup.coe_star,
        Matrix.star_eq_conjTranspose] using
        congrArg (complexMatrixRealFeature N) h

/-- Matrix multiplication transported algebraically to the canonical Euclidean
real matrix-feature space. -/
noncomputable def realFeatureMatrixMulLinearMap
    (N : ℕ) :
    SpecialUnitaryMatrixRealFeatureSpace N →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N →ₗ[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace N :=
  ((LinearMap.mul ℝ (Matrix (Fin N) (Fin N) ℂ)).compl₁₂
      (realFeatureComplexMatrixLinearMap N)
      (realFeatureComplexMatrixLinearMap N)).compr₂
    (complexMatrixRealFeatureLinearMap N)

@[simp] theorem realFeatureMatrixMulLinearMap_apply
    (N : ℕ)
    (v w : SpecialUnitaryMatrixRealFeatureSpace N) :
    realFeatureMatrixMulLinearMap N v w =
      complexMatrixRealFeature N
        (realFeatureComplexMatrixLinearMap N v *
          realFeatureComplexMatrixLinearMap N w) := by
  rfl

/-- Every such bilinear multiplication map is bounded because both input
feature spaces are finite-dimensional Euclidean spaces.  This is the generic
continuous algebraic kernel from which the four-leg contraction is built. -/
noncomputable def realFeatureMatrixMulContinuousBilinearMap
    (N : ℕ) :
    SpecialUnitaryMatrixRealFeatureSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N →L[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace N :=
  (realFeatureMatrixMulLinearMap N).toContinuousBilinearMap

@[simp] theorem realFeatureMatrixMulContinuousBilinearMap_apply
    (N : ℕ)
    (v w : SpecialUnitaryMatrixRealFeatureSpace N) :
    realFeatureMatrixMulContinuousBilinearMap N v w =
      realFeatureMatrixMulLinearMap N v w := by
  rfl

/-- Orientation-correct bilinear multiplication of two degree-one edge
features, still entirely in the canonical Euclidean feature space. -/
noncomputable def orientedRealFeatureMatrixMulLinearMap
    (N : ℕ)
    (o₀ o₁ : PeriodicHypercubicOrientation) :
    SpecialUnitaryMatrixRealFeatureSpace N →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N →ₗ[ℝ]
        SpecialUnitaryMatrixRealFeatureSpace N :=
  (realFeatureMatrixMulLinearMap N).compl₁₂
    (orientedRealFeatureLinearMap N o₀)
    (orientedRealFeatureLinearMap N o₁)

@[simp] theorem orientedRealFeatureMatrixMulLinearMap_specialUnitaryMatrixRealFeature
    (N : ℕ)
    (o₀ o₁ : PeriodicHypercubicOrientation)
    (U V : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    orientedRealFeatureMatrixMulLinearMap N o₀ o₁
        (specialUnitaryMatrixRealFeature N U)
        (specialUnitaryMatrixRealFeature N V) =
      realFeatureMatrixMulLinearMap N
        (orientedRealFeatureLinearMap N o₀
          (specialUnitaryMatrixRealFeature N U))
        (orientedRealFeatureLinearMap N o₁
          (specialUnitaryMatrixRealFeature N V)) := by
  rfl

/-- Algebraic pair tensor carrier for two degree-one real matrix features. -/
abbrev SpecialUnitaryPairRealFeatureTensorSpace (N : ℕ) :=
  SpecialUnitaryMatrixRealFeatureSpace N ⊗[ℝ]
    SpecialUnitaryMatrixRealFeatureSpace N

/-- Orientation-correct multiplication linearized on a two-edge tensor. -/
noncomputable def orientedPairTensorRealFeatureLinearMap
    (N : ℕ)
    (o₀ o₁ : PeriodicHypercubicOrientation) :
    SpecialUnitaryPairRealFeatureTensorSpace N →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  TensorProduct.lift (orientedRealFeatureMatrixMulLinearMap N o₀ o₁)

@[simp] theorem orientedPairTensorRealFeatureLinearMap_tmul
    (N : ℕ)
    (o₀ o₁ : PeriodicHypercubicOrientation)
    (v w : SpecialUnitaryMatrixRealFeatureSpace N) :
    orientedPairTensorRealFeatureLinearMap N o₀ o₁ (v ⊗ₜ[ℝ] w) =
      orientedRealFeatureMatrixMulLinearMap N o₀ o₁ v w := by
  rfl

/-- The pair-tensor contraction is bounded: its source is the canonical
finite-dimensional Hilbert tensor product and its target is Euclidean. -/
noncomputable def orientedPairTensorRealFeatureContraction
    (N : ℕ)
    (o₀ o₁ : PeriodicHypercubicOrientation) :
    SpecialUnitaryPairRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  (orientedPairTensorRealFeatureLinearMap N o₀ o₁).toContinuousLinearMap

/-- Algebraic four-fold tensor carrier, grouped canonically as `(0,1) ⊗ (2,3)`. -/
abbrev SpecialUnitaryFourLegRealFeatureTensorSpace (N : ℕ) :=
  SpecialUnitaryPairRealFeatureTensorSpace N ⊗[ℝ]
    SpecialUnitaryPairRealFeatureTensorSpace N

/-- Canonical pure four-edge tensor in physical `Fin 4` edge order. -/
def specialUnitaryFourLegRealFeatureTensor
    (N : ℕ)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    SpecialUnitaryFourLegRealFeatureTensorSpace N :=
  (v 0 ⊗ₜ[ℝ] v 1) ⊗ₜ[ℝ] (v 2 ⊗ₜ[ℝ] v 3)

/-- Generic orientation-correct four-leg contraction on the algebraic four-fold
tensor carrier.  It first contracts `(0,1)` and `(2,3)`, then multiplies the
two resulting realified matrix features. -/
noncomputable def orientedFourLegTensorRealFeatureLinearMap
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    SpecialUnitaryFourLegRealFeatureTensorSpace N →ₗ[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  TensorProduct.lift
    ((realFeatureMatrixMulLinearMap N).compl₁₂
      (orientedPairTensorRealFeatureLinearMap N
        (orientation 0) (orientation 1))
      (orientedPairTensorRealFeatureLinearMap N
        (orientation 2) (orientation 3)))

@[simp] theorem orientedFourLegTensorRealFeatureLinearMap_pure
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    orientedFourLegTensorRealFeatureLinearMap N orientation
        (specialUnitaryFourLegRealFeatureTensor N v) =
      realFeatureMatrixMulLinearMap N
        (orientedRealFeatureMatrixMulLinearMap N
          (orientation 0) (orientation 1) (v 0) (v 1))
        (orientedRealFeatureMatrixMulLinearMap N
          (orientation 2) (orientation 3) (v 2) (v 3)) := by
  rfl

/-- Bounded linearization of the generic four-leg invariant contraction. -/
noncomputable def orientedFourLegTensorRealFeatureContraction
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    SpecialUnitaryFourLegRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  (orientedFourLegTensorRealFeatureLinearMap N orientation).toContinuousLinearMap

/-- The canonical primary plaquette orientation is read directly from the
existing signed-boundary API; no second orientation convention is introduced. -/
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

/-- The actual primary-spatial four-leg tensor contraction. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction
    (H N : ℕ) :
    SpecialUnitaryFourLegRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  orientedFourLegTensorRealFeatureContraction N
    (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)

/-- On four `SU(N)` degree-one edge features, the contraction is exactly the
defining real feature of the existing naturally oriented plaquette word. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction_apply
    (H N : ℕ)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction H N
        (specialUnitaryFourLegRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N (x k))) =
      specialUnitaryMatrixRealFeature N (orientedFourEdgePlaquetteWord x) := by
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction,
    orientedFourLegTensorRealFeatureContraction,
    orientedFourLegTensorRealFeatureLinearMap_pure,
    orientedRealFeatureMatrixMulLinearMap,
    realFeatureMatrixMulLinearMap,
    periodicHypercubicEvenPrimarySpatialPlaquetteOrientation,
    orientedFourEdgePlaquetteWord,
    specialUnitaryMatrixRealFeature,
    mul_assoc]

/-- Hilbert completion of the algebraic four-edge tensor carrier. -/
abbrev SpecialUnitaryCompletedFourLegRealFeatureTensorSpace (N : ℕ) :=
  UniformSpace.Completion (SpecialUnitaryFourLegRealFeatureTensorSpace N)

/-- Extend the bounded four-leg contraction to the completed four-edge tensor
carrier. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction
    (H N : ℕ) :
    SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction H N).extend
    (UniformSpace.Completion.toComplL :
      SpecialUnitaryFourLegRealFeatureTensorSpace N →L[ℝ]
        SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N)

/-- The completed contraction restricts exactly to the algebraic tensor carrier. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction_coe
    (H N : ℕ)
    (t : SpecialUnitaryFourLegRealFeatureTensorSpace N) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction H N
        (t : SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N) =
      periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction H N t := by
  exact ContinuousLinearMap.extend_eq
    (periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction H N)
    (e := (UniformSpace.Completion.toComplL :
      SpecialUnitaryFourLegRealFeatureTensorSpace N →L[ℝ]
        SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N))
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

/-- The completed four-leg contraction on actual boundary-restricted physical
edge variables is exactly the defining feature of the canonical primary
spatial plaquette holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction_boundaryRestriction
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction H N
        ((specialUnitaryFourLegRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A
              (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))) :
            SpecialUnitaryFourLegRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction_coe]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction_apply]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteHolonomy_eq_orientedFourEdge]
  simp_rw [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryRestriction_apply]

/-- Fibered-coordinate version: the completed contraction depends only on `b`
and reconstructs the primary spatial plaquette feature of every assembly
`boundaryFiberedAssemble b x y`. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction_boundaryFibered
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction H N
        ((specialUnitaryFourLegRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            (b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))) :
            SpecialUnitaryFourLegRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) := by
  simpa using
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction_boundaryRestriction
      H N
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)

/-- Replacing the four explicit boundary coordinates by the four canonical
temporal-companion boundary legs leaves the exact completed primary-plaquette
feature unchanged. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction_temporalCompanionBoundaryLegs
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction H N
        ((specialUnitaryFourLegRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :
            SpecialUnitaryFourLegRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) := by
  simp_rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_fiberedBoundaryLeg_eq]
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction_boundaryFibered
      H N b x y

/-- Apply the identical completed tensor architecture to the four positive-half
open paths supplied by the canonical temporal companions. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCompletedRealFeature
    (H N : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    SpecialUnitaryMatrixRealFeatureSpace N :=
  periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction H N
    ((specialUnitaryFourLegRealFeatureTensor N
      (fun k => specialUnitaryMatrixRealFeature N
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :
        SpecialUnitaryFourLegRealFeatureTensorSpace N) :
      SpecialUnitaryCompletedFourLegRealFeatureTensorSpace N)

/-- Explicit pure-tensor formula for the four temporal-companion open-half
feature: it is the same canonical orientation-correct four-edge word. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCompletedRealFeature_eq
    (H N : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCompletedRealFeature
        H N x =
      specialUnitaryMatrixRealFeature N
        (orientedFourEdgePlaquetteWord
          (fun k =>
            periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCompletedRealFeature
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteCompletedFourLegRealFeatureContraction_coe]
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction_apply
      H N
      (fun k =>
        periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))

end

end MathlibAnalytic
end MGAP4D
