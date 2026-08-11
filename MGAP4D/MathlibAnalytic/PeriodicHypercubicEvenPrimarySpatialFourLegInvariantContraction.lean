import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceKernelFeature
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct

noncomputable section

/-- We use the Frobenius norm only as a local topological presentation of the
finite-dimensional complex matrix algebra.  The resulting algebraic matrix word
and its realified feature are independent of this choice of equivalent norm. -/
local instance matrixFrobeniusNormedRing (N : ℕ) :
    NormedRing (Matrix (Fin N) (Fin N) ℂ) :=
  Matrix.frobeniusNormedRing

local instance matrixFrobeniusNormedSpaceReal (N : ℕ) :
    NormedSpace ℝ (Matrix (Fin N) (Fin N) ℂ) :=
  Matrix.frobeniusNormedSpace

local instance matrixFrobeniusNormedAlgebraReal (N : ℕ) :
    NormedAlgebra ℝ (Matrix (Fin N) (Fin N) ℂ) :=
  Matrix.frobeniusNormedAlgebra

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

/-- Realification is itself a real-linear map. -/
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

/-- Generic bounded four-leg matrix contraction.  The input order is exactly
`Fin 4` order; each leg first passes through its supplied orientation map and
the four resulting matrices are multiplied in that order. -/
noncomputable def orientedFourLegMatrixContraction
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    (SpecialUnitaryMatrixRealFeatureSpace N) [×4]→L[ℝ]
      Matrix (Fin N) (Fin N) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 4
      (Matrix (Fin N) (Fin N) ℂ)).compContinuousLinearMap
    (fun k =>
      (orientedRealFeatureMatrixLinearMap N (orientation k)).toContinuousLinearMap)

/-- The same bounded four-leg contraction, now returned in the canonical real
Euclidean degree-one matrix feature space. -/
noncomputable def orientedFourLegRealFeatureContraction
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    (SpecialUnitaryMatrixRealFeatureSpace N) [×4]→L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  (complexMatrixRealFeatureLinearMap N).toContinuousLinearMap.compContinuousMultilinearMap
    (orientedFourLegMatrixContraction N orientation)

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

/-- The actual primary-spatial bounded four-leg feature contraction. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction
    (H N : ℕ) :
    (SpecialUnitaryMatrixRealFeatureSpace N) [×4]→L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  orientedFourLegRealFeatureContraction N
    (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)

/-- On four defining `SU(N)` edge features, the bounded contraction is exactly
the defining real feature of the existing naturally oriented plaquette word. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction_apply
    (H N : ℕ)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction H N
        (fun k => specialUnitaryMatrixRealFeature N (x k)) =
      specialUnitaryMatrixRealFeature N (orientedFourEdgePlaquetteWord x) := by
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction,
    orientedFourLegRealFeatureContraction,
    orientedFourLegMatrixContraction,
    periodicHypercubicEvenPrimarySpatialPlaquetteOrientation,
    orientedFourEdgePlaquetteWord,
    specialUnitaryMatrixRealFeature,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, mul_assoc]

/-- The algebraic four-fold projective tensor carrier.  Its index is exactly the
four canonical physical edge slots `Fin 4`, so no reassociation or ad hoc edge
permutation is hidden in the carrier. -/
abbrev SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace (N : ℕ) :=
  PiTensorProduct ℝ
    (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)

/-- Canonical pure four-edge tensor in physical edge order. -/
def specialUnitaryFourLegProjectiveRealFeatureTensor
    (N : ℕ)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N :=
  ⨂ₜ[ℝ] k, v k

/-- Universal projective-tensor linearization of the bounded four-leg feature
contraction. -/
noncomputable def orientedFourLegProjectiveRealFeatureContraction
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  PiTensorProduct.liftIsometry ℝ
    (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)
    (SpecialUnitaryMatrixRealFeatureSpace N)
    (orientedFourLegRealFeatureContraction N orientation)

/-- The projective tensor linearization agrees exactly with the multilinear
contraction on pure four-edge tensors. -/
@[simp] theorem orientedFourLegProjectiveRealFeatureContraction_pure
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    orientedFourLegProjectiveRealFeatureContraction N orientation
        (specialUnitaryFourLegProjectiveRealFeatureTensor N v) =
      orientedFourLegRealFeatureContraction N orientation v := by
  simp [orientedFourLegProjectiveRealFeatureContraction,
    specialUnitaryFourLegProjectiveRealFeatureTensor]

/-- Primary-spatial specialization of the algebraic projective-tensor
contraction. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction
    (H N : ℕ) :
    SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  orientedFourLegProjectiveRealFeatureContraction N
    (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)

/-- On a pure tensor of four `SU(N)` defining features, the algebraic tensor
contraction is exactly the naturally oriented primary-plaquette feature. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction_apply
    (H N : ℕ)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction H N
        (specialUnitaryFourLegProjectiveRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N (x k))) =
      specialUnitaryMatrixRealFeature N (orientedFourEdgePlaquetteWord x) := by
  rw [orientedFourLegProjectiveRealFeatureContraction_pure]
  exact periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction_apply
    H N x

/-- Completion of the algebraic four-fold projective tensor carrier. -/
abbrev SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace (N : ℕ) :=
  UniformSpace.Completion
    (SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N)

/-- Extend the projective-tensor contraction continuously to its completed
carrier.  The codomain is the complete finite-dimensional Euclidean real
feature space. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction
    (H N : ℕ) :
    SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction H N).extend
    (UniformSpace.Completion.toComplL :
      SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
        SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N)

/-- The completed contraction restricts exactly to the algebraic contraction
on the canonical dense tensor carrier. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction_coe
    (H N : ℕ)
    (t : SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction H N
        (t : SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N) =
      periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction H N t := by
  exact ContinuousLinearMap.extend_eq
    (periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction H N)
    (e := (UniformSpace.Completion.toComplL :
      SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
        SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        (UniformSpace.Completion.denseRange_coe :
          DenseRange fun x : SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N =>
            (x : SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N)))
    (by
      simpa only [UniformSpace.Completion.coe_toComplL] using
        UniformSpace.Completion.isUniformInducing_coe
          (SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N))
    t

/-- The completed four-leg contraction on actual boundary-restricted physical
edge variables is exactly the defining feature of the canonical primary
spatial plaquette holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction_boundaryRestriction
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction H N
        ((specialUnitaryFourLegProjectiveRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A
              (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))) :
            SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction_coe]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction_apply]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteHolonomy_eq_orientedFourEdge]
  congr 2
  funext k
  exact periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryRestriction_apply H A k

/-- Fibered-coordinate version: the same completed contraction depends only on
`b`; it reconstructs the primary spatial plaquette holonomy of every assembly
`boundaryFiberedAssemble b x y`, independently of the two open-half choices. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction_boundaryFibered
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction H N
        ((specialUnitaryFourLegProjectiveRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            (b (periodicHypercubicEvenPrimarySpatialPlaquetteFixedEdgeEmbedding H k))) :
            SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) := by
  simpa using
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction_boundaryRestriction
      H N
      ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)

/-- Replacing the four explicit boundary coordinates by the four canonical
temporal-companion boundary legs leaves the exact completed primary-plaquette
feature unchanged. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction_temporalCompanionBoundaryLegs
    (H N : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction H N
        ((specialUnitaryFourLegProjectiveRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N
            (periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b
              (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :
            SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N) :
          SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N) =
      specialUnitaryMatrixRealFeature N
        (periodicHypercubicPlaquetteHolonomy
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y)
          (periodicHypercubicEvenPrimarySpatialPlaquette H)) := by
  simp_rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion_fiberedBoundaryLeg_eq]
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction_boundaryFibered
      H N b x y

/-- Apply the identical completed tensor architecture to the four positive-half
open paths supplied by the canonical temporal companions. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfCompletedRealFeature
    (H N : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    SpecialUnitaryMatrixRealFeatureSpace N :=
  periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction H N
    ((specialUnitaryFourLegProjectiveRealFeatureTensor N
      (fun k => specialUnitaryMatrixRealFeature N
        (periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))) :
        SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N) :
      SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N)

/-- Explicit pure-tensor formula for the four temporal-companion open-half
feature: it is the same orientation-correct four-edge word in defining real
matrix feature coordinates. -/
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
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction_coe]
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction_apply
      H N
      (fun k =>
        periodicHypercubicEvenPositiveBoundaryTemporalFiberedOpenPath x
          (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanion H k))

end

end MathlibAnalytic
end MGAP4D
