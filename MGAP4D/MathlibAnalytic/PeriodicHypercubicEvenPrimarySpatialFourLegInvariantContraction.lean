import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialEdgeTemporalCompanion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimarySpatialPlaquetteWilsonClassFunction
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceKernelFeature
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Tactic
import Mathlib.Tactic.FunProp

namespace MGAP4D
namespace MathlibAnalytic

open scoped TensorProduct

noncomputable section

/-- Recover a complex matrix from the transposed real/imaginary coordinates of
its defining Euclidean real feature.  Matrix space stays algebraic here; all
continuous structure below lives on the canonical real feature space. -/
noncomputable def realFeatureComplexMatrixLinearMap
    (N : ℕ) :
    SpecialUnitaryMatrixRealFeatureSpace N →ₗ[ℝ]
      Matrix (Fin N) (Fin N) ℂ where
  toFun := fun v i j => ⟨v ((j, i), true), v ((j, i), false)⟩
  map_add' := by
    intro v w
    ext i j
    apply Complex.ext <;> simp
  map_smul' := by
    intro r v
    ext i j
    apply Complex.ext <;> simp

/-- Realification is real-linear into the canonical Euclidean matrix-feature
space. -/
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

@[simp] theorem complexMatrixRealFeature_add
    (N : ℕ)
    (A B : Matrix (Fin N) (Fin N) ℂ) :
    complexMatrixRealFeature N (A + B) =
      complexMatrixRealFeature N A + complexMatrixRealFeature N B := by
  exact (complexMatrixRealFeatureLinearMap N).map_add A B

@[simp] theorem complexMatrixRealFeature_smul
    (N : ℕ)
    (r : ℝ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    complexMatrixRealFeature N (r • A) =
      r • complexMatrixRealFeature N A := by
  exact (complexMatrixRealFeatureLinearMap N).map_smul r A

@[simp] theorem realFeatureComplexMatrixLinearMap_complexMatrixRealFeature
    (N : ℕ)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    realFeatureComplexMatrixLinearMap N (complexMatrixRealFeature N A) = A := by
  ext i j
  apply Complex.ext <;>
    simp [realFeatureComplexMatrixLinearMap, complexMatrixRealFeature]

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

/-- Canonical signed-edge orientation transported to degree-one Euclidean
matrix features. -/
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

/-- Finite dimensionality upgrades transported multiplication to a bounded
real bilinear map without putting a topology on raw matrices. -/
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

/-- Algebraic four-leg contraction in the canonical `Fin 4` edge order.  The
constructor fixes one decidable equality instance, avoiding any hidden
`Function.update` instance mismatch in the multilinearity laws. -/
noncomputable def orientedFourLegRealFeatureMultilinearMap
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    MultilinearMap ℝ
      (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)
      (SpecialUnitaryMatrixRealFeatureSpace N) := by
  classical
  refine MultilinearMap.mk'
    (fun v =>
      realFeatureMatrixMulLinearMap N
        (realFeatureMatrixMulLinearMap N
          (orientedRealFeatureLinearMap N (orientation 0) (v 0))
          (orientedRealFeatureLinearMap N (orientation 1) (v 1)))
        (realFeatureMatrixMulLinearMap N
          (orientedRealFeatureLinearMap N (orientation 2) (v 2))
          (orientedRealFeatureLinearMap N (orientation 3) (v 3)))) ?_ ?_
  · intro v i x y
    fin_cases i <;> simp [mul_add, add_mul]
  · intro v i r x
    fin_cases i <;> simp [smul_mul_assoc]

/-- Generic bounded four-leg contraction.  Continuity is inherited entirely
from bounded bilinear multiplication and bounded orientation maps on the
Euclidean degree-one feature space. -/
noncomputable def orientedFourLegRealFeatureContraction
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)
      (SpecialUnitaryMatrixRealFeatureSpace N) where
  toMultilinearMap := orientedFourLegRealFeatureMultilinearMap N orientation
  cont := by
    change Continuous
      (fun v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N =>
        realFeatureMatrixMulContinuousBilinearMap N
          (realFeatureMatrixMulContinuousBilinearMap N
            ((orientedRealFeatureLinearMap N (orientation 0)).toContinuousLinearMap (v 0))
            ((orientedRealFeatureLinearMap N (orientation 1)).toContinuousLinearMap (v 1)))
          (realFeatureMatrixMulContinuousBilinearMap N
            ((orientedRealFeatureLinearMap N (orientation 2)).toContinuousLinearMap (v 2))
            ((orientedRealFeatureLinearMap N (orientation 3)).toContinuousLinearMap (v 3))))
    fun_prop

@[simp] theorem orientedFourLegRealFeatureContraction_apply
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    orientedFourLegRealFeatureContraction N orientation v =
      realFeatureMatrixMulLinearMap N
        (realFeatureMatrixMulLinearMap N
          (orientedRealFeatureLinearMap N (orientation 0) (v 0))
          (orientedRealFeatureLinearMap N (orientation 1) (v 1)))
        (realFeatureMatrixMulLinearMap N
          (orientedRealFeatureLinearMap N (orientation 2) (v 2))
          (orientedRealFeatureLinearMap N (orientation 3) (v 3))) := by
  rfl

/-- The primary plaquette reuses the orientation already stored in the
canonical signed-boundary API. -/
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

/-- Actual bounded four-leg contraction for the primary spatial plaquette. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction
    (H N : ℕ) :
    ContinuousMultilinearMap ℝ
      (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)
      (SpecialUnitaryMatrixRealFeatureSpace N) :=
  orientedFourLegRealFeatureContraction N
    (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)

/-- Four defining edge features contract to the exact defining real feature of
the existing naturally oriented primary-plaquette word. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction_apply
    (H N : ℕ)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction H N
        (fun k => specialUnitaryMatrixRealFeature N (x k)) =
      specialUnitaryMatrixRealFeature N (orientedFourEdgePlaquetteWord x) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction
  rw [orientedFourLegRealFeatureContraction_apply]
  change _ = complexMatrixRealFeature N
    ((orientedFourEdgePlaquetteWord x : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      Matrix (Fin N) (Fin N) ℂ)
  simp [periodicHypercubicEvenPrimarySpatialPlaquetteOrientation,
    realFeatureMatrixMulLinearMap_apply,
    orientedFourEdgePlaquetteWord,
    mul_assoc]

/-- Algebraic four-fold projective tensor carrier indexed by the four canonical
physical edge slots. -/
abbrev SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace (N : ℕ) :=
  PiTensorProduct ℝ
    (fun _ : Fin 4 => SpecialUnitaryMatrixRealFeatureSpace N)

/-- Canonical pure four-edge tensor in physical edge order. -/
def specialUnitaryFourLegProjectiveRealFeatureTensor
    (N : ℕ)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N :=
  ⨂ₜ[ℝ] k, v k

/-- Universal projective-tensor linearization of the bounded four-leg
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

@[simp] theorem orientedFourLegProjectiveRealFeatureContraction_pure
    (N : ℕ)
    (orientation : Fin 4 → PeriodicHypercubicOrientation)
    (v : Fin 4 → SpecialUnitaryMatrixRealFeatureSpace N) :
    orientedFourLegProjectiveRealFeatureContraction N orientation
        (specialUnitaryFourLegProjectiveRealFeatureTensor N v) =
      orientedFourLegRealFeatureContraction N orientation v := by
  simp [orientedFourLegProjectiveRealFeatureContraction,
    specialUnitaryFourLegProjectiveRealFeatureTensor]

/-- Primary-spatial specialization on the algebraic projective tensor carrier. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction
    (H N : ℕ) :
    SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  orientedFourLegProjectiveRealFeatureContraction N
    (periodicHypercubicEvenPrimarySpatialPlaquetteOrientation H)

/-- Pure-tensor specialization of the primary projective contraction. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction_apply
    (H N : ℕ)
    (x : Fin 4 → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction H N
        (specialUnitaryFourLegProjectiveRealFeatureTensor N
          (fun k => specialUnitaryMatrixRealFeature N (x k))) =
      specialUnitaryMatrixRealFeature N (orientedFourEdgePlaquetteWord x) := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction
  rw [orientedFourLegProjectiveRealFeatureContraction_pure]
  exact periodicHypercubicEvenPrimarySpatialPlaquetteFourLegRealFeatureContraction_apply
    H N x

/-- Completion of the projective four-edge tensor carrier. -/
abbrev SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace (N : ℕ) :=
  UniformSpace.Completion
    (SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N)

/-- Continuous extension of the primary four-leg projective contraction to the
completed carrier. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteCompletedProjectiveRealFeatureContraction
    (H N : ℕ) :
    SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
      SpecialUnitaryMatrixRealFeatureSpace N :=
  (periodicHypercubicEvenPrimarySpatialPlaquetteProjectiveRealFeatureContraction H N).extend
    (UniformSpace.Completion.toComplL :
      SpecialUnitaryFourLegProjectiveRealFeatureTensorSpace N →L[ℝ]
        SpecialUnitaryCompletedFourLegProjectiveRealFeatureTensorSpace N)

/-- The completed contraction agrees exactly with the algebraic contraction on
the dense projective tensor carrier. -/
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

/-- Contracting the four actual boundary-restricted physical edge variables
recovers the defining feature of the canonical primary spatial plaquette
holonomy. -/
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
  simp_rw [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryRestriction_apply]

/-- Fibered-coordinate specialization: the completed four-leg feature depends
only on the boundary coordinate `b`, hence is independent of both open-half
coordinates. -/
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

/-- The four canonical temporal-companion boundary legs give the identical
completed primary-plaquette feature. -/
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

/-- Apply the same completed tensor architecture to the four positive-half open
paths supplied by the canonical temporal companions. -/
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

/-- The open-half contraction is exactly the same canonical orientation-correct
four-edge word, now built from the four temporal-companion open paths. -/
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