import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachFiniteResponseFamilyCore
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- Postcompose every observable in a finite response family by one bounded
linear map.  This is the covariant transport operation on finite response
families. -/
def continuousLinearMapJointRemainderPostcomposeResponseFamily
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) :
    List ((V →L[ℝ] V) →L[ℝ] X) :=
  φs.map fun φ => ψ.comp φ

@[simp] theorem continuousLinearMapJointRemainderPostcomposeResponseFamily_nil
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X) :
    continuousLinearMapJointRemainderPostcomposeResponseFamily
      (V := V) ψ [] = [] := by
  rfl

@[simp] theorem continuousLinearMapJointRemainderPostcomposeResponseFamily_cons
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) :
    continuousLinearMapJointRemainderPostcomposeResponseFamily ψ (φ :: φs) =
      ψ.comp φ :: continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs := by
  rfl

@[simp] theorem continuousLinearMapJointRemainderPostcomposeResponseFamily_append
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X)
    (φs χs : List ((V →L[ℝ] V) →L[ℝ] W)) :
    continuousLinearMapJointRemainderPostcomposeResponseFamily ψ (φs ++ χs) =
      continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs ++
        continuousLinearMapJointRemainderPostcomposeResponseFamily ψ χs := by
  simp [continuousLinearMapJointRemainderPostcomposeResponseFamily]

@[simp] theorem continuousLinearMapJointRemainderPostcomposeResponseFamily_length
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) :
    (continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs).length =
      φs.length := by
  simp [continuousLinearMapJointRemainderPostcomposeResponseFamily]

/-- Membership in a transported family is exactly membership before
postcomposition together with the postcomposition equation. -/
theorem continuousLinearMapJointRemainder_mem_postcomposeResponseFamily_iff
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (θ : (V →L[ℝ] V) →L[ℝ] X) :
    θ ∈ continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs ↔
      ∃ φ ∈ φs, ψ.comp φ = θ := by
  simpa [continuousLinearMapJointRemainderPostcomposeResponseFamily] using
    (List.mem_map (f := fun φ : (V →L[ℝ] V) →L[ℝ] W => ψ.comp φ)
      (l := φs) (b := θ))

/-- Postcomposition by the identity leaves a finite response family unchanged. -/
@[simp] theorem continuousLinearMapJointRemainderPostcomposeResponseFamily_id
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) :
    continuousLinearMapJointRemainderPostcomposeResponseFamily
      (ContinuousLinearMap.id ℝ W) φs = φs := by
  induction φs with
  | nil => simp
  | cons φ φs ih =>
      simp [ih]

/-- Successive postcomposition is postcomposition by the composite map. -/
@[simp] theorem continuousLinearMapJointRemainderPostcomposeResponseFamily_comp
    {V W X Y : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (χ : X →L[ℝ] Y) (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W)) :
    continuousLinearMapJointRemainderPostcomposeResponseFamily χ
        (continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs) =
      continuousLinearMapJointRemainderPostcomposeResponseFamily (χ.comp ψ) φs := by
  induction φs with
  | nil => simp
  | cons φ φs ih =>
      simp [ih, ContinuousLinearMap.comp_assoc]

/-- The universally positive response order is monotone in the operator norm
of the observable. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_mono_norm
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) (hnorm : ‖φ‖ ≤ ‖θ‖) :
    continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder θ q M epsilon := by
  have hφC : 0 < (‖φ‖ + 1) * M :=
    mul_pos (by linarith [norm_nonneg φ]) hM
  have hθC : 0 < (‖θ‖ + 1) * M :=
    mul_pos (by linarith [norm_nonneg θ]) hM
  have hC : (‖φ‖ + 1) * M ≤ (‖θ‖ + 1) * M := by
    exact mul_le_mul_of_nonneg_right (by linarith) hM.le
  simpa [continuousLinearMapJointRemainderResponseSafeOrder] using
    geometricDecaySharpTruncationOrder_mono_constant
      hq0 hq1 hφC hθC hC hepsilon

/-- Postcomposition by an operator of norm at most one does not increase the
operator norm of an observable. -/
theorem continuousLinearMapJointRemainder_norm_comp_le_of_norm_le_one
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (hψ : ‖ψ‖ ≤ 1) :
    ‖ψ.comp φ‖ ≤ ‖φ‖ := by
  calc
    ‖ψ.comp φ‖ ≤ ‖ψ‖ * ‖φ‖ := ψ.opNorm_comp_le φ
    _ ≤ 1 * ‖φ‖ := mul_le_mul_of_nonneg_right hψ (norm_nonneg φ)
    _ = ‖φ‖ := one_mul _

/-- Contraction postcomposition cannot increase the response safe order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_comp_le_of_norm_le_one
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X) (φ : (V →L[ℝ] V) →L[ℝ] W)
    {q M epsilon : ℝ}
    (hψ : ‖ψ‖ ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (ψ.comp φ) q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon := by
  exact continuousLinearMapJointRemainderResponseSafeOrder_mono_norm
    (ψ.comp φ) φ hq0 hq1 hM hepsilon
    (continuousLinearMapJointRemainder_norm_comp_le_of_norm_le_one ψ φ hψ)

/-- Contraction postcomposition cannot increase the common safe order of a
finite response family. -/
theorem continuousLinearMapJointRemainderResponseFamilySafeOrder_postcompose_le
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    {q M epsilon : ℝ}
    (hψ : ‖ψ‖ ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseFamilySafeOrder
        (continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs)
        q M epsilon ≤
      continuousLinearMapJointRemainderResponseFamilySafeOrder φs q M epsilon := by
  induction φs with
  | nil => simp
  | cons φ φs ih =>
      rw [continuousLinearMapJointRemainderPostcomposeResponseFamily_cons]
      rw [continuousLinearMapJointRemainderResponseFamilySafeOrder_cons]
      rw [continuousLinearMapJointRemainderResponseFamilySafeOrder_cons]
      exact max_le_max
        (continuousLinearMapJointRemainderResponseSafeOrder_comp_le_of_norm_le_one
          ψ φ hψ hq0 hq1 hM hepsilon)
        ih

/-- Contraction postcomposition cannot increase the finite-family master
order; the carrier and trace parts are unchanged and the response-family part
can only decrease. -/
theorem continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder_postcompose_le
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    {q M epsilon : ℝ}
    (hψ : ‖ψ‖ ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        (continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs)
        q M epsilon ≤
      continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        φs q M epsilon := by
  unfold continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
  exact max_le_max le_rfl
    (max_le_max
      (continuousLinearMapJointRemainderResponseFamilySafeOrder_postcompose_le
        ψ φs hψ hq0 hq1 hM hepsilon)
      le_rfl)

/-- The original finite-family master order simultaneously controls all
responses after contraction postcomposition, without choosing a new order. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_finiteResponseFamilyMasterSafeOrder_postcompose
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : W →L[ℝ] X)
    (φs : List ((V →L[ℝ] V) →L[ℝ] W))
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hψ : ‖ψ‖ ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hepsilon : 0 < epsilon) :
    let N := continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
      φs q M epsilon
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    (∀ φ ∈ φs,
      ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
          (ψ.comp φ) N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon) ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  dsimp
  have htransport :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_finiteResponseFamilyMasterSafeOrder_le
      (continuousLinearMapJointRemainderPostcomposeResponseFamily ψ φs)
      (continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
        φs q M epsilon)
      taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
      hq0 hq1 hM hperturb hend
      (continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder_postcompose_le
        ψ φs hψ hq0 hq1 hM hepsilon)
      hepsilon
  refine ⟨htransport.1, ?_, htransport.2.2⟩
  intro φ hφ
  exact htransport.2.1 (ψ.comp φ)
    (by
      exact List.mem_map.mpr ⟨φ, hφ, rfl⟩)

/-- The operator norm of the first component observable is bounded by the norm
of the binary product observable. -/
theorem continuousLinearMapJointRemainder_norm_le_prod_left
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X) :
    ‖φ‖ ≤ ‖φ.prod θ‖ := by
  rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact le_max_left _ _

/-- The operator norm of the second component observable is bounded by the norm
of the binary product observable. -/
theorem continuousLinearMapJointRemainder_norm_le_prod_right
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X) :
    ‖θ‖ ≤ ‖φ.prod θ‖ := by
  rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact le_max_right _ _

/-- The first coordinate projection recovers the first component observable. -/
@[simp] theorem continuousLinearMapJointRemainder_fst_comp_prod
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X) :
    (ContinuousLinearMap.fst ℝ W X).comp (φ.prod θ) = φ := by
  ext A
  rfl

/-- The second coordinate projection recovers the second component observable. -/
@[simp] theorem continuousLinearMapJointRemainder_snd_comp_prod
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X) :
    (ContinuousLinearMap.snd ℝ W X).comp (φ.prod θ) = θ := by
  ext A
  rfl

/-- The safe order of the first component is below that of the binary product
observable. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_le_prod_left
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (φ.prod θ) q M epsilon := by
  exact continuousLinearMapJointRemainderResponseSafeOrder_mono_norm
    φ (φ.prod θ) hq0 hq1 hM hepsilon
    (continuousLinearMapJointRemainder_norm_le_prod_left φ θ)

/-- The safe order of the second component is below that of the binary product
observable. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_le_prod_right
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder θ q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (φ.prod θ) q M epsilon := by
  exact continuousLinearMapJointRemainderResponseSafeOrder_mono_norm
    θ (φ.prod θ) hq0 hq1 hM hepsilon
    (continuousLinearMapJointRemainder_norm_le_prod_right φ θ)

/-- One natural number controls the carrier, a binary product observable, both
coordinate observables, and trace. -/
noncomputable def continuousLinearMapJointRemainderBinaryProductMasterSafeOrder
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (q M epsilon : ℝ) : ℕ :=
  continuousLinearMapJointRemainderFiniteResponseFamilyMasterSafeOrder
    [φ.prod θ] q M epsilon

/-- The product-observable response order lies below the binary-product master
order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_prod_le_binaryProductMasterSafeOrder
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (φ.prod θ) q M epsilon ≤
      continuousLinearMapJointRemainderBinaryProductMasterSafeOrder
        φ θ q M epsilon := by
  exact
    continuousLinearMapJointRemainderResponseSafeOrder_le_finiteResponseFamilyMasterSafeOrder_of_mem
      [φ.prod θ] q M epsilon (by simp)

/-- The first coordinate response order lies below the binary-product master
order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_left_le_binaryProductMasterSafeOrder
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder φ q M epsilon ≤
      continuousLinearMapJointRemainderBinaryProductMasterSafeOrder
        φ θ q M epsilon := by
  exact le_trans
    (continuousLinearMapJointRemainderResponseSafeOrder_le_prod_left
      φ θ hq0 hq1 hM hepsilon)
    (continuousLinearMapJointRemainderResponseSafeOrder_prod_le_binaryProductMasterSafeOrder
      φ θ q M epsilon)

/-- The second coordinate response order lies below the binary-product master
order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_right_le_binaryProductMasterSafeOrder
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder θ q M epsilon ≤
      continuousLinearMapJointRemainderBinaryProductMasterSafeOrder
        φ θ q M epsilon := by
  exact le_trans
    (continuousLinearMapJointRemainderResponseSafeOrder_le_prod_right
      φ θ hq0 hq1 hM hepsilon)
    (continuousLinearMapJointRemainderResponseSafeOrder_prod_le_binaryProductMasterSafeOrder
      φ θ q M epsilon)

/-- Every base order above the binary-product master threshold controls the
carrier, product observable, both coordinates, and trace simultaneously. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_binaryProductMasterSafeOrder_le
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (baseOrder taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hbaseOrder : continuousLinearMapJointRemainderBinaryProductMasterSafeOrder
      φ θ q M epsilon ≤ baseOrder)
    (hepsilon : 0 < epsilon) :
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        (φ.prod θ) baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        φ baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        θ baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V baseOrder taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  have hfamily :=
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_finiteResponseFamilyMasterSafeOrder_le
      [φ.prod θ] baseOrder taylorOrder tailOrder m H ds h Rbase Rend
      q M epsilon hq0 hq1 hM hperturb hend hbaseOrder hepsilon
  have hleftOrder := le_trans
    (continuousLinearMapJointRemainderResponseSafeOrder_left_le_binaryProductMasterSafeOrder
      φ θ hq0 hq1 hM hepsilon) hbaseOrder
  have hrightOrder := le_trans
    (continuousLinearMapJointRemainderResponseSafeOrder_right_le_binaryProductMasterSafeOrder
      φ θ hq0 hq1 hM hepsilon) hbaseOrder
  exact ⟨hfamily.1,
    hfamily.2.1 (φ.prod θ) (by simp),
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
      φ baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
      hq0 hq1 hM hperturb hend hleftOrder hepsilon,
    continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJet_norm_lt_of_safeOrder_le
      θ baseOrder taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
      hq0 hq1 hM hperturb hend hrightOrder hepsilon,
    hfamily.2.2⟩

/-- The explicit binary-product master order gives simultaneous control of the
product and both coordinate responses without any further order choice. -/
theorem continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_binaryProductMasterSafeOrder
    {V W X : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (φ : (V →L[ℝ] V) →L[ℝ] W)
    (θ : (V →L[ℝ] V) →L[ℝ] X)
    (taylorOrder tailOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (Rbase Rend : Fin (taylorOrder + 1) → (V →L[ℝ] V))
    (q M epsilon : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hperturb : ∀ k, ‖Rbase k *
      continuousLinearMapJointSpectralOperatorRemainderIncrement m H ds h‖ ≤ q)
    (hend : ∀ k, ‖Rend k‖ ≤ M)
    (hepsilon : 0 < epsilon) :
    let N := continuousLinearMapJointRemainderBinaryProductMasterSafeOrder
      φ θ q M epsilon
    ‖continuousLinearMapJointTaylorDysonRemainderTailRectangularJetFromResolventFamilies
        N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        (φ.prod θ) N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        φ N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailResponseRectangularJetFromResolventFamilies
        θ N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon ∧
    ‖continuousLinearMapJointTaylorDysonRemainderTailTraceRectangularJetFromResolventFamilies
        V N taylorOrder tailOrder m H ds h Rbase Rend‖ < epsilon := by
  dsimp
  exact
    continuousLinearMapJointTaylorDysonRemainderTailRectangularJet_norm_lt_of_binaryProductMasterSafeOrder_le
      φ θ
      (continuousLinearMapJointRemainderBinaryProductMasterSafeOrder φ θ q M epsilon)
      taylorOrder tailOrder m H ds h Rbase Rend q M epsilon
      hq0 hq1 hM hperturb hend le_rfl hepsilon

end MathlibAnalytic
end MGAP4D
