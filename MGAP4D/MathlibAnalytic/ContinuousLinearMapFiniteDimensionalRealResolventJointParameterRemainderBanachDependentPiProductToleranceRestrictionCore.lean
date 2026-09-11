import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiProductToleranceOrderCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- Restrict a dependent Pi-product to a finite coordinate subfamily. -/
noncomputable def continuousLinearMapJointRemainderDependentPiRestrictionMap
    {ι : Type*} [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (s : Finset ι) :
    (∀ i, W i) →L[ℝ] (∀ i : {i // i ∈ s}, W i.1) :=
  ContinuousLinearMap.pi (fun i =>
    (ContinuousLinearMap.proj i.1 : (∀ j, W j) →L[ℝ] W i.1))

@[simp] theorem continuousLinearMapJointRemainderDependentPiRestrictionMap_apply
    {ι : Type*} [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (s : Finset ι) (x : ∀ i, W i) (i : {i // i ∈ s}) :
    continuousLinearMapJointRemainderDependentPiRestrictionMap s x i = x i.1 := by
  rfl

/-- Finite dependent-product restriction is a contraction. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiRestrictionMap_le_one
    {ι : Type*} [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (s : Finset ι) :
    ‖(continuousLinearMapJointRemainderDependentPiRestrictionMap
      (W := W) s :
      (∀ i, W i) →L[ℝ] (∀ i : {i // i ∈ s}, W i.1))‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound
    (continuousLinearMapJointRemainderDependentPiRestrictionMap
      (W := W) s :
      (∀ i, W i) →L[ℝ] (∀ i : {i // i ∈ s}, W i.1))
    zero_le_one
    (fun x => by
      simp only [one_mul]
      rw [pi_norm_le_iff_of_nonneg
        (x := continuousLinearMapJointRemainderDependentPiRestrictionMap
          (W := W) s x)
        (r := ‖x‖) (norm_nonneg x)]
      intro i
      simpa using
        ((pi_norm_le_iff_of_nonneg (x := x) (r := ‖x‖)
          (norm_nonneg x)).1 le_rfl i.1))

/-- Subfamily encoding is postcomposition by the restriction contraction. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiRestrictionMap_comp_observable
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (s : Finset ι) :
    (continuousLinearMapJointRemainderDependentPiRestrictionMap
      (W := W) s).comp
        (continuousLinearMapJointRemainderDependentPiProductObservable φ) =
      continuousLinearMapJointRemainderDependentPiProductObservable
        (fun i : {i // i ∈ s} => φ i.1) := by
  ext A i
  rfl

/-- The subfamily Pi-product observable has no larger operator norm. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiProductObservable_subfamily_le
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (s : Finset ι) :
    ‖continuousLinearMapJointRemainderDependentPiProductObservable
        (fun i : {i // i ∈ s} => φ i.1)‖ ≤
      ‖continuousLinearMapJointRemainderDependentPiProductObservable φ‖ := by
  let r : (∀ i, W i) →L[ℝ] (∀ i : {i // i ∈ s}, W i.1) :=
    continuousLinearMapJointRemainderDependentPiRestrictionMap
      (W := W) s
  let f : (V →L[ℝ] V) →L[ℝ] (∀ i, W i) :=
    continuousLinearMapJointRemainderDependentPiProductObservable φ
  have hcomp : r.comp f =
      continuousLinearMapJointRemainderDependentPiProductObservable
        (fun i : {i // i ∈ s} => φ i.1) := by
    simpa [r, f] using
      (continuousLinearMapJointRemainderDependentPiRestrictionMap_comp_observable
        (W := W) φ s)
  rw [← hcomp]
  calc
    ‖r.comp f‖ ≤ ‖r‖ * ‖f‖ := r.opNorm_comp_le f
    _ ≤ 1 * ‖f‖ :=
      mul_le_mul_of_nonneg_right
        (by
          simpa [r] using
            (continuousLinearMapJointRemainder_norm_dependentPiRestrictionMap_le_one
              (W := W) s))
        (norm_nonneg f)
    _ = ‖f‖ := by rw [one_mul]

/-- Coordinate-tolerance order of a subfamily is below the full order. -/
theorem continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_subfamily_le
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (s : Finset ι) (q M : ℝ) (epsilon : ι → ℝ) :
    continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        (fun i : {i // i ∈ s} => φ i.1)
        q M (fun i => epsilon i.1) ≤
      continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        φ q M epsilon := by
  apply
    (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_le_iff
      (fun i : {i // i ∈ s} => φ i.1)
      q M (fun i => epsilon i.1) _).2
  intro i
  exact continuousLinearMapJointRemainder_le_finiteMaximum
    (fun j => continuousLinearMapJointRemainderResponseSafeOrder
      (φ j) q M (epsilon j)) i.1

/-- Finite subfamily restriction cannot increase the vector-tolerance master. -/
theorem continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_subfamily_le
    {V ι : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι]
    {W : ι → Type*}
    [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i) (s : Finset ι)
    {q M epsilonCarrier epsilonProduct epsilonTrace : ℝ}
    (epsilonCoordinate : ι → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hProduct : 0 < epsilonProduct) :
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        (fun i : {i // i ∈ s} => φ i.1)
        q M epsilonCarrier epsilonProduct (fun i => epsilonCoordinate i.1)
        epsilonTrace ≤
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        φ q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  unfold continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
  apply max_le_max le_rfl
  apply max_le_max
  · exact continuousLinearMapJointRemainderResponseSafeOrder_mono_norm
      (continuousLinearMapJointRemainderDependentPiProductObservable
        (fun i : {i // i ∈ s} => φ i.1))
      (continuousLinearMapJointRemainderDependentPiProductObservable φ)
      hq0 hq1 hM hProduct
      (continuousLinearMapJointRemainder_norm_dependentPiProductObservable_subfamily_le
        φ s)
  · exact max_le_max
      (continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_subfamily_le
        φ s q M epsilonCoordinate)
      le_rfl

/-- Coordinate-tolerance aggregate is invariant under simultaneous reindexing. -/
theorem continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_reindex_eq
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilon : Fin n → ℝ) (e : Fin n ≃ Fin n) (q M : ℝ) :
    continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        (fun i => φ (e i)) q M (fun i => epsilon (e i)) =
      continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder
        φ q M epsilon := by
  exact continuousLinearMapJointRemainderFiniteMaximum_reindex_eq
    (fun i => continuousLinearMapJointRemainderResponseSafeOrder
      (φ i) q M (epsilon i)) e

/-- Homogeneous vector-tolerance master is invariant under simultaneous reindexing. -/
theorem continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder_reindex_eq
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ}
    (φ : Fin n → ((V →L[ℝ] V) →L[ℝ] W))
    (epsilonCoordinate : Fin n → ℝ) (e : Fin n ≃ Fin n)
    {q M epsilonCarrier epsilonProduct epsilonTrace : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hProduct : 0 < epsilonProduct) :
    continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        (W := fun _ : Fin n => W) (fun i => φ (e i))
        q M epsilonCarrier epsilonProduct (fun i => epsilonCoordinate (e i))
        epsilonTrace =
      continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
        (W := fun _ : Fin n => W) φ
        q M epsilonCarrier epsilonProduct epsilonCoordinate epsilonTrace := by
  unfold continuousLinearMapJointRemainderDependentPiProductToleranceMasterSafeOrder
  rw [continuousLinearMapJointRemainderResponseSafeOrder_dependentPiProduct_reindex_eq
    φ e hq0 hq1 hM hProduct]
  rw [continuousLinearMapJointRemainderDependentPiCoordinateToleranceSafeOrder_reindex_eq
    φ epsilonCoordinate e q M]

end MathlibAnalytic
end MGAP4D
