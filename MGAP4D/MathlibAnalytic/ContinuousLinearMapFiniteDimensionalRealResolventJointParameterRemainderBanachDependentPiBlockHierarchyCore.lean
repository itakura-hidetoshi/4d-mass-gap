import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiBlockToleranceOrderCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- A fine block assignment refines a coarse assignment through a parent map. -/
def ContinuousLinearMapJointDependentPiBlockRefines
    {ι κ σ : Type*} (fineOf : ι → κ) (coarseOf : ι → σ)
    (parent : κ → σ) : Prop :=
  ∀ i, coarseOf i = parent (fineOf i)

/-- Every block assignment refines itself through the identity parent map. -/
theorem continuousLinearMapJointDependentPiBlockRefines_refl
    {ι κ : Type*} (blockOf : ι → κ) :
    ContinuousLinearMapJointDependentPiBlockRefines
      blockOf blockOf (fun k => k) := by
  intro i
  rfl

/-- Refinement is transitive along composition of parent maps. -/
theorem continuousLinearMapJointDependentPiBlockRefines_trans
    {ι κ σ μ : Type*}
    {fineOf : ι → κ} {middleOf : ι → σ} {coarseOf : ι → μ}
    {parent₁ : κ → σ} {parent₂ : σ → μ}
    (h₁ : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf middleOf parent₁)
    (h₂ : ContinuousLinearMapJointDependentPiBlockRefines
      middleOf coarseOf parent₂) :
    ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf (fun k => parent₂ (parent₁ k)) := by
  intro i
  rw [h₂ i, h₁ i]

variable {V ι κ σ : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [Fintype ι] [Fintype κ] [Fintype σ]
variable [DecidableEq κ] [DecidableEq σ]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Restrict one coarse block product to a fine block lying over it. -/
noncomputable def continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap
    (fineOf : ι → κ) (coarseOf : ι → σ) (parent : κ → σ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent) (k : κ) :
    (∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
        coarseOf (parent k), W i.1) →L[ℝ]
      (∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
        fineOf k, W i.1) :=
  ContinuousLinearMap.pi (fun i =>
    (ContinuousLinearMap.proj
      (⟨i.1, by simpa [i.2] using hrefines i.1⟩ :
        continuousLinearMapJointRemainderDependentPiBlockFiber
          coarseOf (parent k)) :
      (∀ j : continuousLinearMapJointRemainderDependentPiBlockFiber
        coarseOf (parent k), W j.1) →L[ℝ] W i.1))

@[simp] theorem continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap_apply
    (fineOf : ι → κ) (coarseOf : ι → σ) (parent : κ → σ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent) (k : κ)
    (x : ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
        coarseOf (parent k), W i.1)
    (i : continuousLinearMapJointRemainderDependentPiBlockFiber fineOf k) :
    continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap
      (W := W) fineOf coarseOf parent hrefines k x i =
      x ⟨i.1, by simpa [i.2] using hrefines i.1⟩ := by
  rfl

/-- Fine-block restriction is a contraction for the finite sup norm. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiFineBlockRestrictionMap_le_one
    (fineOf : ι → κ) (coarseOf : ι → σ) (parent : κ → σ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent) (k : κ) :
    ‖(continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap
      (W := W) fineOf coarseOf parent hrefines k :
      (∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
        coarseOf (parent k), W i.1) →L[ℝ]
      (∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber
        fineOf k, W i.1))‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound
    (continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap
      (W := W) fineOf coarseOf parent hrefines k)
    zero_le_one
    (fun x => by
      simp only [one_mul]
      rw [pi_norm_le_iff_of_nonneg
        (x := continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap
          (W := W) fineOf coarseOf parent hrefines k x)
        (r := ‖x‖) (norm_nonneg x)]
      intro i
      simpa using
        ((pi_norm_le_iff_of_nonneg (x := x) (r := ‖x‖)
          (norm_nonneg x)).1 le_rfl
          (⟨i.1, by simpa [i.2] using hrefines i.1⟩ :
            continuousLinearMapJointRemainderDependentPiBlockFiber
              coarseOf (parent k))))

/-- Fine-block observables are exact postcompositions of their parent coarse
block observables by the restriction contraction. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap_comp_coarseBlockObservable
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ) (parent : κ → σ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent) (k : κ) :
    (continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap
      (W := W) fineOf coarseOf parent hrefines k).comp
      (continuousLinearMapJointRemainderDependentPiBlockObservable
        φ coarseOf (parent k)) =
      continuousLinearMapJointRemainderDependentPiBlockObservable
        φ fineOf k := by
  ext A i
  rfl

/-- A fine-block observable has no larger operator norm than its parent coarse
block observable. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiFineBlockObservable_le_coarseBlockObservable
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ) (parent : κ → σ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent) (k : κ) :
    ‖continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k‖ ≤
      ‖continuousLinearMapJointRemainderDependentPiBlockObservable
        φ coarseOf (parent k)‖ := by
  let r := continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap
    (W := W) fineOf coarseOf parent hrefines k
  let f := continuousLinearMapJointRemainderDependentPiBlockObservable
    φ coarseOf (parent k)
  have hcomp : r.comp f =
      continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k := by
    simpa [r, f] using
      (continuousLinearMapJointRemainderDependentPiFineBlockRestrictionMap_comp_coarseBlockObservable
        (W := W) φ fineOf coarseOf parent hrefines k)
  rw [← hcomp]
  calc
    ‖r.comp f‖ ≤ ‖r‖ * ‖f‖ := r.opNorm_comp_le f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (by simpa [r] using
        (continuousLinearMapJointRemainder_norm_dependentPiFineBlockRestrictionMap_le_one
          (W := W) fineOf coarseOf parent hrefines k))
      (norm_nonneg f)
    _ = ‖f‖ := by rw [one_mul]

/-- At one common tolerance, a fine-block response safe order does not exceed
its parent coarse-block order. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_coarseBlock
    [FiniteDimensional ℝ V]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ) (parent : κ → σ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent) (k : κ)
    {q M epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hepsilon : 0 < epsilon) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ fineOf k) q M epsilon ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ coarseOf (parent k)) q M epsilon := by
  exact continuousLinearMapJointRemainderResponseSafeOrder_mono_norm
    (continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k)
    (continuousLinearMapJointRemainderDependentPiBlockObservable
      φ coarseOf (parent k))
    hq0 hq1 hM hepsilon
    (continuousLinearMapJointRemainder_norm_dependentPiFineBlockObservable_le_coarseBlockObservable
      (W := W) φ fineOf coarseOf parent hrefines k)

/-- A fine-block order at a relaxed tolerance is controlled by its parent
coarse-block order at the inherited stricter tolerance. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_coarseBlock_of_parentTolerance_le
    [FiniteDimensional ℝ V]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ) (parent : κ → σ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent) (k : κ)
    {q M : ℝ} {epsilonFine : κ → ℝ} {epsilonCoarse : σ → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hFine : ∀ j, 0 < epsilonFine j)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hRelax : ∀ j, epsilonCoarse (parent j) ≤ epsilonFine j) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ fineOf k) q M (epsilonFine k) ≤
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ coarseOf (parent k)) q M (epsilonCoarse (parent k)) := by
  exact (continuousLinearMapJointRemainderResponseSafeOrder_antitone_epsilon
    (continuousLinearMapJointRemainderDependentPiBlockObservable φ fineOf k)
    hq0 hq1 hM (hCoarse (parent k)) (hFine k) (hRelax k)).trans
    (continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_coarseBlock
      (W := W) φ fineOf coarseOf parent hrefines k
      hq0 hq1 hM (hCoarse (parent k)))

/-- The entire fine-block tolerance family is bounded by the parent coarse
block family under inherited or relaxed tolerances. -/
theorem continuousLinearMapJointRemainderDependentPiFineBlockResponseToleranceSafeOrder_le_coarse
    [FiniteDimensional ℝ V]
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (fineOf : ι → κ) (coarseOf : ι → σ) (parent : κ → σ)
    (hrefines : ContinuousLinearMapJointDependentPiBlockRefines
      fineOf coarseOf parent)
    {q M : ℝ} {epsilonFine : κ → ℝ} {epsilonCoarse : σ → ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hM : 0 < M)
    (hFine : ∀ k, 0 < epsilonFine k)
    (hCoarse : ∀ c, 0 < epsilonCoarse c)
    (hRelax : ∀ k, epsilonCoarse (parent k) ≤ epsilonFine k) :
    continuousLinearMapJointRemainderDependentPiBlockResponseToleranceSafeOrder
        φ fineOf q M epsilonFine ≤
      continuousLinearMapJointRemainderDependentPiBlockResponseToleranceSafeOrder
        φ coarseOf q M epsilonCoarse := by
  apply (continuousLinearMapJointRemainderDependentBlockResponseToleranceSafeOrder_le_iff
    (fun k => continuousLinearMapJointRemainderDependentPiBlockObservable
      φ fineOf k) q M epsilonFine _).2
  intro k
  exact (continuousLinearMapJointRemainderResponseSafeOrder_fineBlock_le_coarseBlock_of_parentTolerance_le
    (W := W) φ fineOf coarseOf parent hrefines k
    hq0 hq1 hM hFine hCoarse hRelax).trans
    (continuousLinearMapJointRemainder_le_finiteMaximum
      (fun c => continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockObservable
          φ coarseOf c) q M (epsilonCoarse c)) (parent k))

end MathlibAnalytic
end MGAP4D
