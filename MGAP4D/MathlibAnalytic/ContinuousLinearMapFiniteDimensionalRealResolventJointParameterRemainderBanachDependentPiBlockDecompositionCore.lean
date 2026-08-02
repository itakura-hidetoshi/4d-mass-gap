import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterRemainderBanachDependentPiProductToleranceCore
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000

/-- The coordinates assigned to one finite block. -/
abbrev continuousLinearMapJointRemainderDependentPiBlockFiber
    {ι β : Type*} (blockOf : ι → β) (b : β) :=
  {i : ι // blockOf i = b}

variable {V ι β : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [Fintype ι] [Fintype β] [DecidableEq β]
variable {W : ι → Type*}
variable [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Decompose a dependent Pi-product into the nested Pi-product of its block
fibers. -/
noncomputable def continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
    (blockOf : ι → β) :
    (∀ i, W i) →L[ℝ]
      (∀ b, ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
        W i.1) :=
  ContinuousLinearMap.pi (fun b =>
    ContinuousLinearMap.pi (fun i =>
      (ContinuousLinearMap.proj i.1 : (∀ j, W j) →L[ℝ] W i.1)))

@[simp] theorem continuousLinearMapJointRemainderDependentPiBlockDecomposeMap_apply
    (blockOf : ι → β) (x : ∀ i, W i) (b : β)
    (i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b) :
    continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
        (W := W) blockOf x b i = x i.1 := by
  rfl

/-- Reassemble the nested block Pi-product into the original dependent
Pi-product. -/
noncomputable def continuousLinearMapJointRemainderDependentPiBlockAssembleMap
    (blockOf : ι → β) :
    (∀ b, ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
      W i.1) →L[ℝ] (∀ i, W i) :=
  ContinuousLinearMap.pi (fun i =>
    ((ContinuousLinearMap.proj
        (⟨i, rfl⟩ : continuousLinearMapJointRemainderDependentPiBlockFiber
          blockOf (blockOf i)) :
        (∀ j : continuousLinearMapJointRemainderDependentPiBlockFiber
          blockOf (blockOf i), W j.1) →L[ℝ] W i).comp
      (ContinuousLinearMap.proj (blockOf i) :
        (∀ b, ∀ j : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
          W j.1) →L[ℝ]
        (∀ j : continuousLinearMapJointRemainderDependentPiBlockFiber
          blockOf (blockOf i), W j.1))))

@[simp] theorem continuousLinearMapJointRemainderDependentPiBlockAssembleMap_apply
    (blockOf : ι → β)
    (x : ∀ b, ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
      W i.1) (i : ι) :
    continuousLinearMapJointRemainderDependentPiBlockAssembleMap
        (W := W) blockOf x i = x (blockOf i) ⟨i, rfl⟩ := by
  rfl

/-- Block decomposition is a contraction for the finite sup norm. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiBlockDecomposeMap_le_one
    (blockOf : ι → β) :
    ‖(continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
      (W := W) blockOf :
      (∀ i, W i) →L[ℝ]
        (∀ b, ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
          W i.1))‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound
    (continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
      (W := W) blockOf)
    zero_le_one
    (fun x => by
      simp only [one_mul]
      rw [pi_norm_le_iff_of_nonneg
        (x := continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
          (W := W) blockOf x) (r := ‖x‖) (norm_nonneg x)]
      intro b
      rw [pi_norm_le_iff_of_nonneg
        (x := continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
          (W := W) blockOf x b) (r := ‖x‖) (norm_nonneg x)]
      intro i
      simpa using
        ((pi_norm_le_iff_of_nonneg (x := x) (r := ‖x‖)
          (norm_nonneg x)).1 le_rfl i.1))

/-- Block reassembly is also a contraction for the finite sup norm. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiBlockAssembleMap_le_one
    (blockOf : ι → β) :
    ‖(continuousLinearMapJointRemainderDependentPiBlockAssembleMap
      (W := W) blockOf :
      (∀ b, ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
        W i.1) →L[ℝ] (∀ i, W i))‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound
    (continuousLinearMapJointRemainderDependentPiBlockAssembleMap
      (W := W) blockOf)
    zero_le_one
    (fun x => by
      simp only [one_mul]
      rw [pi_norm_le_iff_of_nonneg
        (x := continuousLinearMapJointRemainderDependentPiBlockAssembleMap
          (W := W) blockOf x) (r := ‖x‖) (norm_nonneg x)]
      intro i
      have hinner :
          ‖x (blockOf i)
              (⟨i, rfl⟩ : continuousLinearMapJointRemainderDependentPiBlockFiber
                blockOf (blockOf i))‖ ≤ ‖x (blockOf i)‖ := by
        exact (pi_norm_le_iff_of_nonneg
          (x := x (blockOf i)) (r := ‖x (blockOf i)‖)
          (norm_nonneg (x (blockOf i)))).1 le_rfl ⟨i, rfl⟩
      have houter : ‖x (blockOf i)‖ ≤ ‖x‖ := by
        exact (pi_norm_le_iff_of_nonneg
          (x := x) (r := ‖x‖) (norm_nonneg x)).1 le_rfl (blockOf i)
      simpa using hinner.trans houter)

@[simp] theorem continuousLinearMapJointRemainderDependentPiBlockAssembleDecompose_apply
    (blockOf : ι → β) (x : ∀ i, W i) (i : ι) :
    continuousLinearMapJointRemainderDependentPiBlockAssembleMap
      (W := W) blockOf
      (continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
        (W := W) blockOf x) i = x i := by
  rfl

@[simp] theorem continuousLinearMapJointRemainderDependentPiBlockDecomposeAssemble_apply
    (blockOf : ι → β)
    (x : ∀ b, ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
      W i.1) (b : β)
    (i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b) :
    continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
      (W := W) blockOf
      (continuousLinearMapJointRemainderDependentPiBlockAssembleMap
        (W := W) blockOf x) b i = x b i := by
  rcases i with ⟨i, hi⟩
  subst b
  rfl

/-- Reassembly after decomposition is the identity continuous linear map. -/
theorem continuousLinearMapJointRemainderDependentPiBlockAssemble_comp_decompose
    (blockOf : ι → β) :
    (continuousLinearMapJointRemainderDependentPiBlockAssembleMap
      (W := W) blockOf).comp
      (continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
        (W := W) blockOf) =
      ContinuousLinearMap.id ℝ (∀ i, W i) := by
  ext x i
  rfl

/-- Decomposition after reassembly is the identity continuous linear map. -/
theorem continuousLinearMapJointRemainderDependentPiBlockDecompose_comp_assemble
    (blockOf : ι → β) :
    (continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
      (W := W) blockOf).comp
      (continuousLinearMapJointRemainderDependentPiBlockAssembleMap
        (W := W) blockOf) =
      ContinuousLinearMap.id ℝ
        (∀ b, ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
          W i.1) := by
  ext x b i
  exact continuousLinearMapJointRemainderDependentPiBlockDecomposeAssemble_apply
    (W := W) blockOf x b i

/-- The observable consisting of one dependent Pi-product block. -/
noncomputable def continuousLinearMapJointRemainderDependentPiBlockObservable
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) (b : β) :
    (V →L[ℝ] V) →L[ℝ]
      (∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
        W i.1) :=
  continuousLinearMapJointRemainderDependentPiProductObservable
    (fun i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b =>
      φ i.1)

@[simp] theorem continuousLinearMapJointRemainderDependentPiBlockObservable_apply
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) (b : β) (A : V →L[ℝ] V)
    (i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b) :
    continuousLinearMapJointRemainderDependentPiBlockObservable
      φ blockOf b A i = φ i.1 A := by
  rfl

/-- The nested Pi-product observable of all blocks. -/
noncomputable def continuousLinearMapJointRemainderDependentPiBlockBundleObservable
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) :
    (V →L[ℝ] V) →L[ℝ]
      (∀ b, ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
        W i.1) :=
  continuousLinearMapJointRemainderDependentPiProductObservable
    (fun b => continuousLinearMapJointRemainderDependentPiBlockObservable
      φ blockOf b)

@[simp] theorem continuousLinearMapJointRemainderDependentPiBlockBundleObservable_apply
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) (A : V →L[ℝ] V) (b : β)
    (i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b) :
    continuousLinearMapJointRemainderDependentPiBlockBundleObservable
      φ blockOf A b i = φ i.1 A := by
  rfl

/-- Block bundling is exactly postcomposition by the decomposition map. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiBlockDecomposeMap_comp_observable
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) :
    (continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
      (W := W) blockOf).comp
      (continuousLinearMapJointRemainderDependentPiProductObservable φ) =
      continuousLinearMapJointRemainderDependentPiBlockBundleObservable
        φ blockOf := by
  ext A b i
  rfl

/-- Reassembly of the block bundle recovers the full dependent Pi-product
observable exactly. -/
@[simp] theorem continuousLinearMapJointRemainderDependentPiBlockAssembleMap_comp_bundle
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) :
    (continuousLinearMapJointRemainderDependentPiBlockAssembleMap
      (W := W) blockOf).comp
      (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
        φ blockOf) =
      continuousLinearMapJointRemainderDependentPiProductObservable φ := by
  ext A i
  rfl

/-- One outer coordinate projection recovers the corresponding block
observable. -/
@[simp] theorem continuousLinearMapJointRemainder_proj_comp_dependentPiBlockBundleObservable
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) (b : β) :
    (ContinuousLinearMap.proj b :
      (∀ c, ∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf c,
        W i.1) →L[ℝ]
      (∀ i : continuousLinearMapJointRemainderDependentPiBlockFiber blockOf b,
        W i.1)).comp
      (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
        φ blockOf) =
      continuousLinearMapJointRemainderDependentPiBlockObservable
        φ blockOf b := by
  ext A i
  rfl

/-- Block bundling preserves the observable operator norm exactly. -/
theorem continuousLinearMapJointRemainder_norm_dependentPiBlockBundleObservable_eq
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) :
    ‖continuousLinearMapJointRemainderDependentPiBlockBundleObservable
        φ blockOf‖ =
      ‖continuousLinearMapJointRemainderDependentPiProductObservable φ‖ := by
  let d := continuousLinearMapJointRemainderDependentPiBlockDecomposeMap
    (W := W) blockOf
  let a := continuousLinearMapJointRemainderDependentPiBlockAssembleMap
    (W := W) blockOf
  let f := continuousLinearMapJointRemainderDependentPiProductObservable φ
  let g := continuousLinearMapJointRemainderDependentPiBlockBundleObservable
    φ blockOf
  have hd : d.comp f = g := by
    simpa [d, f, g] using
      (continuousLinearMapJointRemainderDependentPiBlockDecomposeMap_comp_observable
        (W := W) φ blockOf)
  have ha : a.comp g = f := by
    simpa [a, f, g] using
      (continuousLinearMapJointRemainderDependentPiBlockAssembleMap_comp_bundle
        (W := W) φ blockOf)
  apply le_antisymm
  · rw [← hd]
    calc
      ‖d.comp f‖ ≤ ‖d‖ * ‖f‖ := d.opNorm_comp_le f
      _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
        (by simpa [d] using
          (continuousLinearMapJointRemainder_norm_dependentPiBlockDecomposeMap_le_one
            (W := W) blockOf)) (norm_nonneg f)
      _ = ‖f‖ := by rw [one_mul]
  · rw [← ha]
    calc
      ‖a.comp g‖ ≤ ‖a‖ * ‖g‖ := a.opNorm_comp_le g
      _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right
        (by simpa [a] using
          (continuousLinearMapJointRemainder_norm_dependentPiBlockAssembleMap_le_one
            (W := W) blockOf)) (norm_nonneg g)
      _ = ‖g‖ := by rw [one_mul]

/-- Therefore the block bundle and full product have the same response safe
order at every common tolerance. -/
theorem continuousLinearMapJointRemainderResponseSafeOrder_dependentPiBlockBundle_eq
    (φ : ∀ i, (V →L[ℝ] V) →L[ℝ] W i)
    (blockOf : ι → β) (q M epsilon : ℝ) :
    continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiBlockBundleObservable
          φ blockOf) q M epsilon =
      continuousLinearMapJointRemainderResponseSafeOrder
        (continuousLinearMapJointRemainderDependentPiProductObservable φ)
        q M epsilon := by
  unfold continuousLinearMapJointRemainderResponseSafeOrder
  rw [continuousLinearMapJointRemainder_norm_dependentPiBlockBundleObservable_eq]

end MathlibAnalytic
end MGAP4D