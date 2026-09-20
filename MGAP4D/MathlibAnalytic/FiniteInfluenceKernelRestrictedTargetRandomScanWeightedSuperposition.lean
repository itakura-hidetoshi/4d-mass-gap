import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelRestrictedTargetRandomScanSuperposition
import Mathlib.Tactic

/-!
# Weighted superposition for restricted-target random-scan variation

The existing restricted-target random-scan carrier is exactly linear in its
initial variation profile.  The repository already records finite additive
superposition.  For exponentially weighted remote-target arguments we also
need scalar multiplication, so that a target-dependent spatial weight can be
moved from the outer finite sum into the initial variation profile.

This file proves:

* one target update commutes with multiplication by an arbitrary real scalar;
* one restricted random-scan update does the same;
* every finite iterate does the same;
* consequently, finite weighted superpositions commute exactly with every
  restricted random-scan iterate.

These are purely algebraic identities.  No positivity, contraction, geometry,
probability, or mass-gap assumption is added.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- One influence-kernel target update is homogeneous in the variation
profile. -/
theorem finiteInfluenceKernelUpdatedVariation_const_mul
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (a : ℝ)
    (variation : ι → ℝ)
    (updateTarget source : ι) :
    finiteInfluenceKernelUpdatedVariation
        K (fun e => a * variation e) updateTarget source =
      a * finiteInfluenceKernelUpdatedVariation
        K variation updateTarget source := by
  by_cases hEq : source = updateTarget
  · simp [finiteInfluenceKernelUpdatedVariation, hEq]
  · simp only [finiteInfluenceKernelUpdatedVariation, hEq, if_false]
    ring

/-- One restricted-target random-scan update is homogeneous in the variation
profile. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_const_mul
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (a : ℝ)
    (variation : ι → ℝ)
    (source : ι) :
    finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
        K target (fun e => a * variation e) source =
      a *
        finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
          K target variation source := by
  unfold finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
  simp_rw [finiteInfluenceKernelUpdatedVariation_const_mul]
  rw [← Finset.mul_sum]
  ring

/-- Every restricted-target random-scan iterate is homogeneous in the initial
variation profile. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_const_mul
    {ι τ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (a : ℝ)
    (variation : ι → ℝ)
    (n : ℕ)
    (source : ι) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target (fun e => a * variation e) n source =
      a *
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
          K target variation n source := by
  induction n generalizing source with
  | zero =>
      rfl
  | succ n ih =>
      simp only [
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_succ]
      calc
        finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
            K target
            (finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
              K target (fun e => a * variation e) n)
            source =
          finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
            K target
            (fun e =>
              a *
                finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                  K target variation n e)
            source := by
              apply congrArg
                (fun profile : ι → ℝ =>
                  finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
                    K target profile source)
              funext e
              exact ih e
        _ =
          a *
            finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation
              K target
              (finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
                K target variation n)
              source :=
          finiteInfluenceKernelRestrictedTargetRandomScanUpdatedVariation_const_mul
            K target a
            (finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
              K target variation n)
            source

/-- Finite weighted superpositions commute exactly with every restricted-target
random-scan iterate.  The weights are arbitrary real scalars. -/
theorem finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_weighted_finset_sum
    {ι τ κ : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype τ]
    [DecidableEq κ]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (target : τ → ι)
    (indices : Finset κ)
    (weight : κ → ℝ)
    (family : κ → ι → ℝ)
    (n : ℕ)
    (source : ι) :
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target
        (fun e => ∑ k ∈ indices, weight k * family k e)
        n source =
      ∑ k ∈ indices,
        weight k *
          finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
            K target (family k) n source := by
  calc
    finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
        K target
        (fun e => ∑ k ∈ indices, weight k * family k e)
        n source =
      ∑ k ∈ indices,
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
          K target (fun e => weight k * family k e) n source := by
            exact
              finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_finset_sum
                K target indices
                (fun k e => weight k * family k e)
                n source
    _ =
      ∑ k ∈ indices,
        weight k *
          finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate
            K target (family k) n source := by
      apply Finset.sum_congr rfl
      intro k _hk
      exact
        finiteInfluenceKernelRestrictedTargetRandomScanVariationIterate_const_mul
          K target (weight k) (family k) n source

end

end MathlibAnalytic
end MGAP4D
