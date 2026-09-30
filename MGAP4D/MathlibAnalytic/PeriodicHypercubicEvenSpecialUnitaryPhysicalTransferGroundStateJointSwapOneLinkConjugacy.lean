import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSwapSymmetry
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# Endpoint swap conjugates the two genuine one-link conditional expectations

PR #4950 proves that the genuine physical ground-state joint measure is
preserved by exchanging the left and right boundary configurations.  This file
lifts that exact symmetry to the joint real L2 space.

The endpoint-swap pullback is an involutive linear isometry.  It sends the
right one-link retained subspace exactly onto the corresponding left one-link
retained subspace.  Orthogonal projection covariance then gives

  S (P_right,target f) = P_left,target (S f).

Thus the left one-link projection is not a second analytic construction for
subsequent estimates: it is exactly the swap-conjugate of the already-developed
right one-link projection.

No cross-boundary coefficient, variance estimate, recurrence, Poincare
constant, or transfer-gap statement is changed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance groundStateJointSwapOneLinkSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointSwapOneLinkSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointSwapOneLinkSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointSwapOneLinkSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointSwapOneLinkSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointSwapOneLinkSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Pulling the right one-link retained sigma-algebra back by endpoint swap
produces exactly the left one-link retained sigma-algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_comap_swap_eq_left
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    MeasurableSpace.comap Prod.swap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target) =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
        H N target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
  simp_rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
  rfl

/-- Conversely, pulling the left retained sigma-algebra back by endpoint swap
recovers the right retained sigma-algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace_comap_swap_eq_right
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    MeasurableSpace.comap Prod.swap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
          H N target) =
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N target := by
  unfold
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
  simp_rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
  rfl

/-- Pullback by endpoint swap on the genuine ground-state joint real L2 space. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2LinearIsometry
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ Prod.swap
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta)

/-- Endpoint swap is literally involutive on the joint L2 quotient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2LinearIsometry_involutive
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Function.Involutive
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2LinearIsometry
        H N hN beta hbeta) := by
  intro f
  let h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  change
    MeasureTheory.Lp.compMeasurePreserving Prod.swap h
        (MeasureTheory.Lp.compMeasurePreserving Prod.swap h f) = f
  rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply f h h]
  rw [Lp.ext_iff]
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving f (h.comp h)).trans
      (Filter.Eventually.of_forall fun z => by
        rcases z with ⟨left, right⟩
        rfl)

/-- The involutive swap isometry packaged as a linear isometric equivalence. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta ≃ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
  LinearIsometryEquiv.ofSurjective
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2LinearIsometry
      H N hN beta hbeta)
    (by
      intro f
      refine ⟨
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2LinearIsometry
          H N hN beta hbeta f, ?_⟩
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2LinearIsometry_involutive
          H N hN beta hbeta f)

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_apply_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f) = f := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2LinearIsometry_involutive
      H N hN beta hbeta f

/-- Swap sends right one-link measurable L2 vectors to the corresponding left
one-link measurable subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_leftSpatialLink_lpMeas_of_mem_right
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf : f ∈
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta f ∈
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
          H N target) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  let π :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let hs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  have hfMap :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target]
        (fun z => f z) (Measure.map Prod.swap π) := by
    rw [hs.map_eq]
    exact hf
  have hcomp :=
    AEStronglyMeasurable.comp_ae_measurable'
      hfMap measurable_swap.aemeasurable
  rw [
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_comap_swap_eq_left
      H N target] at hcomp
  have hcoe :
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f z) =ᵐ[π]
        (fun z => f z.swap) := by
    change
      (MeasureTheory.Lp.compMeasurePreserving Prod.swap hs f) =ᵐ[π]
        (fun z => f z.swap)
    simpa [Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving f hs)
  exact (by
    simpa [Function.comp_def] using hcomp).congr hcoe.symm

/-- Swap sends left one-link measurable L2 vectors back to the corresponding
right one-link measurable subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_rightSpatialLink_lpMeas_of_mem_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf : f ∈
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
          H N target) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta f ∈
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  let π :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let hs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
      H N hN beta hbeta
  have hfMap :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
          H N target]
        (fun z => f z) (Measure.map Prod.swap π) := by
    rw [hs.map_eq]
    exact hf
  have hcomp :=
    AEStronglyMeasurable.comp_ae_measurable'
      hfMap measurable_swap.aemeasurable
  rw [
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace_comap_swap_eq_right
      H N target] at hcomp
  have hcoe :
      (fun z =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f z) =ᵐ[π]
        (fun z => f z.swap) := by
    change
      (MeasureTheory.Lp.compMeasurePreserving Prod.swap hs f) =ᵐ[π]
        (fun z => f z.swap)
    simpa [Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving f hs)
  exact (by
    simpa [Function.comp_def] using hcomp).congr hcoe.symm

/-- The right one-link measurable Hilbert subspace is carried exactly onto the
left one-link measurable Hilbert subspace by endpoint swap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointRightSpatialLinkLpMeas_map_swap_eq_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
          H N target) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)).map
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta).toLinearEquiv =
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
          H N target) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_leftSpatialLink_lpMeas_of_mem_right
        H N hN beta hbeta target x hx
  · intro y hy
    refine ⟨
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta y,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_mem_rightSpatialLink_lpMeas_of_mem_left
        H N hN beta hbeta target y hy, ?_⟩
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_apply_apply
        H N hN beta hbeta y

/-- Orthogonal projection covariance under endpoint swap. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLink_starProjection
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        ((lpMeas ℝ ℝ
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
              H N target) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
              H N hN beta hbeta)).starProjection f) =
      (lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
            H N target) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta)).starProjection
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f) := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  let R :=
    lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N target) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
  have h :=
    Submodule.starProjection_map_apply E R (E f)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointRightSpatialLinkLpMeas_map_swap_eq_left
      H N hN beta hbeta target] at h
  simpa [E, R] using h.symm

/-- The genuine left one-link conditional expectation is exactly the
swap-conjugate of the genuine right one-link conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLinkCondExpL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
        H N hN beta hbeta target
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_apply]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        ((lpMeas ℝ ℝ
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
              H N target) 2
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
              H N hN beta hbeta)).starProjection f) =
      (lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialLinkMeasurableSpace
            H N target) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta)).starProjection
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f)
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLink_starProjection
      H N hN beta hbeta target f

/-- Equivalent conjugation formula with the left projection isolated. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2_eq_swap_right_swap
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
        H N hN beta hbeta target f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
            H N hN beta hbeta f)) := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLinkCondExpL2
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
        H N hN beta hbeta f)
  simpa using h.symm

/-- Endpoint swap preserves the one-link residual norm while exchanging the
right and left one-link projections. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightResidual_norm_eq_left
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
          H N hN beta hbeta f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
            H N hN beta hbeta f)‖ =
      ‖f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target f‖ := by
  let E :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv
      H N hN beta hbeta
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target
  calc
    ‖E f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialLinkCondExpL2
          H N hN beta hbeta target (E f)‖ =
        ‖E (f - P f)‖ := by
          rw [E.map_sub]
          rw [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSwapL2Equiv_rightSpatialLinkCondExpL2
              H N hN beta hbeta target f]
    _ = ‖f - P f‖ := E.norm_map (f - P f)
    _ = _ := rfl

end

end MathlibAnalytic
end MGAP4D
