import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedCompleteOrderLossContraction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedRelativePoincare
import Mathlib.Tactic

/-!
# Constant-line convergence for any complete two-sided tagged-link order

PR #4976 proves the strict two-boundary path-loss contraction for every
duplicate-free tagged-link order containing every genuine right/left spatial
link.  This file transports the #4970--#4971 constant-line geometry from the
canonical `Finset.univ.toList` order to that complete-order setting.

No permutation of noncommuting projections is used.  The supplied list is
kept literally throughout.

For every complete duplicate-free order we prove:

* its sweep fixed space is exactly the intrinsic joint constant line;
* the intrinsic constant projection absorbs the sweep;
* iterated path loss decays with the existing two-boundary loss ratio;
* the iterates converge strongly to the intrinsic constant projection;
* exact constant-centered Pythagoras;
* the first path loss controls constant-centered variance;
* hence one full sweep contracts constant-centered squared norm by the same
  volume/rank-independent two-boundary loss ratio.

This is the full-sweep input needed for the G1 twelve-color grouped frame.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance twoSidedCompleteOrderConstantSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoSidedCompleteOrderConstantSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance twoSidedCompleteOrderConstantSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoSidedCompleteOrderConstantSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoSidedCompleteOrderConstantSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance twoSidedCompleteOrderConstantSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance twoSidedCompleteOrderConstantLineHasOrthogonalProjection
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta).HasOrthogonalProjection := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  change C.HasOrthogonalProjection
  letI : FiniteDimensional ℝ C := by
    unfold C
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    infer_instance
  letI : CompleteSpace C := FiniteDimensional.complete ℝ C
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace C

/-- Any complete tagged-link order has exactly the intrinsic constant line as
its sweep fixed space.  No order equality with the canonical enumeration is
asserted or needed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCompleteOrder_fixed_iff_mem_constantLine
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hComplete :
      ∀ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        e ∈ sources)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        sources z = z ↔
      z ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
          H N hN beta hbeta := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  change realHilbertProjectionSweep P sources z = z ↔ _
  rw [
    realHilbertProjectionSweep_apply_eq_self_iff_forall_mem_fixed
      P
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta)
      sources z]
  have hAll :
      (∀ e ∈ sources, P e z = z) ↔
        ∀ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
          P e z = z := by
    constructor
    · intro h e
      exact h e (hComplete e)
    · intro h e _
      exact h e
  rw [hAll]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_all_fixed_iff_mem_constantLine
      H N hN beta hbeta z

/-- The intrinsic constant projection absorbs a sweep along any supplied
two-sided tagged-link list. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedSpatialLinkOrder
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
        (realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
            H N hN beta hbeta)
          sources z) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta z := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  change B (realHilbertProjectionSweep P sources z) = B z
  exact
    realHilbertNestedBlock_projectionSweep_absorb
      B P sources
      (fun e _ y =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedSpatialLink
          H N hN beta hbeta e y)
      z

/-- Geometric path-loss decay for any complete duplicate-free supplied order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_iteratedPathLoss_le_geometric_of_completeOrder
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hNodup : sources.Nodup)
    (hComplete :
      ∀ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        e ∈ sources)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (n : ℕ) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let S := realHilbertProjectionSweep P sources
    realHilbertProjectionSweepPathLoss P sources (S^[n] f) ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta ^ n *
        realHilbertProjectionSweepPathLoss P sources f := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let S := realHilbertProjectionSweep P sources
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  induction n generalizing f with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      calc
        realHilbertProjectionSweepPathLoss P sources (S^[n] (S f)) ≤
            eta ^ n *
              realHilbertProjectionSweepPathLoss P sources (S f) :=
          ih (S f)
        _ ≤ eta ^ n *
            (eta * realHilbertProjectionSweepPathLoss P sources f) :=
          mul_le_mul_of_nonneg_left
            (by
              simpa [P, S, eta] using
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul_of_completeOrder_allL2
                  H N hN s hs beta hbeta hcut
                  sources hNodup hComplete f)
            (pow_nonneg
              (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio_nonneg
                s beta)
              n)
        _ = eta ^ (n + 1) *
            realHilbertProjectionSweepPathLoss P sources f := by
          rw [pow_succ]
          ring

/-- Any complete duplicate-free tagged-link sweep converges strongly to the
intrinsic constant projection on the whole genuine joint L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_iterates_tendsto_constantProjection_of_completeOrder
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hNodup : sources.Nodup)
    (hComplete :
      ∀ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        e ∈ sources)
    (z :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let S := realHilbertProjectionSweep P sources
    let B :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
    Tendsto (fun n : ℕ => S^[n] z) atTop (𝓝 (B z)) := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let S := realHilbertProjectionSweep P sources
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  have hEta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio_nonneg_lt_one
      s hs beta hbeta hcut
  have hAbsorb : ∀ y, B (S y) = B y := by
    intro y
    simpa [P, S, B] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedSpatialLinkOrder
        H N hN beta hbeta sources y
  have hFixed : ∀ y, S y = y → B y = y := by
    intro y hy
    let C :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
        H N hN beta hbeta
    change C.starProjection y = y
    apply (Submodule.starProjection_eq_self_iff).2
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCompleteOrder_fixed_iff_mem_constantLine
        H N hN beta hbeta sources hComplete y).1
        (by simpa [P, S] using hy)
  have hDecay : ∀ n : ℕ,
      realHilbertProjectionSweepPathLoss P sources (S^[n] z) ≤
        eta ^ n * realHilbertProjectionSweepPathLoss P sources z := by
    intro n
    simpa [P, S, eta] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_iteratedPathLoss_le_geometric_of_completeOrder
        H N hN s hs beta hbeta hcut
        sources hNodup hComplete z n
  exact
    realHilbertProjectionSweep_tendsto_block_of_geometric_pathLoss
      P sources B eta hEta.1 hEta.2
      hAbsorb hFixed z hDecay

/-- Exact constant-centered Pythagoras for any supplied two-sided tagged-link
order. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_constantProjection_pythagoras_forOrder
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let B :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
    let S := realHilbertProjectionSweep P sources
    ‖f - B f‖ ^ 2 =
      realHilbertProjectionSweepPathLoss P sources f +
        ‖S f - B (S f)‖ ^ 2 := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  let S := realHilbertProjectionSweep P sources
  have hBid : B.comp B = B := by
    apply ContinuousLinearMap.ext
    intro x
    change C.starProjection (C.starProjection x) = C.starProjection x
    exact
      Submodule.starProjection_eq_self_iff.mpr
        (C.starProjection_apply_mem x)
  have hBsymm :
      ∀ x y, inner ℝ (B x) y = inner ℝ x (B y) := by
    intro x y
    exact Submodule.inner_starProjection_left_eq_right C x y
  have hFirst :=
    realHilbertProjection_residual_norm_sq B hBid hBsymm f
  have hSecond :=
    realHilbertProjection_residual_norm_sq B hBid hBsymm (S f)
  have hAbsorb :
      B (S f) = B f := by
    simpa [P, B, S] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedSpatialLinkOrder
        H N hN beta hbeta sources f
  rw [hAbsorb] at hSecond
  have hLoss :=
    realHilbertProjectionSweep_norm_sq_loss
      P
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta)
      sources f
  change ‖f - B f‖ ^ 2 =
    realHilbertProjectionSweepPathLoss P sources f +
      ‖S f - B (S f)‖ ^ 2
  rw [hAbsorb]
  nlinarith

/-- For any complete duplicate-free order, its first path loss controls the
whole constant-centered variance with coefficient `1 - eta`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_ge_one_sub_lossRatio_mul_constantVariance_of_completeOrder
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hNodup : sources.Nodup)
    (hComplete :
      ∀ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        e ∈ sources)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let B :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
    (1 - GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta) *
        ‖f - B f‖ ^ 2 ≤
      realHilbertProjectionSweepPathLoss P sources f := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let S :=
    realHilbertProjectionSweep P sources
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  let D : ℕ → ℝ :=
    fun n => ‖S^[n] f - B (S^[n] f)‖ ^ 2
  let losses : ℕ → ℝ :=
    fun n =>
      realHilbertProjectionSweepPathLoss P sources (S^[n] f)
  have hLimit :
      Tendsto (fun n : ℕ => S^[n] f) atTop (𝓝 (B f)) := by
    simpa [P, S, B] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_iterates_tendsto_constantProjection_of_completeOrder
        H N hN s hs beta hbeta hcut
        sources hNodup hComplete f
  have hIdem : B (B f) = B f := by
    let C :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
        H N hN beta hbeta
    change C.starProjection (C.starProjection f) = C.starProjection f
    exact
      Submodule.starProjection_eq_self_iff.mpr
        (C.starProjection_apply_mem f)
  have hTail : Tendsto D atTop (𝓝 0) := by
    have hDiff :=
      hLimit.sub (((B).continuous.tendsto (B f)).comp hLimit)
    simpa only [
      D, hIdem, sub_self, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      hDiff.norm.pow 2
  have hRenew : ∀ n : ℕ, D n = losses n + D (n + 1) := by
    intro n
    simpa only [
      D, losses, Function.iterate_succ_apply'] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_constantProjection_pythagoras_forOrder
        H N hN beta hbeta sources (S^[n] f)
  have hLoss :
      ∀ n : ℕ, losses (n + 1) ≤ eta * losses n := by
    intro n
    dsimp only [losses]
    rw [Function.iterate_succ_apply']
    simpa [P, S, eta] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul_of_completeOrder_allL2
        H N hN s hs beta hbeta hcut
        sources hNodup hComplete (S^[n] f)
  simpa only [
    D, losses, eta, Function.iterate_zero, id_eq] using
    RenewalTail.current_loss_controls_energy_of_tendsto_zero
      D losses eta hRenew hLoss hTail

/-- A complete duplicate-free supplied sweep contracts the squared distance to
the intrinsic constant line by the same two-boundary loss ratio. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_constantVariance_le_lossRatio_mul_of_completeOrder
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (sources : List (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H))
    (hNodup : sources.Nodup)
    (hComplete :
      ∀ e : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
        e ∈ sources)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let B :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
        H N hN beta hbeta
    let S := realHilbertProjectionSweep P sources
    ‖S f - B (S f)‖ ^ 2 ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta *
        ‖f - B f‖ ^ 2 := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
      H N hN beta hbeta
  let S := realHilbertProjectionSweep P sources
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  have hSplit :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_constantProjection_pythagoras_forOrder
      H N hN beta hbeta sources f
  have hLower :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_ge_one_sub_lossRatio_mul_constantVariance_of_completeOrder
      H N hN s hs beta hbeta hcut sources hNodup hComplete f
  change ‖S f - B (S f)‖ ^ 2 ≤ eta * ‖f - B f‖ ^ 2
  change
    ‖f - B f‖ ^ 2 =
      realHilbertProjectionSweepPathLoss P sources f +
        ‖S f - B (S f)‖ ^ 2 at hSplit
  change
    (1 - eta) * ‖f - B f‖ ^ 2 ≤
      realHilbertProjectionSweepPathLoss P sources f at hLower
  nlinarith

end

end MathlibAnalytic
end MGAP4D
