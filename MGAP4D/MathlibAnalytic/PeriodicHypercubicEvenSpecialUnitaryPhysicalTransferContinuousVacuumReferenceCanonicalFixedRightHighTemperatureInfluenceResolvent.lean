import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureInfluence
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinIterateKernel
import MGAP4D.MathlibAnalytic.FinitePositiveWeightReciprocalInfluenceKernelResponse
import Mathlib.Tactic

/-!
# Canonical high-temperature physical influence iterates and finite resolvent

The preceding canonical high-temperature theorem gives the ORIGINAL pin-free
physical-left influence kernel a strict exponentially weighted COLUMN bound

  sum_target K(target,source) W(center,target) < q(s,beta) W(center,source),

with 0 <= q(s,beta) < 1 on the original closed cutoff interval.

This file keeps that target/source orientation and propagates the weighted
column estimate through the existing finite influence-iterate kernel.  No
transpose kernel and no row-sum reinterpretation are introduced.

For every finite depth d,

  sum_target K^d(target,source) W(center,target)
    <= q(s,beta)^d W(center,source).

Summing finite depths gives the corresponding finite Neumann resolvent bound,
and q < 1 bounds every finite prefix by (1-q)^(-1).  A single nonnegative
summand also gives the pointwise source-to-target iterate estimate.

These are finite-volume physical influence/path-resolvent estimates with
volume/rank-independent scalar q.  They are the bridge toward the existing
covariance telescope; no covariance clustering, random-scan coercivity,
Hamiltonian gap, thermodynamic limit, or continuum construction is asserted
here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000

local instance canonicalHighTemperatureInfluenceResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A nonnegative weighted column subinvariant propagates multiplicatively
through every finite influence iterate.  The orientation is column/source:
the target index is summed and the source index is fixed. -/
theorem finiteInfluenceIterateKernel_weightedColumn_le_pow
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (weight : α → ℝ)
    (hWeight : ∀ x : α, 0 ≤ weight x)
    (q : ℝ)
    (hq : 0 ≤ q)
    (hColumn :
      ∀ source : α,
        (∑ target : α, influence target source * weight target) ≤
          q * weight source)
    (d : ℕ)
    (source : α) :
    (∑ target : α,
        finiteInfluenceIterateKernel influence d target source *
          weight target) ≤
      q ^ d * weight source := by
  induction d generalizing source with
  | zero =>
      simp only [finiteInfluenceIterateKernel, pow_zero, one_mul]
      rw [Finset.sum_eq_single source]
      · simp
      · intro target _ hTarget
        simp [hTarget]
      · intro hSource
        exact False.elim (hSource (Finset.mem_univ source))
  | succ d ih =>
      change
        (∑ target : α,
          (∑ mid : α,
            influence target mid *
              finiteInfluenceIterateKernel influence d mid source) *
            weight target) ≤
          q ^ (d + 1) * weight source
      calc
        (∑ target : α,
          (∑ mid : α,
            influence target mid *
              finiteInfluenceIterateKernel influence d mid source) *
            weight target) =
          ∑ mid : α,
            finiteInfluenceIterateKernel influence d mid source *
              (∑ target : α, influence target mid * weight target) := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro mid _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro target _
            ring
        _ ≤
          ∑ mid : α,
            finiteInfluenceIterateKernel influence d mid source *
              (q * weight mid) := by
            apply Finset.sum_le_sum
            intro mid _
            exact
              mul_le_mul_of_nonneg_left
                (hColumn mid)
                (finiteInfluenceIterateKernel_nonneg
                  influence hInfluence d mid source)
        _ = q *
          (∑ mid : α,
            finiteInfluenceIterateKernel influence d mid source *
              weight mid) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro mid _
            ring
        _ ≤ q * (q ^ d * weight source) :=
          mul_le_mul_of_nonneg_left (ih source) hq
        _ = q ^ (d + 1) * weight source := by
          rw [pow_succ]
          ring

/-- Finite Neumann prefixes inherit the same weighted-column geometry. -/
theorem finiteInfluenceIterateKernel_weightedColumn_finiteResolvent_le
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (weight : α → ℝ)
    (hWeight : ∀ x : α, 0 ≤ weight x)
    (q : ℝ)
    (hq : 0 ≤ q)
    (hColumn :
      ∀ source : α,
        (∑ target : α, influence target source * weight target) ≤
          q * weight source)
    (d : ℕ)
    (source : α) :
    (Finset.range d).sum
        (fun k =>
          ∑ target : α,
            finiteInfluenceIterateKernel influence k target source *
              weight target) ≤
      finiteRealGeometricSeries q d * weight source := by
  calc
    (Finset.range d).sum
        (fun k =>
          ∑ target : α,
            finiteInfluenceIterateKernel influence k target source *
              weight target) ≤
      (Finset.range d).sum
        (fun k => q ^ k * weight source) := by
          apply Finset.sum_le_sum
          intro k hk
          exact
            finiteInfluenceIterateKernel_weightedColumn_le_pow
              influence hInfluence weight hWeight q hq hColumn k source
    _ = finiteRealGeometricSeries q d * weight source := by
      unfold finiteRealGeometricSeries
      rw [Finset.sum_mul]

/-- Under q < 1 every finite weighted-column resolvent prefix is bounded by
the infinite scalar geometric resolvent. -/
theorem finiteInfluenceIterateKernel_weightedColumn_finiteResolvent_le_inv_one_sub
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (weight : α → ℝ)
    (hWeight : ∀ x : α, 0 ≤ weight x)
    (q : ℝ)
    (hq : 0 ≤ q)
    (hqLtOne : q < 1)
    (hColumn :
      ∀ source : α,
        (∑ target : α, influence target source * weight target) ≤
          q * weight source)
    (d : ℕ)
    (source : α) :
    (Finset.range d).sum
        (fun k =>
          ∑ target : α,
            finiteInfluenceIterateKernel influence k target source *
              weight target) ≤
      (1 - q)⁻¹ * weight source := by
  exact
    (finiteInfluenceIterateKernel_weightedColumn_finiteResolvent_le
      influence hInfluence weight hWeight q hq hColumn d source).trans
      (mul_le_mul_of_nonneg_right
        (finiteRealGeometricSeries_le_inv_one_sub q hq hqLtOne d)
        (hWeight source))

/-- A single nonnegative entry inherits the reciprocal target-weight decay
from the full weighted iterate column. -/
theorem finiteInfluenceIterateKernel_entry_le_pow_mul_weight_div
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (weight : α → ℝ)
    (hWeight : ∀ x : α, 0 < weight x)
    (q : ℝ)
    (hq : 0 ≤ q)
    (hColumn :
      ∀ source : α,
        (∑ target : α, influence target source * weight target) ≤
          q * weight source)
    (d : ℕ)
    (target source : α) :
    finiteInfluenceIterateKernel influence d target source ≤
      (q ^ d * weight source) / weight target := by
  have hSingle :
      finiteInfluenceIterateKernel influence d target source *
          weight target ≤
        ∑ other : α,
          finiteInfluenceIterateKernel influence d other source *
            weight other := by
    exact
      Finset.single_le_sum
        (fun other _ =>
          mul_nonneg
            (finiteInfluenceIterateKernel_nonneg
              influence hInfluence d other source)
            (hWeight other).le)
        (Finset.mem_univ target)
  have hColumnD :=
    finiteInfluenceIterateKernel_weightedColumn_le_pow
      influence hInfluence weight (fun x => (hWeight x).le)
      q hq hColumn d source
  exact (le_div_iff₀ (hWeight target)).2 (hSingle.trans hColumnD)

/-- The ORIGINAL canonical pin-free physical-left kernel has exponentially
weighted finite iterate columns bounded by powers of the existing elementary
high-temperature envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influenceIterate_exponentialWeightedColumn_le_pow_halfBarrierCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (d : ℕ) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      finiteInfluenceIterateKernel
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence
        d target source *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center target) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta ^ d *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  let hR : ∀ target source, 0 ≤ R target source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
      H N hN beta hbeta
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta R hR
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s beta
  have hW : ∀ x, 0 ≤ W x := by
    intro x
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s (zero_lt_one.trans_le hs).le center x
  have hq :
      0 ≤ q :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      s beta hbeta hcut).1
  have hColumn :
      ∀ y,
        (∑ x, K.influence x y * W x) ≤ q * W y := by
    intro y
    exact le_of_lt
      (by
        simpa only [K, R, hR, W, q] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_exponentialWeightedColumn_lt_halfBarrierCoefficient
            H N hN s hs beta hbeta hcut center y)
  simpa only [K, R, hR, W, q] using
    finiteInfluenceIterateKernel_weightedColumn_le_pow
      K.influence K.influence_nonneg W hW q hq hColumn d source

/-- Every finite Neumann prefix of the ORIGINAL canonical physical influence
kernel is bounded by the volume/rank-independent scalar resolvent (1-q)^(-1)
times the original source weight. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influenceFiniteResolvent_exponentialWeightedColumn_le_inv_gap
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H)
    (d : ℕ) :
    (Finset.range d).sum
      (fun k =>
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceIterateKernel
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
              H beta hbeta
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                H N hN beta hbeta)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                H N hN beta hbeta)).influence
            k target source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s center target) ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  let hR : ∀ target source, 0 ≤ R target source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
      H N hN beta hbeta
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta R hR
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s beta
  have hW : ∀ x, 0 ≤ W x := by
    intro x
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s (zero_lt_one.trans_le hs).le center x
  have hqPair :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      s beta hbeta hcut
  have hColumn :
      ∀ y,
        (∑ x, K.influence x y * W x) ≤ q * W y := by
    intro y
    exact le_of_lt
      (by
        simpa only [K, R, hR, W, q] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_exponentialWeightedColumn_lt_halfBarrierCoefficient
            H N hN s hs beta hbeta hcut center y)
  simpa only [K, R, hR, W, q] using
    finiteInfluenceIterateKernel_weightedColumn_finiteResolvent_le_inv_one_sub
      K.influence K.influence_nonneg W hW q hqPair.1 hqPair.2
      hColumn d source

/-- Pointwise finite influence paths inherit the reciprocal exponential weight.
For s > 1 this is a base-L1 spatial decay statement for every fixed path depth;
at s = 1 it is only a uniform path bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influenceIterate_le_pow_halfBarrierCoefficient_mul_sourceWeight_div_targetWeight
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s)
    (center target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (d : ℕ) :
    finiteInfluenceIterateKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence
      d target source ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta ^ d *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center target := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  let hR : ∀ target source, 0 ≤ R target source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
      H N hN beta hbeta
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta R hR
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s beta
  have hW : ∀ x, 0 < W x := by
    intro x
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
        H s (zero_lt_one.trans_le hs) center x
  have hq :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      s beta hbeta hcut).1
  have hColumn :
      ∀ y,
        (∑ x, K.influence x y * W x) ≤ q * W y := by
    intro y
    exact le_of_lt
      (by
        simpa only [K, R, hR, W, q] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_exponentialWeightedColumn_lt_halfBarrierCoefficient
            H N hN s hs beta hbeta hcut center y)
  simpa only [K, R, hR, W, q] using
    finiteInfluenceIterateKernel_entry_le_pow_mul_weight_div
      K.influence K.influence_nonneg W hW q hq hColumn d target source

end

end MathlibAnalytic
end MGAP4D
