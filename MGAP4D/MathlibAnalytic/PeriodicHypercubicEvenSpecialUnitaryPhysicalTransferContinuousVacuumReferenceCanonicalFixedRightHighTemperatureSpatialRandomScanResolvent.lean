import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureCovarianceResolvent
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureInfluenceResolvent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Canonical high-temperature spatial random-scan resolvent

The canonical high-temperature lane now has two complementary ingredients:

* the ORIGINAL physical influence kernel has exponentially weighted finite
  path columns and a finite Neumann resolvent (#4639);
* the actual restricted random-scan covariance telescope has a canonical
  normalized finite resolvent profile (#4641).

This file connects them without assuming any monotonicity of the
Classical.choose high-temperature cutoffs at different weight scales.

For one fixed scale s >= 1 and one coupling in that scale's original cutoff,
let q(s,beta) be the existing half-barrier coefficient.  The actual physical
weighted coefficient c is strictly below q < 1.  Therefore the canonical
random-scan finite resolvent itself obeys the growing-weight estimate

  w_M(x) <= (1-q)^(-1) B W_center(x).

The same finite resolvent is a transpose-subinvariant profile for the ORIGINAL
physical influence kernel.  Unrolling that subinvariance with the existing
recursive influence kernel and using the #4639 source-centered pointwise path
bound gives, whenever every nonzero initial variation coordinate is at
base-L1 distance at least D from a source,

  w_M(source)
    <= (1-q)^(-1) s^(-D) * sum_x variation(x).

The residual finite-path term is killed using the same q(s,beta): the growing
weighted bound on w_M and the weighted path-column estimate give a q^d
envelope, which tends to zero.

At s > 1 this is genuine exponential spatial decay of the finite random-scan
resolvent.  At s = 1 it remains a uniform resolvent estimate.  No covariance
telescope, Poincare/coercivity theorem, Hamiltonian gap, or continuum
construction is asserted in this file.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

local instance canonicalHighTemperatureSpatialRandomScanResolventSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One residual step for a transpose-subinvariant profile, using only the
lightweight column iterate already introduced in the canonical high-temperature
lane.  Keeping this algebra local avoids importing the older broad compact-
Dobrushin iterate spine and its unrelated global instance graph. -/
theorem finiteInfluenceColumnIterateKernel_weighted_subinvariant_step
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (v w : α → ℝ)
    (hSub : ∀ source : α,
      w source ≤ v source + ∑ target : α, influence target source * w target)
    (d : ℕ)
    (source : α) :
    (∑ initial : α,
        finiteInfluenceColumnIterateKernel influence d initial source * w initial) ≤
      (∑ initial : α,
        finiteInfluenceColumnIterateKernel influence d initial source * v initial) +
      ∑ initial : α,
        finiteInfluenceColumnIterateKernel influence (d + 1) initial source * w initial := by
  calc
    (∑ initial : α,
        finiteInfluenceColumnIterateKernel influence d initial source * w initial) ≤
      ∑ initial : α,
        finiteInfluenceColumnIterateKernel influence d initial source *
          (v initial + ∑ target : α, influence target initial * w target) := by
      apply Finset.sum_le_sum
      intro initial _
      exact
        mul_le_mul_of_nonneg_left
          (hSub initial)
          (finiteInfluenceColumnIterateKernel_nonneg
            influence hInfluence d initial source)
    _ =
      (∑ initial : α,
          finiteInfluenceColumnIterateKernel influence d initial source * v initial) +
        ∑ initial : α,
          finiteInfluenceColumnIterateKernel influence d initial source *
            (∑ target : α, influence target initial * w target) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ =
      (∑ initial : α,
          finiteInfluenceColumnIterateKernel influence d initial source * v initial) +
        ∑ target : α,
          finiteInfluenceColumnIterateKernel influence (d + 1) target source * w target := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro target _
      calc
        (∑ initial : α,
            finiteInfluenceColumnIterateKernel influence d initial source *
              (influence target initial * w target)) =
          ∑ initial : α,
            (influence target initial *
              finiteInfluenceColumnIterateKernel influence d initial source) * w target := by
            apply Finset.sum_congr rfl
            intro initial _
            ring
        _ =
          (∑ initial : α,
              influence target initial *
                finiteInfluenceColumnIterateKernel influence d initial source) * w target := by
            rw [Finset.sum_mul]
        _ =
          finiteInfluenceColumnIterateKernel influence (d + 1) target source * w target := by
            rfl

/-- Finite Neumann comparison for a transpose-subinvariant profile, stated
directly with the canonical high-temperature column iterate. -/
theorem finiteInfluenceColumnIterateKernel_subinvariant_le_partial_resolvent_add_residual
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (v w : α → ℝ)
    (hSub : ∀ source : α,
      w source ≤ v source + ∑ target : α, influence target source * w target)
    (d : ℕ)
    (source : α) :
    w source ≤
      (Finset.range d).sum
        (fun k => ∑ initial : α,
          finiteInfluenceColumnIterateKernel influence k initial source * v initial) +
      ∑ initial : α,
        finiteInfluenceColumnIterateKernel influence d initial source * w initial := by
  induction d with
  | zero =>
      simp [finiteInfluenceColumnIterateKernel]
  | succ d ih =>
      have hStep :=
        finiteInfluenceColumnIterateKernel_weighted_subinvariant_step
          influence hInfluence v w hSub d source
      calc
        w source ≤
          (Finset.range d).sum
              (fun k => ∑ initial : α,
                finiteInfluenceColumnIterateKernel influence k initial source * v initial) +
            ∑ initial : α,
              finiteInfluenceColumnIterateKernel influence d initial source * w initial := ih
        _ ≤
          (Finset.range d).sum
              (fun k => ∑ initial : α,
                finiteInfluenceColumnIterateKernel influence k initial source * v initial) +
            ((∑ initial : α,
                finiteInfluenceColumnIterateKernel influence d initial source * v initial) +
              ∑ initial : α,
                finiteInfluenceColumnIterateKernel influence (d + 1) initial source * w initial) := by
          exact add_le_add_right hStep _
        _ =
          (Finset.range (d + 1)).sum
              (fun k => ∑ initial : α,
                finiteInfluenceColumnIterateKernel influence k initial source * v initial) +
            ∑ initial : α,
              finiteInfluenceColumnIterateKernel influence (d + 1) initial source * w initial := by
          rw [Finset.sum_range_succ]
          ring

/-- Exact card-multiplied algebra for one generic finite-kernel random-scan
variation update. -/
theorem finiteInfluenceKernelRandomScanUpdatedVariation_card_mul_eq
    {ι : Type*}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (variation : ι → ℝ)
    (source : ι) :
    (Fintype.card ι : ℝ) *
        finiteInfluenceKernelRandomScanUpdatedVariation K variation source =
      ((Fintype.card ι : ℝ) - 1) * variation source +
        ∑ target : ι, K.influence target source * variation target := by
  let n : ℝ := Fintype.card ι
  have hn : n ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hCard)
  unfold finiteInfluenceKernelRandomScanUpdatedVariation
  change
    n * (n⁻¹ *
      ∑ target : ι,
        finiteInfluenceKernelUpdatedVariation K variation target source) =
      (n - 1) * variation source +
        ∑ target : ι, K.influence target source * variation target
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  rw [finiteInfluenceKernelUpdatedVariation_sum_target_eq]
  ring

/-- Exact finite telescope for generic finite-kernel random-scan variation
iterates. -/
theorem finiteInfluenceKernelRandomScanVariationPartialSum_resolvent_identity
    {ι : Type*}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (variation : ι → ℝ) :
    ∀ M : ℕ, ∀ source : ι,
      (Finset.range M).sum
          (fun m =>
            finiteInfluenceKernelRandomScanVariationIterate
              K variation m source) =
        (Fintype.card ι : ℝ) * variation source +
          (∑ target : ι,
            K.influence target source *
              (Finset.range M).sum
                (fun m =>
                  finiteInfluenceKernelRandomScanVariationIterate
                    K variation m target)) -
          (Fintype.card ι : ℝ) *
            finiteInfluenceKernelRandomScanVariationIterate
              K variation M source := by
  intro M
  induction M with
  | zero =>
      intro source
      simp
  | succ M ih =>
      intro source
      let n : ℝ := Fintype.card ι
      let S : ι → ℝ :=
        fun x =>
          (Finset.range M).sum
            (fun m =>
              finiteInfluenceKernelRandomScanVariationIterate
                K variation m x)
      let u : ι → ℝ :=
        finiteInfluenceKernelRandomScanVariationIterate K variation M
      have hRec :=
        finiteInfluenceKernelRandomScanUpdatedVariation_card_mul_eq
          K hCard u source
      rw [Finset.sum_range_succ]
      change
        S source + u source =
          n * variation source +
            (∑ target : ι,
              K.influence target source * (S target + u target)) -
            n * finiteInfluenceKernelRandomScanUpdatedVariation K u source
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      symm
      calc
        n * variation source +
              ((∑ target : ι,
                  K.influence target source * S target) +
                ∑ target : ι,
                  K.influence target source * u target) -
            n * finiteInfluenceKernelRandomScanUpdatedVariation
              K u source =
          (n * variation source +
              ∑ target : ι,
                K.influence target source * S target -
              n * u source) +
            u source := by
              rw [hRec]
              ring
        _ = S source + u source := by
          simpa [n, S, u] using
            congrArg (fun x => x + u source) (ih source).symm

/-- Generic normalized finite random-scan resolvent profile for a finite
nonnegative influence kernel. -/
noncomputable def finiteInfluenceKernelRandomScanFiniteResolventProfile
    {ι : Type*}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (M : ℕ)
    (source : ι) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ m ∈ Finset.range M,
      finiteInfluenceKernelRandomScanVariationIterate
        K variation m source

/-- The generic normalized finite random-scan resolvent is nonnegative. -/
theorem finiteInfluenceKernelRandomScanFiniteResolventProfile_nonneg
    {ι : Type*}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (hVariation : ∀ e, 0 ≤ variation e)
    (M : ℕ)
    (source : ι) :
    0 ≤ finiteInfluenceKernelRandomScanFiniteResolventProfile
      K variation M source := by
  unfold finiteInfluenceKernelRandomScanFiniteResolventProfile
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun m _ =>
      finiteInfluenceKernelRandomScanVariationIterate_nonneg
        K variation hVariation m source)

/-- The generic normalized finite random-scan resolvent is a transpose
subinvariant for the same finite influence kernel. -/
theorem finiteInfluenceKernelRandomScanFiniteResolventProfile_subinvariant
    {ι : Type*}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (hCard : 0 < Fintype.card ι)
    (variation : ι → ℝ)
    (hVariation : ∀ e, 0 ≤ variation e)
    (M : ℕ)
    (source : ι) :
    finiteInfluenceKernelRandomScanFiniteResolventProfile
        K variation M source ≤
      variation source +
        ∑ target : ι,
          K.influence target source *
            finiteInfluenceKernelRandomScanFiniteResolventProfile
              K variation M target := by
  let n : ℝ := Fintype.card ι
  let S : ι → ℝ :=
    fun x =>
      (Finset.range M).sum
        (fun m =>
          finiteInfluenceKernelRandomScanVariationIterate
            K variation m x)
  let uM : ι → ℝ :=
    finiteInfluenceKernelRandomScanVariationIterate K variation M
  have hnPos : 0 < n := Nat.cast_pos.mpr hCard
  have hTerminal : 0 ≤ uM source := by
    dsimp [uM]
    exact
      finiteInfluenceKernelRandomScanVariationIterate_nonneg
        K variation hVariation M source
  have hIdentity :=
    finiteInfluenceKernelRandomScanVariationPartialSum_resolvent_identity
      K hCard variation M source
  have hSle :
      S source ≤
        n * variation source +
          ∑ target : ι, K.influence target source * S target := by
    calc
      S source =
          n * variation source +
            (∑ target : ι, K.influence target source * S target) -
              n * uM source := by
        simpa [n, S, uM] using hIdentity
      _ ≤
          n * variation source +
            ∑ target : ι, K.influence target source * S target :=
        sub_le_self _
          (mul_nonneg hnPos.le hTerminal)
  unfold finiteInfluenceKernelRandomScanFiniteResolventProfile
  change
    n⁻¹ * S source ≤
      variation source +
        ∑ target : ι,
          K.influence target source * (n⁻¹ * S target)
  calc
    n⁻¹ * S source ≤
        n⁻¹ *
          (n * variation source +
            ∑ target : ι, K.influence target source * S target) :=
      mul_le_mul_of_nonneg_left hSle (inv_nonneg.mpr hnPos.le)
    _ =
      variation source +
        ∑ target : ι,
          K.influence target source * (n⁻¹ * S target) := by
      rw [mul_add, Finset.mul_sum]
      have hInvMul : n⁻¹ * n = 1 :=
        inv_mul_cancel₀ (ne_of_gt hnPos)
      rw [← mul_assoc, hInvMul, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro target _htarget
      ring

/-- The canonical finite random-scan resolvent from #4641 is definitionally
the generic finite-kernel resolvent of the ORIGINAL canonical physical
influence kernel, after the #4640 orbit identification. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_eq_kernel
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN beta hbeta variation M source =
      finiteInfluenceKernelRandomScanFiniteResolventProfile
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta))
        variation M source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
    finiteInfluenceKernelRandomScanFiniteResolventProfile
  apply congrArg
    (fun z : ℝ =>
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro m _hm
  exact congrFun
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeResponseControlledRandomScanVariationIterate_eq_kernel
      H N hN beta hbeta variation m)
    source

/-- The canonical finite random-scan resolvent is a transpose subinvariant for
the ORIGINAL canonical physical influence kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_subinvariant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariation : ∀ e, 0 ≤ variation e)
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN beta hbeta variation M source ≤
      variation source +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)).influence target source *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
              H N hN beta hbeta variation M target := by
  have h :=
    finiteInfluenceKernelRandomScanFiniteResolventProfile_subinvariant
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta))
      (periodicHypercubicEvenSpatialSliceLink_card_pos H)
      variation hVariation M source
  simpa only [
    ← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_eq_kernel] using
    h

/-- At one fixed growing scale, the canonical finite random-scan resolvent
inherits the same volume/rank-independent weighted denominator as the
high-temperature physical influence kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_weightedResolvent
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (bound : ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hVariationBound :
      ∀ e,
        variation e ≤
          bound *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s center e)
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN beta hbeta variation M source ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta)⁻¹ *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  classical
  let responseCoefficient :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
      H N hN beta hbeta s center
  let coefficient :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
      beta s responseCoefficient
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s beta
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (PeriodicHypercubicEvenSpatialSliceLink H) coefficient
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s center
  have hResponseCoefficient :
      0 ≤ responseCoefficient := by
    dsimp [responseCoefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_nonneg
        H N hN beta hbeta s hs center
  have hCoefficientNonneg : 0 ≤ coefficient := by
    dsimp [coefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient_nonneg
        beta s responseCoefficient hbeta hResponseCoefficient
  have hCoefficientLtQ : coefficient < q := by
    dsimp [coefficient, q, responseCoefficient]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeCoefficient_lt_halfBarrierCoefficient
        H N hN s hs beta hbeta hcut center
  have hQ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      s beta hbeta hcut
  have hCoefficientLtOne : coefficient < 1 :=
    hCoefficientLtQ.trans hQ.2
  have hCard :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    periodicHypercubicEvenSpatialSliceLink_card_pos H
  have hPrefix :
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
          finiteRealGeometricSeries rate M ≤
        (1 - coefficient)⁻¹ := by
    simpa [rate] using
      inv_card_mul_finiteRealGeometricSeries_le_one_sub_inv
        (ι := PeriodicHypercubicEvenSpatialSliceLink H)
        hCard hCoefficientNonneg hCoefficientLtOne M
  have hDenCoefficient : 0 < 1 - coefficient :=
    sub_pos.mpr hCoefficientLtOne
  have hDenQ : 0 < 1 - q :=
    sub_pos.mpr hQ.2
  have hInv :
      (1 - coefficient)⁻¹ ≤ (1 - q)⁻¹ :=
    (inv_le_inv₀ hDenCoefficient hDenQ).2 (by linarith)
  have hWNonneg : 0 ≤ W source := by
    dsimp [W]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s (zero_lt_one.trans_le hs).le center source
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
  calc
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ∑ m ∈ Finset.range M,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
              H N hN beta hbeta)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
              H N hN beta hbeta)
            variation m source ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        ∑ m ∈ Finset.range M,
          rate ^ m * bound * W source := by
            apply mul_le_mul_of_nonneg_left
            · apply Finset.sum_le_sum
              intro m _hm
              simpa [rate, coefficient, responseCoefficient, W] using
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledRandomScanVariationIterate_le_weightedRate_pow_mul
                  H beta hbeta s hs center
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
                    H N hN beta hbeta)
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
                    H N hN beta hbeta)
                  responseCoefficient hResponseCoefficient
                  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_exponentialWeightedColumnBound_exactCoefficient
                    H N hN beta hbeta s hs center)
                  variation hVariationNonneg bound hBoundNonneg
                  hVariationBound m source
            · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    _ =
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
        finiteRealGeometricSeries rate M) *
          (bound * W source) := by
            simp_rw [mul_assoc]
            rw [← Finset.sum_mul]
            rw [finiteRealGeometricSeries]
            ring
    _ ≤
      (1 - coefficient)⁻¹ * (bound * W source) :=
        mul_le_mul_of_nonneg_right hPrefix
          (mul_nonneg hBoundNonneg hWNonneg)
    _ ≤
      (1 - q)⁻¹ * (bound * W source) :=
        mul_le_mul_of_nonneg_right hInv
          (mul_nonneg hBoundNonneg hWNonneg)
    _ =
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta)⁻¹ *
        bound *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
      rfl

/-- If every nonzero initial variation coordinate lies at base-L1 distance at
least D from one source, the canonical finite random-scan resolvent at that
source has the reciprocal exponential factor s^(-D). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_spatialResolvent_of_distance
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg : ∀ e, 0 ≤ variation e)
    (D : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistance :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        variation target ≠ 0 →
          D ≤
            periodicHypercubicEdgeBaseL1Distance
              (PeriodicHypercubicEvenSideLength H)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
              (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))
    (M : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
        H N hN beta hbeta variation M source ≤
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta)⁻¹ *
        (s ^ D)⁻¹ *
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          variation target) := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s source
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s beta
  let total :=
    ∑ target : PeriodicHypercubicEvenSpatialSliceLink H, variation target
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile
      H N hN beta hbeta variation M
  let A := (1 - q)⁻¹ * (s ^ D)⁻¹ * total
  let C := (1 - q)⁻¹ * total
  have hQ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
      s beta hbeta hcut
  have hsPos : 0 < s := zero_lt_one.trans_le hs
  have hPowDPos : 0 < s ^ D := pow_pos hsPos D
  have hTotalNonneg : 0 ≤ total := by
    dsimp [total]
    exact Finset.sum_nonneg fun target _ => hVariationNonneg target
  have hInvGapNonneg : 0 ≤ (1 - q)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hQ.2.le)
  have hCNonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hInvGapNonneg hTotalNonneg
  have hWeightOne :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        1 ≤ W target := by
    intro target
    dsimp [W,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight]
    have hPow :=
      pow_le_pow_right₀ hs
        (Nat.zero_le
          (periodicHypercubicEdgeBaseL1Distance
            (PeriodicHypercubicEvenSideLength H)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
            (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)))
    simpa using hPow
  have hVariationLeTotal :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        variation target ≤ total := by
    intro target
    dsimp [total]
    exact
      Finset.single_le_sum
        (fun other _ => hVariationNonneg other)
        (Finset.mem_univ target)
  have hVariationWeighted :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        variation target ≤ total * W target := by
    intro target
    calc
      variation target ≤ total := hVariationLeTotal target
      _ = total * 1 := by ring
      _ ≤ total * W target :=
        mul_le_mul_of_nonneg_left (hWeightOne target) hTotalNonneg
  have hWBound :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        w target ≤ C * W target := by
    intro target
    dsimp [w, C]
    simpa [mul_assoc] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_le_weightedResolvent
        H N hN s hs beta hbeta hcut source variation hVariationNonneg
        total hTotalNonneg hVariationWeighted M target
  have hWNonneg :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤ w target := by
    intro target
    dsimp [w]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_nonneg
        H N hN beta hbeta variation hVariationNonneg M target
  have hSub :
      ∀ y : PeriodicHypercubicEvenSpatialSliceLink H,
        w y ≤
          variation y +
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              K.influence target y * w target := by
    intro y
    dsimp [w, K]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeRandomScanFiniteResolventProfile_subinvariant
        H N hN beta hbeta variation hVariationNonneg M y
  have hSelf : W source = 1 := by
    dsimp [W]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_self
        H s source
  have hTerm :
      ∀ k : ℕ,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceColumnIterateKernel
              K.influence k target source *
            variation target) ≤
          q ^ k * (s ^ D)⁻¹ * total := by
    intro k
    calc
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceColumnIterateKernel
              K.influence k target source *
            variation target) ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          (q ^ k * (s ^ D)⁻¹) * variation target := by
            apply Finset.sum_le_sum
            intro target _htarget
            by_cases hZero : variation target = 0
            · simp [hZero]
            · have hDist := hDistance target hZero
              have hWeightLower : s ^ D ≤ W target := by
                dsimp [W,
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight]
                exact pow_le_pow_right₀ hs hDist
              have hWeightPos : 0 < W target := by
                dsimp [W]
                exact
                  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
                    H s hsPos source target
              have hInvWeight :
                  (W target)⁻¹ ≤ (s ^ D)⁻¹ :=
                (inv_le_inv₀ hWeightPos hPowDPos).2 hWeightLower
              have hEntryColumn :=
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influenceIterate_le_pow_halfBarrierCoefficient_mul_sourceWeight_div_targetWeight
                  H N hN s hs beta hbeta hcut source target source k
              have hEntry :
                  finiteInfluenceColumnIterateKernel
                      K.influence k target source ≤
                    q ^ k * (W target)⁻¹ := by
                simpa [K, W, q, hSelf, div_eq_mul_inv] using hEntryColumn
              have hEntry' :
                  finiteInfluenceColumnIterateKernel
                      K.influence k target source ≤
                    q ^ k * (s ^ D)⁻¹ := by
                exact hEntry.trans
                  (mul_le_mul_of_nonneg_left hInvWeight
                    (pow_nonneg hQ.1 k))
              exact
                mul_le_mul_of_nonneg_right hEntry'
                  (hVariationNonneg target)
      _ = q ^ k * (s ^ D)⁻¹ * total := by
        rw [Finset.mul_sum]
  have hPartial :
      ∀ d : ℕ,
        (Finset.range d).sum
            (fun k =>
              ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                finiteInfluenceColumnIterateKernel
                    K.influence k target source *
                  variation target) ≤
          A := by
    intro d
    have hSeries :
        (Finset.range d).sum
            (fun k =>
              ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                finiteInfluenceColumnIterateKernel
                    K.influence k target source *
                  variation target) ≤
          finiteRealGeometricSeries q d * ((s ^ D)⁻¹ * total) := by
      calc
        (Finset.range d).sum
            (fun k =>
              ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                finiteInfluenceColumnIterateKernel
                    K.influence k target source *
                  variation target) ≤
          (Finset.range d).sum
            (fun k => q ^ k * (s ^ D)⁻¹ * total) := by
              apply Finset.sum_le_sum
              intro k _hk
              exact hTerm k
        _ =
          finiteRealGeometricSeries q d * ((s ^ D)⁻¹ * total) := by
            unfold finiteRealGeometricSeries
            simp_rw [mul_assoc]
            rw [← Finset.sum_mul]
    have hGeom :=
      finiteRealGeometricSeries_le_inv_one_sub q hQ.1 hQ.2 d
    calc
      (Finset.range d).sum
          (fun k =>
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              finiteInfluenceColumnIterateKernel
                  K.influence k target source *
                variation target) ≤
        finiteRealGeometricSeries q d * ((s ^ D)⁻¹ * total) := hSeries
      _ ≤
        (1 - q)⁻¹ * ((s ^ D)⁻¹ * total) :=
          mul_le_mul_of_nonneg_right hGeom
            (mul_nonneg (inv_nonneg.mpr hPowDPos.le) hTotalNonneg)
      _ = A := by
        dsimp [A]
        ring
  have hResidual :
      ∀ d : ℕ,
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceColumnIterateKernel K.influence d target source *
            w target) ≤
          q ^ d * C := by
    intro d
    have hColumn :
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceColumnIterateKernel K.influence d target source *
            W target) ≤
          q ^ d * W source := by
      simpa only [K, W, q] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influenceIterate_exponentialWeightedColumn_le_pow_halfBarrierCoefficient
          H N hN s hs beta hbeta hcut source source d
    calc
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceColumnIterateKernel K.influence d target source *
            w target) ≤
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          finiteInfluenceColumnIterateKernel K.influence d target source *
            (C * W target) := by
              apply Finset.sum_le_sum
              intro target _htarget
              exact
                mul_le_mul_of_nonneg_left
                  (hWBound target)
                  (finiteInfluenceColumnIterateKernel_nonneg
                    K.influence K.influence_nonneg d target source)
      _ =
        C *
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            finiteInfluenceColumnIterateKernel K.influence d target source *
              W target) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro target _htarget
            ring
      _ ≤ C * (q ^ d * W source) :=
        mul_le_mul_of_nonneg_left hColumn hCNonneg
      _ = q ^ d * C := by
        rw [hSelf]
        ring
  have hForall :
      ∀ d : ℕ, w source ≤ A + q ^ d * C := by
    intro d
    have hUnroll :=
      finiteInfluenceColumnIterateKernel_subinvariant_le_partial_resolvent_add_residual
        K.influence K.influence_nonneg variation w hSub d source
    exact hUnroll.trans
      (add_le_add (hPartial d) (hResidual d))
  have hPow :
      Tendsto (fun d : ℕ => q ^ d) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hQ.1 hQ.2
  have hTendsto :
      Tendsto (fun d : ℕ => A + q ^ d * C) atTop (𝓝 A) := by
    have hResidualTendsto :
        Tendsto (fun d : ℕ => q ^ d * C) atTop (𝓝 0) := by
      simpa using hPow.mul_const C
    simpa using tendsto_const_nhds.add hResidualTendsto
  change w source ≤ A
  exact le_of_tendsto' hTendsto hForall

end

end MGAP4D.MathlibAnalytic
