import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRandomScanVariationIteration
import Mathlib.Tactic

/-!
# Finite non-strict influence resolvent for continuous-vacuum posterior variation

PR #5164 defines the exact finite random-scan variation iterate

  u₀ = v,
  uₘ₊₁ = U uₘ

for the continuous-state posterior non-strict influence carrier.  This file
extracts the exact finite influence-kernel algebra before any strictness
assumption.

For the number n of spatial-slice links, one random-scan update satisfies

  n (U v)(s) =
    (n - 1) v(s) + ∑_t c(t,s) v(t).

For the finite partial sum

  S_M = ∑_{m<M} u_m,

telescoping gives the exact identity

  S_M(s) =
    n v(s) + ∑_t c(t,s) S_M(t) - n u_M(s).

Since every finite iterate is nonnegative, the normalized finite accumulated
profile

  w_M = n⁻¹ S_M

already obeys the transpose subinvariance inequality

  w_M(s) ≤ v(s) + ∑_t c(t,s) w_M(t).

This is a fully finite theorem over the literal non-strict posterior influence
matrix.  No strict row-sum estimate, geometric convergence, infinite Neumann
series, posterior fixed-point closure, heat-bath-time / Euclidean-time
identification, H1-D5 exact descent, or complete Yang--Mills mass-gap claim is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorFiniteResolventSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact finite partial sum of posterior random-scan variation iterates. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    ℕ → PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
  fun m =>
    Nat.rec (fun _ => 0)
      (fun k previous source =>
        previous source +
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D variation k source)
      m

/-- The finite partial sum is the literal finite sum of posterior random-scan
variation iterates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_eq_sum
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
        D variation M source =
      (Finset.range M).sum
        (fun m =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D variation m source) := by
  induction M with
  | zero =>
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum]
  | succ M ih =>
      rw [Finset.sum_range_succ]
      simpa [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum] using
        congrArg
          (fun x =>
            x +
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
                D variation M source)
          ih

/-- Exact sum over target links for one posterior random-scan pointwise
variation update.  The deleted diagonal target contributes one copy of the
source variation, while the influence diagonal itself is zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_targetSum_eq
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
        D variation target source) =
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) - 1) *
          variation source +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * variation target := by
  classical
  have hPointwise (target : PeriodicHypercubicEvenSpatialSliceLink H) :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
          D variation target source =
        variation source + D.influence target source * variation target -
          (if target = source then variation source else 0) := by
    by_cases h : target = source
    · subst target
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation,
        D.influence_diagonal_zero]
    · have h' : source ≠ target := Ne.symm h
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation,
        h, h']
  calc
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
        D variation target source) =
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (variation source + D.influence target source * variation target -
          (if target = source then variation source else 0)) := by
      apply Finset.sum_congr rfl
      intro target _
      exact hPointwise target
    _ =
      (∑ _target : PeriodicHypercubicEvenSpatialSliceLink H, variation source) +
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * variation target) -
        variation source := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp
    _ =
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) - 1) *
          variation source +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * variation target := by
      simp [nsmul_eq_mul]
      ring

/-- Exact pointwise algebra of the posterior uniform random-scan variation
operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_card_mul_eq
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
          D variation source =
      ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) - 1) *
          variation source +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * variation target := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hn : n ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hEdge)
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
  change
    n * (n⁻¹ *
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
          D variation target source) =
      (n - 1) * variation source +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * variation target
  rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_targetSum_eq
      D variation source

/-- Finite posterior random-scan telescope before normalization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_resolvent_identity
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)) :
    ∀ M : ℕ, ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
          D variation M source =
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
            variation source +
          (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            D.influence target source *
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
                D variation M target) -
          (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
              D variation M source := by
  intro M
  induction M with
  | zero =>
      intro source
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate]
  | succ M ih =>
      intro source
      let n : ℝ :=
        Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
      let S :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
          D variation M
      let u :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D variation M
      have hRec :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_card_mul_eq
          D u hEdge source
      change
        S source + u source =
          n * variation source +
            (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              D.influence target source * (S target + u target)) -
            n *
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
                D u source
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      symm
      calc
        n * variation source +
              ((∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                  D.influence target source * S target) +
                ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                  D.influence target source * u target) -
            n *
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
                D u source =
          (n * variation source +
              ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
                D.influence target source * S target -
              n * u source) +
            u source := by
          rw [hRec]
          ring
        _ = S source + u source := by
          simpa [n, S, u] using
            congrArg (fun x => x + u source) (ih source).symm

/-- Normalized finite accumulated posterior random-scan variation profile. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ *
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
      D variation M source

/-- The normalized finite accumulated posterior random-scan profile is
nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_nonneg
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariation :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
        D variation M source := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  induction M with
  | zero =>
      simp [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum]
  | succ M ih =>
      change
        0 ≤
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
              D variation M source +
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
              D variation M source
      exact add_nonneg ih
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
          D variation hVariation M source)

/-- The finite normalized posterior random-scan accumulated profile is already
transpose-subinvariant under the non-strict influence kernel. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_subinvariant
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariation :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
        D variation M source ≤
      variation source +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
              D variation M target := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let S :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
      D variation M
  let uM :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
      D variation M
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hTerminal : 0 ≤ uM source :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
      D variation hVariation M source
  have hIdentity :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_resolvent_identity
      D variation hEdge M source
  have hSle :
      S source ≤
        n * variation source +
          ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
            D.influence target source * S target := by
    calc
      S source =
          n * variation source +
            (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              D.influence target source * S target) -
            n * uM source := by
        simpa [n, S, uM] using hIdentity
      _ ≤
          n * variation source +
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              D.influence target source * S target :=
        sub_le_self _ (mul_nonneg hnPos.le hTerminal)
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
  change
    n⁻¹ * S source ≤
      variation source +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * (n⁻¹ * S target)
  calc
    n⁻¹ * S source ≤
        n⁻¹ *
          (n * variation source +
            ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              D.influence target source * S target) := by
      exact mul_le_mul_of_nonneg_left hSle (inv_nonneg.mpr hnPos.le)
    _ =
      variation source +
        ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source * (n⁻¹ * S target) := by
      rw [mul_add, Finset.mul_sum]
      have hInvMul : n⁻¹ * n = 1 :=
        inv_mul_cancel₀ (ne_of_gt hnPos)
      rw [← mul_assoc, hInvMul, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro target _
      ring

end

end MathlibAnalytic
end MGAP4D
