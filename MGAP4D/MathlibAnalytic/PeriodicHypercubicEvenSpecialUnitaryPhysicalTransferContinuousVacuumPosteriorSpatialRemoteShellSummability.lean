import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorSpatialLocalDegree
import MGAP4D.MathlibAnalytic.FiniteExponentialShellGeometricBound
import Mathlib.Tactic

/-!
# Volume-uniform spatial remote-shell summability for posterior influence

PR #5190 closes the volume accumulation problem for the direct local part of
the refined posterior influence: every spatial plaquette-local row and column
has mass at most

  18 * q_local(beta),

uniformly in the periodic side H.

The remaining issue is the remote contribution. This file isolates the exact
combinatorial statement needed for that step.

Starting from one spatial link, let reachable d be the set of endpoints of
walks obtained by exactly d off-diagonal spatial plaquette-local steps. Since
every link has at most 18 such neighbors,

  card(reachable d) <= 18^d.

Consequently, for any integer-valued distance whose distance-d shell embeds
into reachable d, exponential pointwise decay with ratio r is summable
uniformly in volume whenever

  18 * r < 1.

Any remote profile satisfying

  remote(source) <= C * r^(distance source)

then has total mass at most

  C / (1 - 18*r).

This is the combinatorial shell-summability half of the remote problem. The
analytic theorem that the actual posterior remote response has such spatial
decay is intentionally not asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorSpatialRemoteShellSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Endpoints reachable from target after exactly d off-diagonal intrinsic
spatial plaquette-local steps. -/
noncomputable def
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
    (H d : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Nat.rec {target}
    (fun _ previous =>
      previous.biUnion
        (periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H))
    d

@[simp] theorem
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable_zero
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable H 0 target =
      {target} := by
  simp [periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable]

@[simp] theorem
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable_succ
    (H d : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable H (d + 1) target =
      (periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable H d target).biUnion
        (periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H) := by
  simp [periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable]

/-- One exact-step expansion costs at most the uniform local degree 18. -/
theorem
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable_succ_card_le
    (H d : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
        H (d + 1) target).card ≤
      (periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
        H d target).card * 18 := by
  classical
  let reachable :=
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable H d target
  rw [
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable_succ]
  change
    (reachable.biUnion
      (periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H)).card ≤
      reachable.card * 18
  calc
    (reachable.biUnion
        (periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H)).card ≤
      ∑ source ∈ reachable,
        (periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors
          H source).card :=
      finset_card_biUnion_le_sum_card reachable
        (periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors H)
    _ ≤ ∑ _source ∈ reachable, 18 := by
      apply Finset.sum_le_sum
      intro source _hSource
      exact
        periodicHypercubicEvenSpatialSlicePlaquetteLocalNeighbors_card_le_eighteen
          H source
    _ = reachable.card * 18 := by simp

/-- Exact-step spatial reachable endpoint sets grow at most as 18^d,
uniformly in the periodic side. -/
theorem
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable_card_le_pow_eighteen
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ d : ℕ,
      (periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
        H d target).card ≤ 18 ^ d := by
  intro d
  induction d with
  | zero =>
      simp
  | succ d ih =>
      calc
        (periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
            H (d + 1) target).card ≤
          (periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
            H d target).card * 18 :=
          periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable_succ_card_le
            H d target
        _ ≤ 18 ^ d * 18 :=
          Nat.mul_le_mul_right 18 ih
        _ = 18 ^ (d + 1) := by
          rw [pow_succ]

/-- Real-valued form of the exact-step spatial shell-capacity estimate. -/
theorem
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable_card_real_le_pow_eighteen
    (H d : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ((periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
        H d target).card : ℝ) ≤
      (18 : ℝ) ^ d := by
  exact_mod_cast
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable_card_le_pow_eighteen
      H target d

/-- If an integer-valued spatial distance is realized by an exact local walk,
then every distance shell has cardinality at most 18^m. -/
theorem
    periodicHypercubicEvenSpatialSliceDistanceShell_card_real_le_pow_eighteen
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (distance : PeriodicHypercubicEvenSpatialSliceLink H → ℕ)
    (hReachable :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        source ∈
          periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
            H (distance source) target)
    (m : ℕ) :
    (((Finset.univ.filter fun source :
        PeriodicHypercubicEvenSpatialSliceLink H =>
          distance source = m).card : ℕ) : ℝ) ≤
      (18 : ℝ) ^ m := by
  classical
  let shell : Finset (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Finset.univ.filter fun source => distance source = m
  have hSubset :
      shell ⊆
        periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
          H m target := by
    intro source hSource
    have hDistance : distance source = m :=
      (Finset.mem_filter.mp hSource).2
    have h := hReachable source
    rw [hDistance] at h
    exact h
  have hCard :
      shell.card ≤
        (periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
          H m target).card :=
    Finset.card_le_card hSubset
  have hReachCard :
      (periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
          H m target).card ≤
        18 ^ m :=
    periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable_card_le_pow_eighteen
      H target m
  have hNat : shell.card ≤ 18 ^ m :=
    hCard.trans hReachCard
  have hReal : (shell.card : ℝ) ≤ ((18 ^ m : ℕ) : ℝ) := by
    exact_mod_cast hNat
  simpa [shell] using hReal

/-- The spatial degree-18 shell bound instantiates the existing finite
exponential-shell control whenever every distance is realized by a local walk
and 18 * ratio < 1. -/
noncomputable def
    periodicHypercubicEvenSpatialSlicePosteriorFiniteExponentialShellControl
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (distance : PeriodicHypercubicEvenSpatialSliceLink H → ℕ)
    (radius : ℕ)
    (ratio : ℝ)
    (hRatioNonneg : 0 ≤ ratio)
    (hGrowthRatio : 18 * ratio < 1)
    (hDistanceRadius :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        distance source < radius)
    (hReachable :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        source ∈
          periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
            H (distance source) target) :
    FiniteDistanceShellGeometricSum.FiniteExponentialShellControl
      (PeriodicHypercubicEvenSpatialSliceLink H) := by
  have hRatioLtOne : ratio < 1 := by
    nlinarith
  exact
    { distance := distance
      radius := radius
      ratio := ratio
      shellPrefactor := 1
      shellGrowth := 18
      ratio_nonneg := hRatioNonneg
      ratio_lt_one := hRatioLtOne
      shellPrefactor_nonneg := by norm_num
      shellGrowth_nonneg := by norm_num
      growth_mul_ratio_lt_one := by
        simpa using hGrowthRatio
      distance_lt_radius := hDistanceRadius
      shell_card_real_le := by
        intro m
        simpa using
          periodicHypercubicEvenSpatialSliceDistanceShell_card_real_le_pow_eighteen
            H target distance hReachable m }

/-- The total exponential spatial shell weight is volume independent:
sum ratio^distance <= 1/(1-18 ratio). -/
theorem
    periodicHypercubicEvenSpatialSlice_sum_pow_distance_le_one_div_one_sub_eighteen_mul
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (distance : PeriodicHypercubicEvenSpatialSliceLink H → ℕ)
    (radius : ℕ)
    (ratio : ℝ)
    (hRatioNonneg : 0 ≤ ratio)
    (hGrowthRatio : 18 * ratio < 1)
    (hDistanceRadius :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        distance source < radius)
    (hReachable :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        source ∈
          periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
            H (distance source) target) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      ratio ^ distance source) ≤
      1 / (1 - 18 * ratio) := by
  let C :=
    periodicHypercubicEvenSpatialSlicePosteriorFiniteExponentialShellControl
      H target distance radius ratio hRatioNonneg hGrowthRatio
      hDistanceRadius hReachable
  have h :=
    FiniteDistanceShellGeometricSum.FiniteExponentialShellControl.sum_pow_distance_le_explicit
      C
  simpa [C,
    periodicHypercubicEvenSpatialSlicePosteriorFiniteExponentialShellControl] using h

/-- Any pointwise remote influence bound C * ratio^distance therefore has a
volume-independent total mass bound C/(1-18 ratio). -/
theorem
    periodicHypercubicEvenSpatialSlice_remoteMass_le_of_exponential_distance_decay
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (distance : PeriodicHypercubicEvenSpatialSliceLink H → ℕ)
    (radius : ℕ)
    (ratio prefactor : ℝ)
    (hRatioNonneg : 0 ≤ ratio)
    (hGrowthRatio : 18 * ratio < 1)
    (hPrefactorNonneg : 0 ≤ prefactor)
    (hDistanceRadius :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        distance source < radius)
    (hReachable :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        source ∈
          periodicHypercubicEvenSpatialSlicePlaquetteLocalReachable
            H (distance source) target)
    (remote : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRemote :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        remote source ≤ prefactor * ratio ^ distance source) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      remote source) ≤
      prefactor / (1 - 18 * ratio) := by
  have hWeight :=
    periodicHypercubicEvenSpatialSlice_sum_pow_distance_le_one_div_one_sub_eighteen_mul
      H target distance radius ratio hRatioNonneg hGrowthRatio
      hDistanceRadius hReachable
  calc
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        remote source) ≤
      ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        prefactor * ratio ^ distance source := by
          apply Finset.sum_le_sum
          intro source _hSource
          exact hRemote source
    _ =
      prefactor *
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          ratio ^ distance source) := by
            rw [Finset.mul_sum]
    _ ≤ prefactor * (1 / (1 - 18 * ratio)) :=
      mul_le_mul_of_nonneg_left hWeight hPrefactorNonneg
    _ = prefactor / (1 - 18 * ratio) := by
      simp [div_eq_mul_inv]

end

end MathlibAnalytic
end MGAP4D
