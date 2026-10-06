import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalUniformFullSweepContraction
import MGAP4D.MathlibAnalytic.PhysicalYangMillsFloorExponentialTransferTrajectory
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Floor-scaled volume-uniform posterior full-sweep decay

PR #5200 proves that, on the canonical positive Dobrushin interval, one complete
posterior random-scan sweep contracts every nonnegative variation envelope by

  rho(s,beta)
    = exp(-(1 - alpha_bar(s,beta))) < 1,

where rho contains no finite-volume parameter H or rank N.

This file performs the next continuum-scaling step without identifying Markov
sweep time with Euclidean physical time.

For a positive lattice-spacing sequence a_n -> 0 and a fixed positive target
time t, the canonical floor count

  k_n = floor(t / a_n)

tends to infinity.  Consequently

  rho ^ k_n -> 0.

Combining this scalar fact with PR #5200 yields decay to zero for the actual
posterior variation after k_n complete sweeps, uniformly with respect to any
varying finite-volume sequence H_n, boundary sequence, and source-link
sequence, provided the initial variation envelopes share one finite bound V.

This closes the analytic floor-scaling consequence of the H-independent
full-sweep contraction.  It deliberately does not assert that one random-scan
sweep is one Euclidean physical-time lattice step.  Such an identification,
or a generator-level bridge proving it, remains a separate obligation.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology BigOperators

noncomputable section

local instance posteriorUniformFloorSweepSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At fixed positive target time, the natural floor-selected iteration count
goes to infinity as positive lattice spacing tends to zero. -/
theorem physicalTemporalFloorNatStep_tendsto_atTop_of_pos
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (t : NNReal)
    (ht : 0 < t) :
    Tendsto
      (physicalTemporalFloorNatStep latticeSpacing t)
      atTop atTop := by
  have htReal : 0 < (t : ℝ) := by
    exact_mod_cast ht
  have htime :=
    physicalTemporalFloorNatStep_tendsto
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero t
  refine tendsto_atTop.2 ?_
  intro M
  by_cases hM : M = 0
  · subst M
    exact Filter.Eventually.of_forall fun n => Nat.zero_le _
  · have hMNat : 0 < M := Nat.pos_of_ne_zero hM
    have hMReal : 0 < (M : ℝ) := by
      exact_mod_cast hMNat
    let epsilon : ℝ := (t : ℝ) / (2 * (M : ℝ))
    have hEpsilon : 0 < epsilon := by
      dsimp [epsilon]
      positivity
    have hSpacing :
        ∀ᶠ n in atTop, latticeSpacing n < epsilon :=
      (tendsto_order.1 latticeSpacing_tendsto_zero).2
        epsilon hEpsilon
    have hTimeLower :
        ∀ᶠ n in atTop,
          (t : ℝ) / 2 <
            (physicalTemporalFloorNatStep latticeSpacing t n : ℝ) *
              latticeSpacing n := by
      exact
        (tendsto_order.1 htime).1
          ((t : ℝ) / 2) (by linarith)
    filter_upwards [hSpacing, hTimeLower] with n hSpacingN hTimeN
    by_contra hNot
    have hStepLt :
        physicalTemporalFloorNatStep latticeSpacing t n < M :=
      Nat.lt_of_not_ge hNot
    have hStepLtReal :
        (physicalTemporalFloorNatStep latticeSpacing t n : ℝ) < (M : ℝ) := by
      exact_mod_cast hStepLt
    have hSpacingPos : 0 < latticeSpacing n :=
      latticeSpacing_pos n
    have hFirst :
        (physicalTemporalFloorNatStep latticeSpacing t n : ℝ) *
            latticeSpacing n <
          (M : ℝ) * latticeSpacing n :=
      mul_lt_mul_of_pos_right hStepLtReal hSpacingPos
    have hSecond :
        (M : ℝ) * latticeSpacing n <
          (M : ℝ) * epsilon :=
      mul_lt_mul_of_pos_left hSpacingN hMReal
    have hMEpsilon :
        (M : ℝ) * epsilon = (t : ℝ) / 2 := by
      dsimp [epsilon]
      field_simp [ne_of_gt hMReal]
    linarith

/-- Any fixed scalar contraction factor in [0,1) vanishes when raised to the
positive-time floor count associated with a lattice spacing tending to zero. -/
theorem floorNatStep_pow_tendsto_zero_of_lt_one
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (rho : ℝ)
    (hrhoNonneg : 0 ≤ rho)
    (hrhoLtOne : rho < 1)
    (t : NNReal)
    (ht : 0 < t) :
    Tendsto
      (fun n =>
        rho ^ physicalTemporalFloorNatStep latticeSpacing t n)
      atTop (nhds 0) := by
  exact
    (tendsto_pow_atTop_nhds_zero_of_lt_one hrhoNonneg hrhoLtOne).comp
      (physicalTemporalFloorNatStep_tendsto_atTop_of_pos
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero t ht)

/-- The canonical H-independent posterior full-sweep factor therefore vanishes
at every positive floor-scaled time as lattice spacing tends to zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_floorNatStep_tendsto_zero
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (t : NNReal)
    (ht : 0 < t) :
    Tendsto
      (fun n =>
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
          s beta) ^
          physicalTemporalFloorNatStep latticeSpacing t n)
      atTop (nhds 0) := by
  exact
    floorNatStep_pow_tendsto_zero_of_lt_one
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
        s beta)
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_pos
        s beta).le
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_lt_one
        s hs beta hbeta hbetaCutoff)
      t ht

/-- Pointwise floor-scaled bound for a varying finite-volume family.  The
iteration count is the floor number of complete sweeps, so the actual number of
single-link random-scan updates is floor(t/a_n) times the spatial-link count of
that finite volume. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanVariationIterate_floorSweeps_le
    (H : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B :
      (n : ℕ) →
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (H n) N)
    (variation :
      (n : ℕ) →
        PeriodicHypercubicEvenSpatialSliceLink (H n) → ℝ)
    (hVariationNonneg :
      ∀ n e, 0 ≤ variation n e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ n e, variation n e ≤ V)
    (source :
      (n : ℕ) → PeriodicHypercubicEvenSpatialSliceLink (H n))
    (latticeSpacing : ℕ → ℝ)
    (t : NNReal)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
          (H n) N hN s hs beta hbeta hbetaCutoff (B n)).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        (variation n)
        (physicalTemporalFloorNatStep latticeSpacing t n *
          Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (H n)))
        (source n) ≤
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
        s beta) ^
          physicalTemporalFloorNatStep latticeSpacing t n *
        V := by
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanVariationIterate_fullSweep_le
      (H n) N hN s hs beta hbeta hbetaCutoff (B n)
      (variation n)
      (hVariationNonneg n)
      V hV
      (hVariationLe n)
      (physicalTemporalFloorNatStep latticeSpacing t n)
      (source n)

/-- The actual posterior variation at positive floor-scaled sweep time tends to
zero uniformly along arbitrary varying finite volumes, boundaries, and source
links, provided the starting variation envelope has one common bound V. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanVariationIterate_floorSweeps_tendsto_zero
    (H : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B :
      (n : ℕ) →
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (H n) N)
    (variation :
      (n : ℕ) →
        PeriodicHypercubicEvenSpatialSliceLink (H n) → ℝ)
    (hVariationNonneg :
      ∀ n e, 0 ≤ variation n e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ n e, variation n e ≤ V)
    (source :
      (n : ℕ) → PeriodicHypercubicEvenSpatialSliceLink (H n))
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero :
      Tendsto latticeSpacing atTop (nhds 0))
    (t : NNReal)
    (ht : 0 < t) :
    Tendsto
      (fun n =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
            (H n) N hN s hs beta hbeta hbetaCutoff (B n)).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
          (variation n)
          (physicalTemporalFloorNatStep latticeSpacing t n *
            Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (H n)))
          (source n))
      atTop (nhds 0) := by
  let rho :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate
      s beta
  let upper : ℕ → ℝ :=
    fun n =>
      rho ^ physicalTemporalFloorNatStep latticeSpacing t n * V
  have hUpperTendsto :
      Tendsto upper atTop (nhds 0) := by
    have hRho :=
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformFullSweepRate_floorNatStep_tendsto_zero
        s hs beta hbeta hbetaCutoff
        latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
        t ht
    simpa [upper, rho] using hRho.mul_const V
  apply squeeze_zero
  · intro n
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
          (H n) N hN s hs beta hbeta hbetaCutoff (B n)).toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        (variation n)
        (hVariationNonneg n)
        (physicalTemporalFloorNatStep latticeSpacing t n *
          Fintype.card (PeriodicHypercubicEvenSpatialSliceLink (H n)))
        (source n)
  · intro n
    simpa [upper, rho] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformRandomScanVariationIterate_floorSweeps_le
        H N hN s hs beta hbeta hbetaCutoff B variation
        hVariationNonneg V hV hVariationLe source latticeSpacing t n
  · exact hUpperTendsto

end

end MathlibAnalytic
end MGAP4D
