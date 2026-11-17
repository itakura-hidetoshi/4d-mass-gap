import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentPositivity
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANB — full-periodic Wilson positive-half fiber law

Exact original finite-volume Wilson Gibbs density, integrated over only the
negative open-half Haar coordinates. The resulting density retains the full
partition function and the genuinely interacting fixed-boundary vacuum. It is
NOT the separately normalized temporal-gauge half-path law of ANA.

This additive theorem file changes no original model definitions, no pinned
mathlib dependency, and no old proof statements. Machine certification is
required before it can be merged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANB_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37ANB_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37ANB_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37ANB_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37ANB_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Full-periodic Gibbs fiber density in the positive closure equals the
existing completed positive-half Gram feature times the boundary vacuum. -/
theorem p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_eq_vacuum_mul_feature
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    (∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) =
      periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta b *
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta b x := by
  let μ := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let c := periodicHypercubicEvenOpenHalfOrientationCorrection
    (H := H) (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ)
  let f := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
    H N hN beta hbeta b
  let d : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N → ℝ :=
    fun y => (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
      H N hN beta hbeta (b, (x, y))).toReal
  have htransport : (∫ y, d (c y) ∂μ) = ∫ y, d y ∂μ := by
    dsimp [d, c, μ]
    simpa only [one_mul, mul_one] using
      (periodicHypercubicEvenBoundaryObservable_corrected_innerIntegral_eq_original
        H N hN beta hbeta (fun _ => (1 : ℝ)) b x)
  have hfactor (y : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
      d (c y) = f x * f y := by
    dsimp [d, c, f]
    rw [periodicHypercubicEvenBoundaryDensity_orientationCorrection_eq_inner]
    rw [periodicHypercubicEven_real_inner_eq_mul]
  change (∫ y, d y ∂μ) =
    periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta b * f x
  calc
    (∫ y, d y ∂μ) = ∫ y, d (c y) ∂μ := htransport.symm
    _ = ∫ y, f x * f y ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      exact hfactor y
    _ = f x * (∫ y, f y ∂μ) := integral_const_mul _ _
    _ = periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta b * f x := by
      change f x * (∫ y, f y ∂μ) = (∫ y, f y ∂μ) * f x
      ring

/-- The exact full-periodic positive-closure fiber has positive mass. -/
theorem p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :
    0 < (∫ y,
      (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
        H N hN beta hbeta (b, (x, y))).toReal
      ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  rw [p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_eq_vacuum_mul_feature]
  exact mul_pos
    (periodicHypercubicEvenBoundaryVacuumMoment_pos H N hN beta hbeta b)
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pos
      H N hN beta hbeta b x)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_eq_vacuum_mul_feature
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANB_fullPeriodicPositiveHalfFiber_pos
