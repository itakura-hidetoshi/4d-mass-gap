import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakLimitObservableNontriviality
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteEnergyVarianceLowerBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A sequence of finite periodic four-dimensional `Z₂` Wilson systems with one
selected gauge-invariant plaquette observable at each scale. -/
structure Z2PeriodicHypercubicPlaquetteTrajectory where
  sideLength : ℕ → ℕ
  sideLength_ge_two : ∀ k, 2 ≤ sideLength k
  beta : ℕ → ℝ
  beta_nonneg : ∀ k, 0 ≤ beta k
  plaquette : ∀ k, PeriodicHypercubicPlaquette (sideLength k)

/-- Finite-volume Gibbs variance of the selected plaquette observable at one
scale of a periodic `Z₂` trajectory. -/
def Z2PeriodicHypercubicPlaquetteTrajectory.gibbsVariance
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ) : ℝ := by
  have hPos : 0 < T.sideLength k :=
    lt_of_lt_of_le (by norm_num) (T.sideLength_ge_two k)
  letI : NeZero (T.sideLength k) := ⟨Nat.ne_of_gt hPos⟩
  let L := z2PeriodicHypercubicOrientedWilsonSystem
    (T.sideLength k) (T.beta k) (T.beta_nonneg k)
  exact L.gibbsVarianceReal
    (z2PeriodicHypercubicPlaquetteEnergyObservable
      (T.sideLength k) (T.beta k) (T.beta_nonneg k) (T.plaquette k))

/-- The pointwise explicit plaquette-variance lower bound along a trajectory. -/
theorem Z2PeriodicHypercubicPlaquetteTrajectory.explicit_gibbsVariance_lower
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (k : ℕ) :
    Real.exp (-(6 * T.beta k)) / 8 ≤ T.gibbsVariance k := by
  have hPos : 0 < T.sideLength k :=
    lt_of_lt_of_le (by norm_num) (T.sideLength_ge_two k)
  letI : NeZero (T.sideLength k) := ⟨Nat.ne_of_gt hPos⟩
  unfold Z2PeriodicHypercubicPlaquetteTrajectory.gibbsVariance
  exact z2PeriodicHypercubicPlaquetteEnergyObservable_gibbsVarianceReal_lower
    (T.sideLength k) (T.sideLength_ge_two k)
    (T.beta k) (T.beta_nonneg k) (T.plaquette k)

/-- An upper bound on the coupling trajectory produces one positive variance
constant that is uniform in the lattice scale. -/
theorem Z2PeriodicHypercubicPlaquetteTrajectory.uniform_gibbsVariance_lower_of_beta_le
    (T : Z2PeriodicHypercubicPlaquetteTrajectory)
    (B : ℝ)
    (hBetaLe : ∀ k, T.beta k ≤ B)
    (k : ℕ) :
    Real.exp (-(6 * B)) / 8 ≤ T.gibbsVariance k := by
  calc
    Real.exp (-(6 * B)) / 8 ≤ Real.exp (-(6 * T.beta k)) / 8 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact Real.exp_le_exp.mpr (by nlinarith [hBetaLe k])
    _ ≤ T.gibbsVariance k := T.explicit_gibbsVariance_lower k

/-- The bounded-coupling trajectory lower bound is strictly positive. -/
theorem z2PeriodicHypercubic_boundedCoupling_varianceLower_pos
    (B : ℝ) :
    0 < Real.exp (-(6 * B)) / 8 :=
  div_pos (Real.exp_pos _) (by norm_num)

/-- Data identifying the finite periodic `Z₂` plaquette variances with the
approximating variances of one bounded continuous observable on a common
physical Polish carrier.

The equality field is the remaining interpolation/observable-compatibility
obligation.  No such interpolation is manufactured by this structure. -/
structure Z2PeriodicHypercubicPlaquetteWeakLimitRealization
    (S : PhysicalFourDimensionalYangMillsWeakLimit) where
  trajectory : Z2PeriodicHypercubicPlaquetteTrajectory
  observable : BoundedContinuousFunction S.Configuration ℝ
  betaUpper : ℝ
  beta_le : ∀ k, trajectory.beta k ≤ betaUpper
  approximating_variance_eq :
    ∀ k, S.approximatingObservableVariance k observable =
      trajectory.gibbsVariance k

/-- A bounded-coupling periodic `Z₂` plaquette realization on a common physical
carrier yields the generic observable nontriviality certificate. -/
noncomputable def
    Z2PeriodicHypercubicPlaquetteWeakLimitRealization.toObservableNontrivialityCertificate
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    (R : Z2PeriodicHypercubicPlaquetteWeakLimitRealization S) :
    S.ObservableNontrivialityCertificate :=
  { observable := R.observable
    lowerBound := Real.exp (-(6 * R.betaUpper)) / 8
    lowerBound_pos :=
      z2PeriodicHypercubic_boundedCoupling_varianceLower_pos R.betaUpper
    approximating_variance_ge := by
      intro k
      rw [R.approximating_variance_eq k]
      exact R.trajectory.uniform_gibbsVariance_lower_of_beta_le
        R.betaUpper R.beta_le k }

/-- Hence the continuum observable variance is strictly positive whenever the
bounded-coupling realization and weak convergence are supplied. -/
theorem Z2PeriodicHypercubicPlaquetteWeakLimitRealization.continuum_variance_pos
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    (R : Z2PeriodicHypercubicPlaquetteWeakLimitRealization S) :
    0 < S.continuumObservableVariance R.observable :=
  R.toObservableNontrivialityCertificate.continuum_variance_pos

/-- The realized continuum plaquette observable cannot collapse almost
everywhere to any constant. -/
theorem Z2PeriodicHypercubicPlaquetteWeakLimitRealization.observable_not_ae_eq_const
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    (R : Z2PeriodicHypercubicPlaquetteWeakLimitRealization S)
    (c : ℝ) :
    ¬ (fun A : S.Configuration => R.observable A) =ᵐ[
        (S.continuumMeasure : MeasureTheory.Measure S.Configuration)]
      (fun _ => c) :=
  R.toObservableNontrivialityCertificate.observable_not_ae_eq_const c

end

end MathlibAnalytic
end MGAP4D
