import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanGibbsExpectation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Gibbs mean absolute deviation of a real observable on oriented physical-link
configurations. -/
def FiniteOrientedLatticeWilsonSystem.gibbsMeanAbsoluteDeviationReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℝ := by
  classical
  exact ∑ A : L.Configuration,
    L.gibbsProbabilityReal A * |f A - L.gibbsExpectationReal f|

/-- Stationary random-scan temporal covariance.  The second observable is
advanced by `k` random-scan heat-bath steps while the first remains at time
zero. -/
def FiniteOrientedLatticeWilsonSystem.randomScanTemporalCovarianceReal
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ)
    (k : ℕ) : ℝ :=
  L.gibbsPairingReal
    (fun A => f A - L.gibbsExpectationReal f)
    (fun A => L.randomScanConditionalAverageIterate g k A -
      L.gibbsExpectationReal g)

/-- A uniform pointwise bound on the centered time-`k` observable controls its
stationary temporal covariance by the mean absolute deviation of the time-zero
observable. -/
theorem finite_oriented_randomScanTemporalCovarianceReal_abs_le_mad_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ)
    (k : ℕ)
    (M : ℝ)
    (hBound : ∀ A : L.Configuration,
      |L.randomScanConditionalAverageIterate g k A -
        L.gibbsExpectationReal g| ≤ M) :
    |L.randomScanTemporalCovarianceReal f g k| ≤
      L.gibbsMeanAbsoluteDeviationReal f * M := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.randomScanTemporalCovarianceReal
    FiniteOrientedLatticeWilsonSystem.gibbsMeanAbsoluteDeviationReal
    FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  calc
    |∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          (f A - L.gibbsExpectationReal f) *
          (L.randomScanConditionalAverageIterate g k A -
            L.gibbsExpectationReal g)| ≤
      ∑ A : L.Configuration,
        |L.gibbsProbabilityReal A *
          (f A - L.gibbsExpectationReal f) *
          (L.randomScanConditionalAverageIterate g k A -
            L.gibbsExpectationReal g)| :=
      finite_abs_sum_le_sum_abs Finset.univ
        (fun A : L.Configuration =>
          L.gibbsProbabilityReal A *
            (f A - L.gibbsExpectationReal f) *
            (L.randomScanConditionalAverageIterate g k A -
              L.gibbsExpectationReal g))
    _ = ∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          |f A - L.gibbsExpectationReal f| *
          |L.randomScanConditionalAverageIterate g k A -
            L.gibbsExpectationReal g| := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [abs_mul, abs_mul,
        abs_of_nonneg (finite_oriented_gibbsProbabilityReal_nonneg L A)]
    _ ≤ ∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          |f A - L.gibbsExpectationReal f| * M := by
      apply Finset.sum_le_sum
      intro A _hA
      exact mul_le_mul_of_nonneg_left
        (hBound A)
        (mul_nonneg
          (finite_oriented_gibbsProbabilityReal_nonneg L A)
          (abs_nonneg _))
    _ = (∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          |f A - L.gibbsExpectationReal f|) * M := by
      rw [Finset.sum_mul]

/-- Dobrushin random-scan contraction gives geometric decay of stationary
temporal covariance. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanTemporalCovarianceReal_abs_le_mad_mul_pow_sum
    {L : FiniteOrientedLatticeWilsonSystem}
    {g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (f : L.Configuration → ℝ)
    (k : ℕ) :
    |L.randomScanTemporalCovarianceReal f g k| ≤
      L.gibbsMeanAbsoluteDeviationReal f *
        ((finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k *
          ∑ source : L.Edge, P.variation source) := by
  apply finite_oriented_randomScanTemporalCovarianceReal_abs_le_mad_mul
  intro A
  exact
    P.randomScanConditionalAverageIterate_abs_sub_gibbsExpectation_le_pow_mul_sum
      D hEdge k A

/-- Under a unit plaquette-energy bound, one plaquette observable has Gibbs
mean absolute deviation at most one. -/
theorem
    FiniteOrientedLatticeWilsonPlaquetteEnergyUnitBound.gibbsMeanAbsoluteDeviationReal_plaquette_le_one
    {L : FiniteOrientedLatticeWilsonSystem}
    (U : FiniteOrientedLatticeWilsonPlaquetteEnergyUnitBound L)
    (p : L.Plaquette) :
    L.gibbsMeanAbsoluteDeviationReal (L.plaquetteObservable p) ≤ 1 := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsMeanAbsoluteDeviationReal
  calc
    (∑ A : L.Configuration,
      L.gibbsProbabilityReal A *
        |L.plaquetteObservable p A -
          L.gibbsExpectationReal (L.plaquetteObservable p)|) ≤
      ∑ A : L.Configuration, L.gibbsProbabilityReal A * 1 := by
        apply Finset.sum_le_sum
        intro A _hA
        apply mul_le_mul_of_nonneg_left
        · apply finite_oriented_abs_sub_gibbsExpectationReal_le_of_pairwise
          intro B
          exact finite_oriented_abs_plaquetteObservable_sub_le_one
            L U p A B
        · exact finite_oriented_gibbsProbabilityReal_nonneg L A
    _ = ∑ A : L.Configuration, L.gibbsProbabilityReal A := by
      apply Finset.sum_congr rfl
      intro A _hA
      ring
    _ = 1 := by
      simpa [FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal] using
        (finite_pmf_sum_toReal_eq_one L.gibbsPMF)

/-- For a periodic `Z₂` target plaquette, stationary temporal covariance with an
arbitrary time-zero observable decays at the same `4 q^k` rate, multiplied by
that observable's Gibbs mean absolute deviation. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteRandomScanTemporalCovariance_abs_le_mad_mul_four_mul_pow
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta))
    (f :
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).Configuration → ℝ)
    (k : ℕ) :
    |FiniteOrientedLatticeWilsonSystem.randomScanTemporalCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        f
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) target)
        k| ≤
      FiniteOrientedLatticeWilsonSystem.gibbsMeanAbsoluteDeviationReal
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) f *
        (4 *
          (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k) := by
  apply finite_oriented_randomScanTemporalCovarianceReal_abs_le_mad_mul
  intro A
  exact
    z2PeriodicHypercubicOrientedPlaquetteRandomScanObservableIterate_abs_sub_gibbsExpectation_le_four_mul_pow
      n beta hBeta target D k A

/-- Any two selected periodic `Z₂` plaquette observables have stationary
random-scan temporal covariance bounded by `4 q^k`.  This is a temporal bound;
it does not encode the spatial distance between the plaquettes. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteRandomScanTemporalCovariance_abs_le_four_mul_pow
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (source target : PeriodicHypercubicPlaquette n)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta))
    (k : ℕ) :
    |FiniteOrientedLatticeWilsonSystem.randomScanTemporalCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) source)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) target)
        k| ≤
      4 *
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k := by
  have hEdge : 0 < Fintype.card (PeriodicHypercubicEdge n) :=
    Fintype.card_pos_iff.mpr ⟨((fun _ => 0), 0)⟩
  have hCov :=
    z2PeriodicHypercubicOrientedPlaquetteRandomScanTemporalCovariance_abs_le_mad_mul_four_mul_pow
      n beta hBeta target D
      (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) source) k
  have hMad :=
    (z2PeriodicHypercubicOrientedPlaquetteEnergyUnitBound n beta hBeta)
      |>.gibbsMeanAbsoluteDeviationReal_plaquette_le_one source
  have hRateNonneg :
      0 ≤ 4 *
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k :=
    mul_nonneg (by norm_num)
      (pow_nonneg
        (finiteOrientedConditionalAverageRandomScanContractionFactor_nonneg
          D hEdge) k)
  calc
    |FiniteOrientedLatticeWilsonSystem.randomScanTemporalCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) source)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) target)
        k| ≤
      FiniteOrientedLatticeWilsonSystem.gibbsMeanAbsoluteDeviationReal
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
            (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta) source) *
        (4 *
          (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k) :=
      hCov
    _ ≤ 1 *
        (4 *
          (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k) :=
      mul_le_mul_of_nonneg_right hMad hRateNonneg
    _ = 4 *
        (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k := by
      ring

end

end MathlibAnalytic
end MGAP4D
