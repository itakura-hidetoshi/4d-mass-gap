import MGAP4D.MathlibAnalytic.PhysicalYangMillsWeakLimitConnectedCorrelation
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance (k : ℕ) :
    NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) :=
  ⟨by
    unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume
    omega⟩

/-- The finite oriented Gibbs expectation is the Bochner integral against the
finite oriented Gibbs measure. -/
theorem finite_oriented_gibbsExpectationReal_eq_integral
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.gibbsExpectationReal f =
      ∫ A, f A ∂L.gibbsMeasure := by
  classical
  rw [FiniteOrientedLatticeWilsonSystem.gibbsMeasure,
    PMF.integral_eq_sum]
  unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
    FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
  simp only [smul_eq_mul]

/-- The native Gibbs pairing is expectation of the pointwise product. -/
theorem finite_oriented_gibbsPairingReal_eq_expectation_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f g =
      L.gibbsExpectationReal (fun A => f A * g A) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Finite oriented Gibbs expectation preserves subtraction. -/
theorem finite_oriented_gibbsExpectationReal_sub
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsExpectationReal (fun A => f A - g A) =
      L.gibbsExpectationReal f - L.gibbsExpectationReal g := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
  calc
    (∑ A : L.Configuration,
        L.gibbsProbabilityReal A * (f A - g A)) =
      ∑ A : L.Configuration,
        (L.gibbsProbabilityReal A * f A -
          L.gibbsProbabilityReal A * g A) := by
      apply Finset.sum_congr rfl
      intro A _hA
      ring
    _ =
      (∑ A : L.Configuration, L.gibbsProbabilityReal A * f A) -
        ∑ A : L.Configuration, L.gibbsProbabilityReal A * g A := by
      rw [Finset.sum_sub_distrib]

/-- Finite oriented Gibbs expectation preserves right scalar multiplication. -/
theorem finite_oriented_gibbsExpectationReal_mul_const
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (c : ℝ) :
    L.gibbsExpectationReal (fun A => f A * c) =
      L.gibbsExpectationReal f * c := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
  calc
    (∑ A : L.Configuration,
        L.gibbsProbabilityReal A * (f A * c)) =
      ∑ A : L.Configuration,
        (L.gibbsProbabilityReal A * f A) * c := by
      apply Finset.sum_congr rfl
      intro A _hA
      ring
    _ =
      (∑ A : L.Configuration,
        L.gibbsProbabilityReal A * f A) * c := by
      rw [Finset.sum_mul]

/-- Finite oriented Gibbs expectation preserves left scalar multiplication. -/
theorem finite_oriented_gibbsExpectationReal_const_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (c : ℝ)
    (f : L.Configuration → ℝ) :
    L.gibbsExpectationReal (fun A => c * f A) =
      c * L.gibbsExpectationReal f := by
  simpa [mul_comm] using
    finite_oriented_gibbsExpectationReal_mul_const L f c

/-- The expectation of a constant under the normalized finite Gibbs law is the
constant. -/
theorem finite_oriented_gibbsExpectationReal_const
    (L : FiniteOrientedLatticeWilsonSystem)
    (c : ℝ) :
    L.gibbsExpectationReal (fun _ : L.Configuration => c) = c := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsExpectationReal
  calc
    (∑ A : L.Configuration, L.gibbsProbabilityReal A * c) =
      (∑ A : L.Configuration, L.gibbsProbabilityReal A) * c := by
      rw [Finset.sum_mul]
    _ = 1 * c := by
      congr 1
      simpa [FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal] using
        finite_oriented_pmf_sum_toReal_eq_one L.gibbsPMF
    _ = c := by ring

/-- Static Gibbs covariance is expectation of the product minus the product of
expectations. -/
theorem finite_oriented_gibbsCovarianceReal_eq_expectation_mul_sub_mul
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsCovarianceReal f g =
      L.gibbsExpectationReal (fun A => f A * g A) -
        L.gibbsExpectationReal f * L.gibbsExpectationReal g := by
  rw [FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal,
    finite_oriented_gibbsPairingReal_eq_expectation_mul]
  let Ef : ℝ := L.gibbsExpectationReal f
  let Eg : ℝ := L.gibbsExpectationReal g
  change
    L.gibbsExpectationReal
        (fun A => (f A - Ef) * (g A - Eg)) =
      L.gibbsExpectationReal (fun A => f A * g A) - Ef * Eg
  calc
    L.gibbsExpectationReal
        (fun A => (f A - Ef) * (g A - Eg)) =
      L.gibbsExpectationReal
        (fun A =>
          (f A * g A - f A * Eg) -
            (Ef * g A - Ef * Eg)) := by
      congr 1
      funext A
      ring
    _ =
      (L.gibbsExpectationReal (fun A => f A * g A) -
          L.gibbsExpectationReal (fun A => f A * Eg)) -
        (L.gibbsExpectationReal (fun A => Ef * g A) -
          L.gibbsExpectationReal (fun _ => Ef * Eg)) := by
      rw [finite_oriented_gibbsExpectationReal_sub,
        finite_oriented_gibbsExpectationReal_sub,
        finite_oriented_gibbsExpectationReal_sub]
    _ =
      (L.gibbsExpectationReal (fun A => f A * g A) -
          L.gibbsExpectationReal f * Eg) -
        (Ef * L.gibbsExpectationReal g - Ef * Eg) := by
      rw [finite_oriented_gibbsExpectationReal_mul_const,
        finite_oriented_gibbsExpectationReal_const_mul,
        finite_oriented_gibbsExpectationReal_const]
    _ =
      L.gibbsExpectationReal (fun A => f A * g A) - Ef * Eg := by
      dsimp [Ef, Eg]
      ring

/-- Static finite Gibbs covariance written entirely as integrals against the
finite Gibbs measure. -/
theorem finite_oriented_gibbsCovarianceReal_eq_integral_sub_mul_integral
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsCovarianceReal f g =
      (∫ A, f A * g A ∂L.gibbsMeasure) -
        (∫ A, f A ∂L.gibbsMeasure) *
          ∫ A, g A ∂L.gibbsMeasure := by
  rw [finite_oriented_gibbsCovarianceReal_eq_expectation_mul_sub_mul,
    finite_oriented_gibbsExpectationReal_eq_integral,
    finite_oriented_gibbsExpectationReal_eq_integral,
    finite_oriented_gibbsExpectationReal_eq_integral]

/-- Concrete interpolation data identifying periodic finite-volume `Z₂`
plaquette observables with two bounded continuous observables on a common
physical weak-limit carrier.

The bridge records the actual pushforward identity for the approximating
measures and pointwise pullback identities for both plaquette observables. -/
structure PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ) where
  interpolate :
    ∀ k : ℕ,
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        beta hBeta.le).Configuration →
      S.Configuration
  interpolate_measurable :
    ∀ k : ℕ, Measurable (interpolate k)
  approximatingMeasure_eq_map :
    ∀ k : ℕ,
      (S.approximatingMeasure k : Measure S.Configuration) =
        Measure.map (interpolate k)
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le).gibbsMeasure
  sourceObservable : BoundedContinuousFunction S.Configuration ℝ
  targetObservable : BoundedContinuousFunction S.Configuration ℝ
  sourcePlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
  targetPlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
  distance_eq :
    ∀ k : ℕ,
      periodicHypercubicPlaquetteBaseL1Distance
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          (sourcePlaquette k)
          (targetPlaquette k) =
        distance
  source_pullback :
    ∀ (k : ℕ)
      (A :
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).Configuration),
      sourceObservable (interpolate k A) =
        FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (sourcePlaquette k) A
  target_pullback :
    ∀ (k : ℕ)
      (A :
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).Configuration),
      targetObservable (interpolate k A) =
        FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (targetPlaquette k) A

/-- Integration against an approximating physical measure is integration of the
pullback against the corresponding finite periodic `Z₂` Gibbs measure. -/
theorem
    PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge.approximatingExpectation_eq_gibbs_pullback
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge
        S beta hBeta distance)
    (k : ℕ)
    (O : BoundedContinuousFunction S.Configuration ℝ) :
    (∫ A, O A
      ∂(S.approximatingMeasure k : Measure S.Configuration)) =
      ∫ U, O (B.interpolate k U)
        ∂(z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le).gibbsMeasure := by
  rw [B.approximatingMeasure_eq_map k]
  exact MeasureTheory.integral_map
    (B.interpolate_measurable k).aemeasurable
    O.continuous.aestronglyMeasurable

/-- The pushforward and pullback identities automatically identify the actual
finite plaquette covariance with the connected correlation of the common-space
approximating measure. -/
theorem
    PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge.finiteCovariance_eq
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge
        S beta hBeta distance)
    (k : ℕ) :
    FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          beta hBeta.le)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (B.sourcePlaquette k))
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (B.targetPlaquette k)) =
      S.approximatingConnectedCorrelation
        k B.sourceObservable B.targetObservable := by
  let L :=
    z2PeriodicHypercubicOrientedWilsonSystem
      (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
      beta hBeta.le
  let sourceFinite : L.Configuration → ℝ :=
    FiniteOrientedLatticeWilsonSystem.plaquetteObservable
      L (B.sourcePlaquette k)
  let targetFinite : L.Configuration → ℝ :=
    FiniteOrientedLatticeWilsonSystem.plaquetteObservable
      L (B.targetPlaquette k)
  have hProduct :=
    B.approximatingExpectation_eq_gibbs_pullback
      k (B.sourceObservable * B.targetObservable)
  have hSource :=
    B.approximatingExpectation_eq_gibbs_pullback
      k B.sourceObservable
  have hTarget :=
    B.approximatingExpectation_eq_gibbs_pullback
      k B.targetObservable
  simp_rw [B.source_pullback k, B.target_pullback k] at hProduct
  simp_rw [B.source_pullback k] at hSource
  simp_rw [B.target_pullback k] at hTarget
  change L.gibbsCovarianceReal sourceFinite targetFinite =
    S.approximatingConnectedCorrelation
      k B.sourceObservable B.targetObservable
  calc
    L.gibbsCovarianceReal sourceFinite targetFinite =
      (∫ U, sourceFinite U * targetFinite U ∂L.gibbsMeasure) -
        (∫ U, sourceFinite U ∂L.gibbsMeasure) *
          ∫ U, targetFinite U ∂L.gibbsMeasure :=
      finite_oriented_gibbsCovarianceReal_eq_integral_sub_mul_integral
        L sourceFinite targetFinite
    _ =
      S.approximatingConnectedCorrelation
        k B.sourceObservable B.targetObservable := by
      unfold PhysicalFourDimensionalYangMillsWeakLimit.approximatingConnectedCorrelation
      rw [hProduct, hSource, hTarget]

/-- The concrete interpolation bridge automatically supplies the weak-limit
covariance identification bridge introduced in the preceding layer. -/
noncomputable def
    PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge.toWeakLimitBridge
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (B :
      PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge
        S beta hBeta distance) :
    PhysicalYangMillsZ2PeriodicPlaquetteCovarianceWeakLimitBridge
      S beta hBeta distance :=
  { sourceObservable := B.sourceObservable
    targetObservable := B.targetObservable
    sourcePlaquette := B.sourcePlaquette
    targetPlaquette := B.targetPlaquette
    distance_eq := B.distance_eq
    finiteCovariance_eq := B.finiteCovariance_eq }

/-- Volume-uniform finite plaquette clustering passes to the continuum connected
correlation once the actual interpolation, pushforward, and pullback data are
provided. -/
theorem
    PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge.continuumConnectedCorrelation_abs_le
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta)
    (B :
      PhysicalYangMillsZ2PeriodicPlaquetteInterpolationBridge
        S beta hBeta distance) :
    |S.continuumConnectedCorrelation
        B.sourceObservable B.targetObservable| ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) :=
  B.toWeakLimitBridge.continuumConnectedCorrelation_abs_le K

end

end MathlibAnalytic
end MGAP4D
