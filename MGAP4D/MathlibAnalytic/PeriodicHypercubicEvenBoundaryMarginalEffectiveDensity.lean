import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentPositivity

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance boundaryEffectiveDensityNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryEffectiveDensityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryEffectiveDensityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryEffectiveDensitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryEffectiveDensityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryEffectiveDensityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The actual finite Wilson boundary marginal density with respect to boundary
Haar measure.  The earlier vacuum-moment theorem identifies this square exactly
with the result of integrating the boundary-fibered Gibbs density over both
open halves. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalEffectiveDensity
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) : ENNReal :=
  ENNReal.ofReal
    (periodicHypercubicEvenBoundaryVacuumMoment H N hN beta hbeta b ^ 2)

/-- The actual effective boundary density is measurable. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_measurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta) := by
  unfold periodicHypercubicEvenBoundaryMarginalEffectiveDensity
  exact ENNReal.continuous_ofReal.measurable.comp
    ((periodicHypercubicEvenBoundaryVacuumMoment_measurable
      H N hN beta hbeta).pow_const 2)

/-- Because the finite Wilson boundary vacuum wavefunction is pointwise
strictly positive, its squared ENNReal density never vanishes. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_ne_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    periodicHypercubicEvenBoundaryMarginalEffectiveDensity
      H N hN beta hbeta b ≠ 0 := by
  unfold periodicHypercubicEvenBoundaryMarginalEffectiveDensity
  rw [ENNReal.ofReal_ne_zero_iff]
  positivity

/-- Audit-friendly almost-everywhere form of the same nonvanishing statement,
ready for Mathlib's `withDensity_absolutelyContinuous'` API. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_ae_ne_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∀ᵐ b ∂(periodicHypercubicEvenBoundaryHaarMeasure H N),
      periodicHypercubicEvenBoundaryMarginalEffectiveDensity
        H N hN beta hbeta b ≠ 0 :=
  Filter.Eventually.of_forall
    (periodicHypercubicEvenBoundaryMarginalEffectiveDensity_ne_zero
      H N hN beta hbeta)

/-- Converting the effective density back to the reals recovers exactly the
square of the boundary vacuum moment. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_toReal
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
      H N hN beta hbeta b).toReal =
      periodicHypercubicEvenBoundaryVacuumMoment
        H N hN beta hbeta b ^ 2 := by
  unfold periodicHypercubicEvenBoundaryMarginalEffectiveDensity
  rw [ENNReal.toReal_ofReal]
  positivity

/-- The effective density is not merely an auxiliary definition: its real
value is exactly the actual Wilson Gibbs density after integrating out both
open halves at fixed boundary configuration. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveDensity_toReal_eq_openHalf_integrals
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :
    (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
      H N hN beta hbeta b).toReal =
      ∫ x, ∫ y,
        (periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
          H N hN beta hbeta (b, (x, y))).toReal
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  rw [periodicHypercubicEvenBoundaryMarginalEffectiveDensity_toReal]
  symm
  exact periodicHypercubicEvenBoundaryFiberedGibbsDensity_integral_eq_vacuumMoment_sq
    H N hN beta hbeta b

end

end MathlibAnalytic
end MGAP4D
