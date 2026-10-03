import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeHalfWeightedCrossingGram
import Mathlib.Tactic

/-!
# Spatial half-weight as an equivalent positive Haar density

#5046 rewrites the remaining H1-D5 two-mode scalar obstruction as the
temporal-crossing kernel with one spatial half-Boltzmann factor absorbed at
each endpoint.

The next Fock-strictness layers in this repository are formulated for
arbitrary finite positive changes of Haar density. This file puts the #5046
half-weight into exactly that form.

No strict-positivity conclusion for the crossing Gram is asserted here. The
content is measure-theoretic only:

* the spatial half-weight gives a measurable ENNReal density;
* the density is everywhere nonzero and finite;
* for nonnegative coupling it is bounded by one, hence its Haar tilt is finite;
* the tilted measure and spatial-slice Haar have the same null sets;
* Bochner integration against the tilted measure is exactly multiplication by
  the literal spatial half-weight followed by Haar integration.

Thus the remaining model-specific step can use the existing positive-density
Wilson/Fock machinery without hiding the endpoint reweighting.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance h1d5HalfWeightDensityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5HalfWeightDensityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5HalfWeightDensitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5HalfWeightDensityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5HalfWeightDensityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5HalfWeightDensitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5HalfWeightDensitySpatialHaarProbability (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The literal spatial half-Boltzmann amplitude, viewed as an ENNReal
Radon--Nikodym density over spatial-slice Haar. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
    (H N : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ENNReal :=
  ENNReal.ofReal
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta A)

/-- The half-weight density is measurable. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_measurable
    (H N : ℕ)
    (beta : ℝ) :
    Measurable
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
        H N beta) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
  exact
    (ENNReal.continuous_ofReal.comp
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_continuous
        H N beta)).measurable

/-- The half-weight density is everywhere nonzero. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_ne_zero
    (H N : ℕ)
    (beta : ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
        H N beta A ≠ 0 := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
  rw [ENNReal.ofReal_ne_zero_iff]
  exact
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
      H N beta A

/-- The half-weight itself is at most one for nonnegative coupling. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta A ≤ 1 := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
  rw [Real.exp_le_one_iff]
  exact
    mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg hbeta (by norm_num)))
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
        H N hN A)

/-- Consequently the ENNReal density is bounded by one. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta A ≤ 1 := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
  simpa using
    ENNReal.ofReal_le_ofReal
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_le_one
        H N hN beta hbeta A)

/-- The half-weight density has finite Haar mass. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_lintegral_ne_top
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (∫⁻ A,
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
        H N beta A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ≠ ⊤ := by
  have hle :
      (∫⁻ A,
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
          H N beta A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ≤
        1 := by
    calc
      (∫⁻ A,
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
          H N beta A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) ≤
          ∫⁻ _ :
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            (1 : ENNReal)
            ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
              apply lintegral_mono
              intro A
              exact
                periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_le_one
                  H N hN beta hbeta A
      _ = 1 := by simp
  exact ne_top_of_le_ne_top (by simp) hle

/-- Spatial Haar tilted by the literal half-weight is a finite measure. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_isFiniteMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsFiniteMeasure
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).withDensity
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
          H N beta)) := by
  exact isFiniteMeasure_withDensity
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_lintegral_ne_top
      H N hN beta hbeta)

/-- The positive half-weight tilt is absolutely continuous with respect to
spatial Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_withDensity_absolutelyContinuous
    (H N : ℕ)
    (beta : ℝ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).withDensity
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta) ≪
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  exact withDensity_absolutelyContinuous _ _

/-- Because the half-weight is everywhere positive, spatial Haar is also
absolutely continuous with respect to the tilted measure. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_absolutelyContinuous_halfWeight
    (H N : ℕ)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N ≪
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).withDensity
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta) := by
  exact
    withDensity_absolutelyContinuous'
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_measurable
        H N beta).aemeasurable
      (Filter.Eventually.of_forall
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_ne_zero
          H N beta))

/-- Bochner integration against the half-weighted Haar measure is literally
Haar integration after multiplication by the spatial half-weight. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_integral_withDensity
    (H N : ℕ)
    (beta : ℝ)
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → E) :
    (∫ A, f A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).withDensity
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta)) =
      ∫ A,
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta A • f A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  have htop :
      ∀ᵐ A ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
          H N beta A < ⊤ := by
    filter_upwards with A
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
    exact ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_measurable
      H N beta).aemeasurable htop]
  apply integral_congr_ae
  filter_upwards with A
  congr 1
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity
  rw [ENNReal.toReal_ofReal
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
      H N beta A).le]

/-- Scalar specialization of the same density identity. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_integral_withDensity_real
    (H N : ℕ)
    (beta : ℝ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ) :
    (∫ A, f A
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).withDensity
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta)) =
      ∫ A,
        periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H N beta A * f A
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  simpa [smul_eq_mul] using
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_integral_withDensity
      H N beta f

end

end MathlibAnalytic
end MGAP4D
