import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonVacuumNormalizedH1D5TwoModeHalfWeightPositiveDensity
import Mathlib.Tactic

/-!
# H1-D5 residual as a positive-density temporal-crossing Gram determinant

PR #5046 isolated the temporal-gauge crossing kernel, leaving one positive
spatial half-Boltzmann factor at each endpoint. PR #5047 proved that this
half-weight is an everywhere-positive finite Haar density.

This file performs the exact measure change. The two endpoint half-weights are
moved completely into the endpoint measures. Thus the remaining H1-D5 scalar
obstruction is a 2 x 2 Gram determinant for the bare temporal-crossing kernel
under an equivalent positive reweighting of spatial-slice Haar.

No crossing-kernel strictness is assumed or proved here. After this rewrite,
that strictness is the only model-specific residual.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance h1d5PositiveDensityCrossingTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance h1d5PositiveDensityCrossingCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance h1d5PositiveDensityCrossingSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance h1d5PositiveDensityCrossingMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance h1d5PositiveDensityCrossingBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance h1d5PositiveDensityCrossingSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance h1d5PositiveDensityCrossingSpatialHaarProbability (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Spatial-slice Haar tilted by the literal positive half-Boltzmann weight. -/
noncomputable def periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure
    (H N : ℕ)
    (beta : ℝ) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).withDensity
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta)

/-- The half-weighted spatial measure is finite at nonnegative coupling. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure_isFiniteMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    IsFiniteMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H N beta) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure
  exact
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_isFiniteMeasure
      H N hN beta hbeta

/-- The independent pair of half-weighted endpoint measures is exactly
product-Haar tilted by the product of the two half-weight densities. -/
theorem periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure_prod
    (H N : ℕ)
    (beta : ℝ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H N beta).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H N beta) =
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N).withDensity
        (fun p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta p.1 *
            periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta p.2) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let w := periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta
  have hw : Measurable w := by
    simpa [w] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_measurable
        H N beta
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  simpa [μ, w] using prod_withDensity hw hw

/-- Bare temporal-crossing coefficient of the two explicit physical Wilson
modes under the positive half-weight endpoint measure. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingCoefficient
    (H N : ℕ)
    (_hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (_hbeta : 0 ≤ beta)
    (i j : Fin 2) : ℝ :=
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H N beta
  let ui : Lp ℝ 2 μ :=
    (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
      H hN2 i :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
  let uj : Lp ℝ 2 μ :=
    (periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
      H hN2 j :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
  ∫ p :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H N beta p.1 p.2 *
      ui p.1 * uj p.2
    ∂(ν.prod ν)

/-- Exact endpoint-density rewrite: the #5046 half-weighted crossing
coefficient is the bare crossing coefficient under the positive endpoint
measure. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient_eq_positiveDensityCrossingCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (i j : Fin 2) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient
        H N hN hN2 beta hbeta i j =
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingCoefficient
        H N hN hN2 beta hbeta i j := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let w := periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta
  let ν := periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure H N beta
  have hw : Measurable w := by
    simpa [w] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_measurable
        H N beta
  have hpairMeas :
      Measurable
        (fun p :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          w p.1 * w p.2) :=
    (hw.comp measurable_fst).mul (hw.comp measurable_snd)
  have hpairTop :
      ∀ᵐ p ∂(μ.prod μ), w p.1 * w p.2 < (⊤ : ENNReal) := by
    filter_upwards with p
    dsimp [w]
    calc
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta p.1 *
          periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity H N beta p.2 ≤
          1 * 1 := by
        exact mul_le_mul'
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_le_one
            H N hN beta hbeta p.1)
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity_le_one
            H N hN beta hbeta p.2)
      _ < (⊤ : ENNReal) := by simp
  have hprod :
      ν.prod ν =
        (μ.prod μ).withDensity
          (fun p :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            w p.1 * w p.2) := by
    simpa [ν, μ, w,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightMeasure_prod
        H N beta
  unfold
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient
  unfold
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingCoefficient
  change
    (∫ p,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
          H N beta p.1 p.2 *
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
          H N beta p.1 *
          ((periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
            H hN2 i :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 μ) p.1) *
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight
          H N beta p.2 *
          ((periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
            H hN2 j :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
            Lp ℝ 2 μ) p.2)
      ∂(μ.prod μ)) =
    ∫ p,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
          H N beta p.1 p.2 *
        ((periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 i :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 μ) p.1 *
        ((periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalL2
          H hN2 j :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
          Lp ℝ 2 μ) p.2
      ∂(ν.prod ν)
  rw [hprod]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hpairMeas.aemeasurable hpairTop]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [smul_eq_mul]
  dsimp [w, periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeightDensity]
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
        H N beta p.1).le,
    ENNReal.toReal_ofReal
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight_pos
        H N beta p.2).le]
  ring

/-- The 2 x 2 crossing Gram determinant after all endpoint half-weights have
been moved into the equivalent positive endpoint measure. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingGramDet
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) : ℝ :=
  periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingCoefficient
      H N hN hN2 beta hbeta 0 0 *
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingCoefficient
      H N hN hN2 beta hbeta 1 1 -
  periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingCoefficient
      H N hN hN2 beta hbeta 0 1 *
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingCoefficient
      H N hN hN2 beta hbeta 1 0

/-- Exact determinant bridge from #5046 to the positive-density crossing Gram. -/
theorem
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingGramDet_eq_positiveDensityCrossingGramDet
    (H N : ℕ)
    (hN : 0 < N)
    (hN2 : 2 ≤ N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingGramDet
        H N hN hN2 beta hbeta =
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingGramDet
        H N hN hN2 beta hbeta := by
  unfold
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingGramDet
  unfold
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingGramDet
  rw [
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient_eq_positiveDensityCrossingCoefficient
      H N hN hN2 beta hbeta 0 0,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient_eq_positiveDensityCrossingCoefficient
      H N hN hN2 beta hbeta 1 1,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient_eq_positiveDensityCrossingCoefficient
      H N hN hN2 beta hbeta 0 1,
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingCoefficient_eq_positiveDensityCrossingCoefficient
      H N hN hN2 beta hbeta 1 0]

section H1D5PositiveDensityCrossing

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    {hN2 : 2 ≤ N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta
        Q.vacuumNormalized.toWeakStarBridge hInvariant)

/-- A nonzero positive-density temporal-crossing two-mode determinant at one
finite scale refutes H1-D5. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_positiveDensityCrossingGramDet_ne_zero
    (n : ℕ)
    (hne :
      periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingGramDet
        (halfExtent n) N hN hN2 (beta n) (hbeta n) ≠ 0) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  apply
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_halfWeightedCrossingGramDet_ne_zero
      (hN2 := hN2) Q hInvariant C n
  rwa [
    periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalHalfWeightedCrossingGramDet_eq_positiveDensityCrossingGramDet
      (halfExtent n) N hN hN2 (beta n) (hbeta n)]

/-- Strict positivity of the same positive-density crossing determinant is a
convenient sufficient witness. -/
theorem
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_positiveDensityCrossingGramDet_pos
    (n : ℕ)
    (hpos :
      0 <
        periodicHypercubicEvenPrimarySpatialSliceWilsonTwoModePhysicalPositiveDensityCrossingGramDet
          (halfExtent n) N hN hN2 (beta n) (hbeta n)) :
    ¬ PhysicalYangMillsSUNTwoModeExplicitOSVacuumPairCompletedTransferCompatibility
        (S := S) (D := D) (halfExtent := halfExtent)
        (N := N) (hN := hN)
        (beta := beta) (hbeta := hbeta)
        (Q := Q.vacuumNormalized) (hInvariant := hInvariant) C := by
  exact
    physicalYangMillsVacuumNormalizedSUNTwoMode_not_completedCompatibility_of_positiveDensityCrossingGramDet_ne_zero
      (hN2 := hN2) Q hInvariant C n hpos.ne'

end H1D5PositiveDensityCrossing

end

end MathlibAnalytic
end MGAP4D
