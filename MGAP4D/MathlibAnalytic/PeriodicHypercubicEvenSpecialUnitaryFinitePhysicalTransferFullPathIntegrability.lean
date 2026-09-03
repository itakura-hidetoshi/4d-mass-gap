import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferFullPathBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finitePhysicalTransferFullPathIntegrabilityTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finitePhysicalTransferFullPathIntegrabilityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finitePhysicalTransferFullPathIntegrabilitySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finitePhysicalTransferFullPathIntegrabilityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finitePhysicalTransferFullPathIntegrabilityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finitePhysicalTransferFullPathIntegrabilitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For physical Haar-`L²` endpoint vectors and nonnegative coupling, the
complete two-ended finite temporal-gauge path integrand is automatically
Bochner integrable.  No separate path-integrability hypothesis is needed:
the path Wilson factor has absolute value at most one, while the two endpoint
factors are controlled by their pulled-back `L²` squares. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand_integrable
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand h N beta f g)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (h + 1) N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N
  let ρ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (h + 1) N
  let fL2 : Lp ℝ 2 μ := f
  let gL2 : Lp ℝ 2 μ := g
  have hfSq : Integrable (fun A => ‖fL2 A‖ ^ 2) μ := by
    exact
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable fL2)).1
        (Lp.memLp fL2)
  have hgSq : Integrable (fun A => ‖gL2 A‖ ^ 2) μ := by
    exact
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable gL2)).1
        (Lp.memLp gL2)
  have hEvalZero : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (h + 1) N =>
        path 0) ρ μ := by
    simpa [ρ, μ,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) + 1) => μ)
        (0 : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) + 1)))
  have hEvalLast : MeasurePreserving
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (h + 1) N =>
        path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1)))) ρ μ := by
    simpa [ρ, μ,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1) + 1) => μ)
        (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1))))
  have hfSqPath : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (h + 1) N =>
        ‖fL2 (path 0)‖ ^ 2) ρ := by
    simpa [Function.comp_def] using hEvalZero.integrable_comp_of_integrable hfSq
  have hgSqPath : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (h + 1) N =>
        ‖gL2 (path (Fin.last
          (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1))))‖ ^ 2) ρ := by
    simpa [Function.comp_def] using hEvalLast.integrable_comp_of_integrable hgSq
  have hdom : Integrable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (h + 1) N =>
        ‖fL2 (path 0)‖ ^ 2 +
          ‖gL2 (path (Fin.last
            (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1))))‖ ^ 2) ρ :=
    hfSqPath.add hgSqPath
  have hkMeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (h + 1) N beta) ρ := by
    unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
    refine Finset.aestronglyMeasurable_fun_prod Finset.univ ?_
    intro i hi
    exact
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        (h + 1) N beta).aestronglyMeasurable.comp_measurable (by fun_prop)
  have hfMeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (h + 1) N =>
        fL2 (path 0)) ρ :=
    (hEvalZero.integrable_comp_of_integrable
      ((Lp.memLp fL2).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2) |>
        (memLp_one_iff_integrable.mp))).aestronglyMeasurable
  have hgMeas : AEStronglyMeasurable
      (fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (h + 1) N =>
        gL2 (path (Fin.last
          (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1))))) ρ :=
    (hEvalLast.integrable_comp_of_integrable
      ((Lp.memLp gL2).mono_exponent (by norm_num : (1 : ENNReal) ≤ 2) |>
        (memLp_one_iff_integrable.mp))).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand h N beta f g) ρ := by
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand
    change AEStronglyMeasurable
      (fun path => fL2 (path 0) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          (h + 1) N beta path *
        gL2 (path (Fin.last
          (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1))))) ρ
    exact continuous_mul.comp_aestronglyMeasurable₂
      (continuous_mul.comp_aestronglyMeasurable₂ hfMeas hkMeas) hgMeas
  apply hdom.mono' hmeas
  filter_upwards with path
  have hk :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_abs_le_one
      (h + 1) N hN beta hbeta path
  let a := ‖fL2 (path 0)‖
  let b := ‖gL2 (path (Fin.last
    (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1))))‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hkab :
      ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
          (h + 1) N beta path‖ ≤ 1 := by
    simpa [Real.norm_eq_abs] using hk
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand
  change ‖fL2 (path 0) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (h + 1) N beta path *
      gL2 (path (Fin.last
        (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1))))‖ ≤
    a ^ 2 + b ^ 2
  rw [norm_mul, norm_mul]
  calc
    ‖fL2 (path 0)‖ *
          ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
            (h + 1) N beta path‖ *
        ‖gL2 (path (Fin.last
          (periodicHypercubicEvenPositiveHalfCylinderSlabCount (h + 1))))‖ ≤
        a * 1 * b := by
      dsimp [a, b]
      gcongr
    _ ≤ a ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg (a - b)]

/-- The full finite temporal-gauge path integral is therefore the literal
adjacent-slab Wilson amplitude with no external integrability premise. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude_eq_literal_of_nonnegativeCoupling
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude h N beta f g =
      periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude h N beta f g := by
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude_eq_literal
      h N beta f g
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathIntegrand_integrable
        h N hN beta hbeta f g)

/-- The complete finite temporal-gauge path amplitude is exactly the actual
physical two-ended transfer recursion.  This closes the finite Markov/Fubini
bridge without an auxiliary path-integrability assumption. -/
theorem periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude_eq_projectedPhysicalRecursion
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude h N beta f g =
      periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude
        h N hN beta hbeta f g := by
  calc
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude h N beta f g =
        periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude h N beta f g :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeTwoEndedPathAmplitude_eq_literal_of_nonnegativeCoupling
        h N hN beta hbeta f g
    _ = periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude
        h N hN beta hbeta f g :=
      (periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude_eq_literal
        h N hN beta hbeta f g).symm

end

end MathlibAnalytic
end MGAP4D
