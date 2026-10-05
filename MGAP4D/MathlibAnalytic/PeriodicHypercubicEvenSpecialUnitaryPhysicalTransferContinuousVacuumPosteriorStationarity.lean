import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorSingleLinkFellerClosure
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Global stationarity of continuous-vacuum posterior one-link conditionals

PR #5160 closes every posterior one-link conditional expectation on the
bounded-continuous carrier. This file proves the missing global compatibility:
the posterior law is stationary under each literal posterior one-link
conditional expectation.

The proof uses only the actual spatial-slice Haar measure as a finite product
of normalized Haar probabilities, the generic one-coordinate product-Haar
averaging identity, the exact posterior fiber definitions, off-target
invariance from PR #5160, and Mathlib's integral_tilted formula.

No Gibbs-law identification is inserted. No strict Dobrushin coefficient,
geometric decay, Euclidean-time identification, H1-D5 exact descent, or
complete Yang--Mills mass-gap claim is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter

noncomputable section

local instance posteriorStationarityTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorStationarityCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorStationaritySecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorStationarityMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorStationarityBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance posteriorStationaritySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Re-averaging one coordinate of product spatial-slice Haar against fresh
normalized Haar preserves every nonnegative measurable integral. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_lintegral_singleLink_average
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (∫⁻ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          f (Function.update A target g)
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) =
      ∫⁻ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  classical
  let μcoord :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun _ => normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  have hUpdate :
      Measurable
        (fun z :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update z.1 target z.2) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
      H N target).measurable
  have hJoint :
      Measurable
        (fun z :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              Matrix.specialUnitaryGroup (Fin N) ℂ =>
          f (Function.update z.1 target z.2)) :=
    hf.comp hUpdate
  have hAverage :
      Measurable
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          ∫⁻ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
            f (Function.update A target g)
            ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    hJoint.lintegral_prod_right
  change
    (∫⁻ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (∫⁻ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          f (Function.update A target g)
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        ∂Measure.pi μcoord) =
      ∫⁻ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f A ∂Measure.pi μcoord
  apply MeasureTheory.lintegral_eq_of_lmarginal_eq
    (μ := μcoord) {target} hAverage hf
  ext A
  rw [MeasureTheory.lmarginal_singleton, MeasureTheory.lmarginal_singleton]
  simp [μcoord]

/-- Real-valued continuous version of one-coordinate Haar re-averaging. -/
theorem
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_integral_singleLink_average
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : Continuous f) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          f (Function.update A target g)
          ∂normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        f A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun z => f (Function.update z.1 target z.2)
  have hFcont : Continuous F := by
    exact hf.comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_update_prod_continuous
        H N target)
  have hFint : Integrable F (μ.prod ν) :=
    hFcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfInt : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPos :
      (∫⁻ z, ENNReal.ofReal (F z) ∂(μ.prod ν)) =
        ∫⁻ A, ENNReal.ofReal (f A) ∂μ := by
    calc
      (∫⁻ z, ENNReal.ofReal (F z) ∂(μ.prod ν)) =
          ∫⁻ A, ∫⁻ g, ENNReal.ofReal (f (Function.update A target g)) ∂ν ∂μ := by
            rw [MeasureTheory.lintegral_prod]
            · rfl
            · exact hFcont.measurable.ennreal_ofReal.aemeasurable
      _ = ∫⁻ A, ENNReal.ofReal (f A) ∂μ := by
        simpa [μ, ν] using
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_lintegral_singleLink_average
            H N target (fun A => ENNReal.ofReal (f A))
            hf.measurable.ennreal_ofReal
  have hNeg :
      (∫⁻ z, ENNReal.ofReal (-F z) ∂(μ.prod ν)) =
        ∫⁻ A, ENNReal.ofReal (-f A) ∂μ := by
    calc
      (∫⁻ z, ENNReal.ofReal (-F z) ∂(μ.prod ν)) =
          ∫⁻ A, ∫⁻ g, ENNReal.ofReal (-f (Function.update A target g)) ∂ν ∂μ := by
            rw [MeasureTheory.lintegral_prod]
            · rfl
            · exact hFcont.neg.measurable.ennreal_ofReal.aemeasurable
      _ = ∫⁻ A, ENNReal.ofReal (-f A) ∂μ := by
        simpa [μ, ν] using
          periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_lintegral_singleLink_average
            H N target (fun A => ENNReal.ofReal (-f A))
            hf.neg.measurable.ennreal_ofReal
  calc
    (∫ A, ∫ g, f (Function.update A target g) ∂ν ∂μ) =
        ∫ z, F z ∂(μ.prod ν) := by
          exact (MeasureTheory.integral_prod F hFint).symm
    _ =
        (∫⁻ z, ENNReal.ofReal (F z) ∂(μ.prod ν)).toReal -
          (∫⁻ z, ENNReal.ofReal (-F z) ∂(μ.prod ν)).toReal :=
      MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hFint
    _ =
        (∫⁻ A, ENNReal.ofReal (f A) ∂μ).toReal -
          (∫⁻ A, ENNReal.ofReal (-f A) ∂μ).toReal := by
            rw [hPos, hNeg]
    _ = ∫ A, f A ∂μ :=
      (MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfInt).symm

/-- The exponential posterior fiber log weight is literally the raw posterior
weight evaluated at the target-updated environment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann_eq_posteriorWeight_update
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
        H N hN beta hbeta B A target g =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
        H N hN beta hbeta B (Function.update A target g) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberWeight
  exact Real.exp_log
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight_pos
      H N hN beta hbeta B (Function.update A target g))

/-- Raw posterior-weighted stationarity of one posterior one-link conditional
expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_rawWeighted_integral_singleLinkConditionalExpectationBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
            H N hN beta hbeta B A *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
            H N hN beta hbeta B O A target
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
            H N hN beta hbeta B A * O A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let ν := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
      H N hN beta hbeta B
  let CE := fun A =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
      H N hN beta hbeta B O A target
  let numerator := fun A =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkNumerator
      H N hN beta hbeta B O A target
  have hw : Continuous w := by
    simpa [w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight_continuous
        H N hN beta hbeta B
  have hCE : Continuous CE := by
    simpa [CE] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_continuous
        H N hN beta hbeta B O target
  have hLeftAvg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_integral_singleLink_average
      H N target (fun A => w A * CE A) (hw.mul hCE)
  have hRightAvg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_integral_singleLink_average
      H N target (fun A => w A * O A) (hw.mul O.continuous)
  have hInnerLeft :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
            w (Function.update A target g) *
              CE (Function.update A target g) ∂ν) =
          numerator A := by
    intro A
    have hCEupdate :
        ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          CE (Function.update A target g) = CE A := by
      intro g
      apply
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF_eq_of_agreeOffTarget
          H N hN beta hbeta B (Function.update A target g) A target O
      intro e he
      simp [Function.update, he]
    calc
      (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          w (Function.update A target g) *
            CE (Function.update A target g) ∂ν) =
        ∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann
              H N hN beta hbeta B A target g *
            CE A ∂ν := by
              apply integral_congr_ae
              filter_upwards with g
              rw [hCEupdate g]
              congr 1
              symm
              exact
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann_eq_posteriorWeight_update
                  H N hN beta hbeta B A target g
      _ =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
            H N hN beta hbeta B A target * CE A := by
          rw [integral_mul_const]
          rfl
      _ = numerator A := by
        unfold CE numerator
        unfold
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
        have hPart :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition
                H N hN beta hbeta B A target ≠ 0 :=
          ne_of_gt
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberPartition_pos
              H N hN beta hbeta B A target)
        field_simp [hPart]
  have hInnerRight :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        (∫ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
            w (Function.update A target g) *
              O (Function.update A target g) ∂ν) =
          numerator A := by
    intro A
    unfold numerator
    apply integral_congr_ae
    filter_upwards with g
    congr 1
    symm
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberBoltzmann_eq_posteriorWeight_update
        H N hN beta hbeta B A target g
  calc
    (∫ A, w A * CE A ∂μ) =
        ∫ A, ∫ g, w (Function.update A target g) *
          CE (Function.update A target g) ∂ν ∂μ := hLeftAvg.symm
    _ = ∫ A, numerator A ∂μ := by
      apply integral_congr_ae
      filter_upwards with A
      exact hInnerLeft A
    _ = ∫ A, ∫ g, w (Function.update A target g) *
          O (Function.update A target g) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with A
      exact (hInnerRight A).symm
    _ = ∫ A, w A * O A ∂μ := hRightAvg

/-- Global posterior stationarity of every posterior one-link conditional
expectation on the bounded-continuous carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_integral_singleLinkConditionalExpectationBCF
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    (∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalExpectationBCF
          H N hN beta hbeta B O A target
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
          H N hN beta hbeta B) =
      ∫ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        O A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
          H N hN beta hbeta B := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorWeight
      H N hN beta hbeta B
  have hRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosterior_rawWeighted_integral_singleLinkConditionalExpectationBCF
      H N hN beta hbeta B target O
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
  rw [MeasureTheory.integral_tilted, MeasureTheory.integral_tilted]
  simp_rw [smul_eq_mul, div_mul_eq_mul_div]
  rw [integral_div, integral_div]
  have hExp :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        Real.exp
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight
              H N hN beta hbeta B A) =
          w A := fun A =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorLogWeight_exp
      H N hN beta hbeta B A
  congr 1
  simpa [μ, w] using hRaw

end

end MathlibAnalytic
end MGAP4D
