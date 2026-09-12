import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkWeightHarnack
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumGroundStateNormalizedMinorizationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumGroundStateNormalizedMinorizationSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumGroundStateNormalizedMinorizationSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumGroundStateNormalizedMinorizationSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumGroundStateNormalizedMinorizationSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The normalization mass of the exact complete continuous-vacuum ground-state
one-link weight against normalized compact Haar probability. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ≥0∞ :=
  doobWeightMass
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target)

/-- The normalized density of the exact complete continuous-vacuum ground-state
one-link law against normalized compact Haar probability. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ≥0∞ :=
  doobWeightedDensity
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target)
    g

/-- The normalized exact complete continuous-vacuum ground-state one-link law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  doobWeightedMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target)

/-- The complete continuous-vacuum ground-state one-link weight is continuous
in the inserted target-link value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_continuous
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target) := by
  let update : Matrix.specialUnitaryGroup (Fin N) ℂ →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun g => Function.update right target g
  have hUpdate : Continuous update := by
    simpa [update,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N right target
  have hPair : Continuous
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ => (left, update g)) :=
    continuous_const.prodMk hUpdate
  have hKernel : Continuous (fun g =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta left (update g)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp hPair
  have hOmega : Continuous (fun g =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta (update g)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta).comp hUpdate
  change Continuous (fun g =>
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta left *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta left (update g) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (update g))))
  exact ENNReal.continuous_ofReal.comp
    (continuous_const.mul ((continuous_const.mul hKernel).mul hOmega))

/-- The complete one-link weight is measurable for normalized Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_aemeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    AEMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_continuous
    H N hN beta hbeta left right target).measurable.aemeasurable

/-- Every complete one-link weight value is finite. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_lt_top
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target g < ∞ := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
  exact ENNReal.ofReal_lt_top

/-- Integrating the complete pairwise Harnack inequality gives the sharp upper
normalization-denominator bound with only one `exp (16 * beta)` factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_le_exp_sixteen_mul_weight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass
        H N hN beta hbeta left right target ≤
      ENNReal.ofReal (Real.exp (16 * beta)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right target h := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * beta))
  have hPoint : ∀ g, w g ≤ R * w h := by
    intro g
    simpa [w, R] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_pairwise_harnack
        H N hN beta hbeta left right target g h).1
  change (∫⁻ g, w g ∂μ) ≤ R * w h
  calc
    (∫⁻ g, w g ∂μ) ≤ ∫⁻ _g : Matrix.specialUnitaryGroup (Fin N) ℂ, R * w h ∂μ :=
      lintegral_mono hPoint
    _ = R * w h := by simp [μ]

/-- The reverse integrated pairwise comparison controls each weight value by
the same Harnack factor times the exact normalization mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkWeight_le_exp_sixteen_mul_normalizationMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
        H N hN beta hbeta left right target h ≤
      ENNReal.ofReal (Real.exp (16 * beta)) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass
          H N hN beta hbeta left right target := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * beta))
  have hw : AEMeasurable w μ := by
    simpa [w, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_aemeasurable
        H N hN beta hbeta left right target
  have hPoint : ∀ g, w h ≤ R * w g := by
    intro g
    simpa [w, R] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_pairwise_harnack
        H N hN beta hbeta left right target h g).1
  change w h ≤ R * ∫⁻ g, w g ∂μ
  calc
    w h = ∫⁻ _g : Matrix.specialUnitaryGroup (Fin N) ℂ, w h ∂μ := by simp [μ]
    _ ≤ ∫⁻ g, R * w g ∂μ := lintegral_mono hPoint
    _ = R * ∫⁻ g, w g ∂μ := by
      rw [lintegral_const_mul _ hw]

/-- The exact complete-weight normalization denominator is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_pos
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass
        H N hN beta hbeta left right target := by
  let g0 : Matrix.specialUnitaryGroup (Fin N) ℂ := 1
  have hw0 :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
          H N hN beta hbeta left right target g0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_pos
      H N hN beta hbeta left right target g0
  have hcomp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkWeight_le_exp_sixteen_mul_normalizationMass
      H N hN beta hbeta left right target g0
  rw [pos_iff_ne_zero]
  intro hmass
  rw [hmass, mul_zero] at hcomp
  exact (not_lt_of_ge hcomp) hw0

/-- The exact complete-weight normalization denominator is finite. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_lt_top
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass
        H N hN beta hbeta left right target < ∞ := by
  let g0 : Matrix.specialUnitaryGroup (Fin N) ℂ := 1
  have hcomp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_le_exp_sixteen_mul_weight
      H N hN beta hbeta left right target g0
  exact hcomp.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_lt_top
        H N hN beta hbeta left right target g0))

/-- Sharp normalized lower density bound.  The pairwise Harnack factor is paid
exactly once: there is no `exp (32 * beta)` loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity
        H N hN beta hbeta left right target g := by
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * beta))
  let Z : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass
      H N hN beta hbeta left right target
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target
  have hR0 : R ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hRtop : R ≠ ∞ := ne_of_lt ENNReal.ofReal_lt_top
  have hZ0 : Z ≠ 0 := by
    exact ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_pos
        H N hN beta hbeta left right target)
  have hZtop : Z ≠ ∞ := by
    exact ne_of_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_lt_top
        H N hN beta hbeta left right target)
  have hMass : Z ≤ R * w g := by
    simpa [Z, R, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_le_exp_sixteen_mul_weight
        H N hN beta hbeta left right target g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity
    doobWeightedDensity
  change R⁻¹ ≤ w g / Z
  rw [← one_div]
  apply (ENNReal.le_div_iff_mul_le (Or.inl hZ0) (Or.inl hZtop)).2
  change Z / R ≤ w g
  exact (ENNReal.div_le_iff hR0 hRtop).2 (by simpa [mul_comm] using hMass)

/-- Sharp normalized upper density bound with the same single Harnack factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity_upper_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity
        H N hN beta hbeta left right target g ≤
      ENNReal.ofReal (Real.exp (16 * beta)) := by
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * beta))
  let Z : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass
      H N hN beta hbeta left right target
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target
  have hZ0 : Z ≠ 0 := by
    exact ne_of_gt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_pos
        H N hN beta hbeta left right target)
  have hZtop : Z ≠ ∞ := by
    exact ne_of_lt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_lt_top
        H N hN beta hbeta left right target)
  have hWeight : w g ≤ R * Z := by
    simpa [Z, R, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkWeight_le_exp_sixteen_mul_normalizationMass
        H N hN beta hbeta left right target g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity
    doobWeightedDensity
  change w g / Z ≤ R
  exact (ENNReal.div_le_iff hZ0 hZtop).2 (by simpa [mul_comm] using hWeight)

/-- The normalized complete one-link law is an actual probability measure. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_isProbability
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right target) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target
  have hw : AEMeasurable w μ := by
    simpa [w, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight_aemeasurable
        H N hN beta hbeta left right target
  have hMass0 : doobWeightMass μ w ≠ 0 := by
    simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass,
      μ, w] using
      (ne_of_gt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_pos
          H N hN beta hbeta left right target))
  have hMassTop : doobWeightMass μ w ≠ ∞ := by
    simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass,
      μ, w] using
      (ne_of_lt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizationMass_lt_top
          H N hN beta hbeta left right target))
  refine ⟨?_⟩
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
  exact doobWeightedMeasure_measure_univ μ w hw hMass0 hMassTop

/-- Volume-independent Doeblin minorization of the normalized complete one-link
law by normalized compact Haar probability. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ •
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right target := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * beta))
  have hDensity :
      (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => R⁻¹) ≤ᵐ[μ]
        doobWeightedDensity μ w := by
    filter_upwards with g
    simpa [R, μ, w,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity,
      doobWeightedDensity] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity_lower_bound
        H N hN beta hbeta left right target g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
    doobWeightedMeasure
  simpa [R, μ, w] using (withDensity_mono (μ := μ) hDensity)

/-- Matching volume-independent Haar majorization of the normalized complete
one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_upper_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right target ≤
      ENNReal.ofReal (Real.exp (16 * beta)) •
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkFiberWeight
      H N hN beta hbeta left right target
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * beta))
  have hDensity :
      doobWeightedDensity μ w ≤ᵐ[μ]
        (fun _ : Matrix.specialUnitaryGroup (Fin N) ℂ => R) := by
    filter_upwards with g
    simpa [R, μ, w,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity,
      doobWeightedDensity] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberDensity_upper_bound
        H N hN beta hbeta left right target g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
    doobWeightedMeasure
  simpa [R, μ, w] using (withDensity_mono (μ := μ) hDensity)

end

end MathlibAnalytic
end MGAP4D
