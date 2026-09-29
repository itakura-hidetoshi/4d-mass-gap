import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedKernelSectionPairEnergy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedIntegratedResponse
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Exact conditional iid normalization of the source-fixed pair energy

The pair energy from #4928 uses two independent values of the SAME actual
source conditional law. It is exactly twice the averaged source variance of
the literal target mean. This factor is normalization, not an estimate.

We prove measurability and boundedness of that target mean and its source
sections, apply Mathlib's product-variance identity, and keep the exact half
through the outer vacuum lower integral. Combining #4927 and #4928 charges
this normalized source variance to the genuine target residual with coefficient
`ofReal(1/2) * OrderedResponseResidualCoefficient`.

The remaining genuine joint-L2 numerator bridge is not assumed here: the
averaged conditional source variance must still be identified with the actual
`P_target g - P_source (P_target g)` norm square. No projection commutation,
new cutoff, source/target reversal, or volume-cardinality factor is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section

attribute [local instance]
  sourceFixedPairEnergyIsTopologicalGroup
  sourceFixedPairEnergyCompactSpace
  sourceFixedPairEnergySecondCountableTopology
  sourceFixedPairEnergyMeasurableSpace
  sourceFixedPairEnergyBorelSpace
  sourceFixedPairEnergySpatialLinkFintype

namespace GroundStateSourceFixedPairEnergy

/-- Exact iid normalization, requiring only actual L2 membership. -/
theorem iid_sqDifference_integral_eq_two_mul_variance
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ) :
    (∫ z : α × α, (X z.1 - X z.2) ^ 2 ∂μ.prod μ) = 2 * variance X μ := by
  let D : α × α → ℝ := fun z => X z.1 - X z.2
  have hD : MemLp D 2 (μ.prod μ) := (hX.comp_fst μ).sub (hX.comp_snd μ)
  have hInt : Integrable X μ := hX.integrable one_le_two
  have hZero : ∫ z, D z ∂μ.prod μ = 0 := by
    dsimp only [D]
    rw [integral_sub (hInt.comp_fst μ) (hInt.comp_snd μ),
      integral_fun_fst, integral_fun_snd]
    simp
  have hVar := variance_add_prod (μ := μ) (ν := μ) hX hX.neg
  calc
    (∫ z : α × α, (X z.1 - X z.2) ^ 2 ∂μ.prod μ) = variance D (μ.prod μ) :=
      (variance_of_integral_eq_zero hD.aemeasurable hZero).symm
    _ = variance X μ + variance (fun a => -X a) μ := by
      simpa only [D, sub_eq_add_neg] using hVar
    _ = 2 * variance X μ := by
      rw [variance_fun_neg]
      ring

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin N) ℂ

/-- The literal target mean is strongly measurable in the background. Reuse
its already-constructed mean kernel on the current-value diagonal. -/
theorem targetMean_stronglyMeasurable (target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F) (C : Cfg) :
    StronglyMeasurable (targetMean H N hN beta hbeta target F C) := by
  let diagonal : Cfg → Cfg × (Gauge × Gauge) := fun A => (A, (A target, A target))
  have hDiag : Measurable diagonal :=
    measurable_id.prodMk ((measurable_pi_apply target).prodMk (measurable_pi_apply target))
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_stronglyMeasurable
      H N hN beta hbeta C target target target (C target) (C target) F hF C 0
  have hEq :
      (fun A => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean
        H N hN beta hbeta C target target target (C target) (C target) F C 0 (diagonal A)) =
      targetMean H N hN beta hbeta target F C := by
    funext A
    rw [oldFirstMean_diagonal_eq_targetMean]
    simp only [diagonal, Function.update_eq_self]
  exact hEq ▸ hMean.comp_measurable hDiag

/-- The target average retains the original bound, with no loss in its use
below. The absolute value accommodates the existing bounded-core interface. -/
theorem targetMean_norm_le (target : Link) (F : (Cfg × Cfg) → ℝ)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) (C A : Cfg) :
    ‖targetMean H N hN beta hbeta target F C A‖ ≤ |bound| := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_norm_le
      H N hN beta hbeta C target target target (C target) (C target)
      F bound hbound C 0 (A, (A target, A target))
  rw [oldFirstMean_diagonal_eq_targetMean] at h
  simpa only [Function.update_eq_self, abs_zero, add_zero] using h

/-- The actual source fiber is a probability law by its exact diagonal
reference identification. No different measure is substituted silently. -/
theorem sourceFiber_isProbabilityMeasure (source : Link) (C A : Cfg) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A source) := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure
    H N hN beta hbeta C A source source source]
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
    H N hN beta hbeta C source source source (C source) (C source) A

/-- The concrete target mean evaluated on a source fiber is genuinely L2 for
that same fiber law; no arbitrary quotient representative is evaluated. -/
theorem targetMean_sourceSection_memLp_two (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) (C A : Cfg) :
    MemLp (fun u => targetMean H N hN beta hbeta target F C (Function.update A source u)) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A source) := by
  letI := sourceFiber_isProbabilityMeasure H N hN beta hbeta source C A
  exact MemLp.of_bound
    ((targetMean_stronglyMeasurable H N hN beta hbeta target F hF C).comp_measurable
      (measurable_update A)).aestronglyMeasurable |bound|
    (Filter.Eventually.of_forall fun u =>
      targetMean_norm_le H N hN beta hbeta target F bound hbound C (Function.update A source u))

/-- Actual conditional source variance of the target mean, averaged over the
actual fixed-boundary background. Unlike pairEnergy, this is normalized once. -/
def sourceVariance (source target : Link) (F : (Cfg × Cfg) → ℝ) (C : Cfg) : ℝ :=
  ∫ A, variance
    (fun u => targetMean H N hN beta hbeta target F C (Function.update A source u))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta C A source)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C

theorem sourceVariance_nonneg (source target : Link) (F : (Cfg × Cfg) → ℝ) (C : Cfg) :
    0 ≤ sourceVariance H N hN beta hbeta source target F C :=
  integral_nonneg fun _ => variance_nonneg _ _

/-- Expand the variance as the centered source-fiber energy with its literal
source-conditional mean as center. No global CondExpL2 identification is made. -/
theorem sourceVariance_eq_centeredSourceEnergy (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) (C : Cfg) :
    sourceVariance H N hN beta hbeta source target F C =
      ∫ A, ∫ u,
        (targetMean H N hN beta hbeta target F C (Function.update A source u) -
          ∫ v, targetMean H N hN beta hbeta target F C (Function.update A source v)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
              H N hN beta hbeta C A source) ^ 2
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A source
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C := by
  unfold sourceVariance
  apply integral_congr_ae
  filter_upwards with A
  exact variance_eq_integral
    (targetMean_sourceSection_memLp_two H N hN beta hbeta source target F hF bound hbound C A).aemeasurable

/-- Exact iid factor two for the existing physical pair energy. This equality
requires no source invariance and no off-diagonal assumption. -/
theorem pairEnergy_eq_two_mul_sourceVariance (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) (C : Cfg) :
    pairEnergy H N hN beta hbeta source target F C =
      2 * sourceVariance H N hN beta hbeta source target F C := by
  unfold pairEnergy sourceVariance
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with A
  letI := sourceFiber_isProbabilityMeasure H N hN beta hbeta source C A
  exact iid_sqDifference_integral_eq_two_mul_variance _ _
    (targetMean_sourceSection_memLp_two H N hN beta hbeta source target F hF bound hbound C A)

/-- Retain the exact half when passing from two-sample energy to variance. -/
theorem sourceVariance_eq_half_pairEnergy (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) (C : Cfg) :
    sourceVariance H N hN beta hbeta source target F C =
      (1 / 2 : ℝ) * pairEnergy H N hN beta hbeta source target F C := by
  rw [pairEnergy_eq_two_mul_sourceVariance H N hN beta hbeta source target F hF bound hbound C]
  ring

/-- Vacuum average of the actual normalized conditional source variance. -/
def vacuumSourceVarianceEnergy (source target : Link) (F : (Cfg × Cfg) → ℝ) : ℝ≥0∞ :=
  ∫⁻ C, ENNReal.ofReal (sourceVariance H N hN beta hbeta source target F C)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta

/-- Exact half-factor survives vacuum integration without a new measurability
hypothesis. Its finiteness is the constant-extraction hypothesis. -/
theorem vacuumSourceVarianceEnergy_eq_half_pairEnergy (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    vacuumSourceVarianceEnergy H N hN beta hbeta source target F =
      ENNReal.ofReal (1 / 2 : ℝ) *
        ∫⁻ C, ENNReal.ofReal (pairEnergy H N hN beta hbeta source target F C)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta := by
  unfold vacuumSourceVarianceEnergy
  calc
    (∫⁻ C, ENNReal.ofReal (sourceVariance H N hN beta hbeta source target F C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) =
      ∫⁻ C, ENNReal.ofReal (1 / 2 : ℝ) *
        ENNReal.ofReal (pairEnergy H N hN beta hbeta source target F C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta := by
      apply lintegral_congr
      intro C
      rw [sourceVariance_eq_half_pairEnergy H N hN beta hbeta source target F hF bound hbound C,
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The normalized source variance inherits #4927 with precisely half its
ordered coefficient. The right side is the genuine joint-L2 target residual. -/
theorem vacuumSourceVarianceEnergy_le_half_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source target : Link) (hne : target ≠ source)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : Cfg) (value : Gauge),
      F (left, Function.update right source value) = F (left, right)) :
    vacuumSourceVarianceEnergy H N hN beta hbeta source target F ≤
      (ENNReal.ofReal (1 / 2 : ℝ) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
          H N hN s beta hbeta source target) * ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_vacuum_norm_sq_le_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
      N hN s hs beta hbeta hcut H source source target hne F hF bound hbound hInvariant
  have hPair :
      (∫⁻ C, ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
          H N hN beta hbeta C source source target
          (C source) (C source) F hF bound hbound C 0‖ ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) =
      ∫⁻ C, ENNReal.ofReal (pairEnergy H N hN beta hbeta source target F C)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta := by
    apply lintegral_congr
    intro C
    rw [fullDifferenceL2_norm_sq_eq_pairEnergy H N hN beta hbeta C source source target F hF bound hbound]
  rw [hPair] at h
  rw [vacuumSourceVarianceEnergy_eq_half_pairEnergy H N hN beta hbeta source target F hF bound hbound]
  simpa only [mul_assoc] using mul_le_mul_left' h (ENNReal.ofReal (1 / 2 : ℝ))

/-- A single source-invariant representative of the actual update satisfies
the normalized estimate for every off-diagonal target. -/
theorem exists_sourceUpdate_representative_vacuumSourceVarianceEnergy_bound
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source : Link)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta) :
    ∃ (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
      (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta source f ∧
      (∀ (left right : Cfg) (value : Gauge),
        F (left, Function.update right source value) = F (left, right)) ∧
      ∀ target : Link, target ≠ source →
        vacuumSourceVarianceEnergy H N hN beta hbeta source target F ≤
          (ENNReal.ofReal (1 / 2 : ℝ) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
              H N hN s beta hbeta source target) * ENNReal.ofReal
            (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta source f -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta target
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2 H N hN beta hbeta source f)‖ ^ 2) := by
  obtain ⟨F, hF, bound, hbound, hRep, hInvariant⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_bounded_sourceInvariant_representative
      H N hN beta hbeta source f hf
  refine ⟨F, hF, bound, hbound, hRep, hInvariant, ?_⟩
  intro target hne
  have h := vacuumSourceVarianceEnergy_le_half_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
    H N hN beta hbeta s hs hcut source target hne F hF bound hbound hInvariant
  simpa only [hRep] using h

end GroundStateSourceFixedPairEnergy

end

end MGAP4D.MathlibAnalytic
