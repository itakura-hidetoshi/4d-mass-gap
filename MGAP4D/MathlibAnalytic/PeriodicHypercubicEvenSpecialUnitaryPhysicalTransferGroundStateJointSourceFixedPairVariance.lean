import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFullDifferenceConditionalVariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkFubiniCompatibility
import Mathlib.Tactic

/-!
# Stationary realization of the actual source conditional variance

PR #4929 has already proved exact conditional iid normalization. We reuse its
conditionalVarianceEnergy, not a second variance carrier or iid proof.

The actual target mean is strongly measurable. Its source heat-bath average
is an actual source conditional integral and is unchanged by source updates.
The existing exact one-link stationarity then identifies conditional variance
with the squared source-projection residual on the original fixed-boundary
background. The resulting vacuum estimate retains exactly half of #4927's
ordered response coefficient.

This closes the fixed-boundary residual presentation, not the remaining
identification of these concrete means with genuine joint CondExpL2 on the
outer vacuum carrier. No positive-beta projection commutation, new cutoff,
source/target reversal or volume-cardinality factor is used.
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

/-- Source projection of the actual target mean, using the existing current-
value reference heat-bath operator. The next theorem exposes its actual law. -/
def sourceProjectedTargetMean (source target : Link) (F : (Cfg × Cfg) → ℝ)
    (C A : Cfg) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection
    H N hN beta hbeta C source source source (C source) (C source)
    (targetMean H N hN beta hbeta target F C) A

/-- The reference presentation is exactly the actual source conditional
integral of the target mean. No inequality or change of law is inserted. -/
theorem sourceProjectedTargetMean_eq_fiberIntegral (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F) (C A : Cfg) :
    sourceProjectedTargetMean H N hN beta hbeta source target F C A =
      ∫ u, targetMean H N hN beta hbeta target F C (Function.update A source u)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A source := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_diagonalCurrentValues_eq_kernelSectionSpatialLinkIntegral
      H N hN beta hbeta C A source source source
      (targetMean H N hN beta hbeta target F C)
      (targetMean_stronglyMeasurable H N hN beta hbeta target F hF C)

/-- Source projection is measurable on the same fixed-boundary carrier. -/
theorem sourceProjectedTargetMean_stronglyMeasurable (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F) (C : Cfg) :
    StronglyMeasurable (sourceProjectedTargetMean H N hN beta hbeta source target F C) := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_stronglyMeasurable
      H N hN beta hbeta C source source source (C source) (C source)
      (targetMean H N hN beta hbeta target F C)
      (targetMean_stronglyMeasurable H N hN beta hbeta target F hF C)

/-- Same-source invariance of a source conditional mean is not commutation
between different one-link projections. -/
theorem sourceProjectedTargetMean_update_source (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (C A : Cfg) (u : Gauge) :
    sourceProjectedTargetMean H N hN beta hbeta source target F C (Function.update A source u) =
      sourceProjectedTargetMean H N hN beta hbeta source target F C A := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathProjection_update_fiber
      H N hN beta hbeta C source source source (C source) (C source)
      (targetMean H N hN beta hbeta target F C) A u

/-- Squared residual of the actual target mean after its source projection,
measured on the original actual fixed-boundary background. -/
def fixedBoundaryLeakageEnergy (source target : Link) (F : (Cfg × Cfg) → ℝ)
    (C : Cfg) : ℝ≥0∞ :=
  ∫⁻ A, ENNReal.ofReal
    ((targetMean H N hN beta hbeta target F C A -
      sourceProjectedTargetMean H N hN beta hbeta source target F C A) ^ 2)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C

/-- Exact stationary return of #4929's actual conditional source variance to
the original background residual. Strong measurability suffices; no new
boundedness, source invariance or off-diagonal assumption is needed. -/
theorem conditionalVarianceEnergy_eq_fixedBoundaryLeakageEnergy (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F) (C : Cfg) :
    conditionalVarianceEnergy H N hN beta hbeta source target F C =
      fixedBoundaryLeakageEnergy H N hN beta hbeta source target F C := by
  let M := targetMean H N hN beta hbeta target F C
  let Q := sourceProjectedTargetMean H N hN beta hbeta source target F C
  let Phi : Cfg → ℝ≥0∞ := fun A => ENNReal.ofReal ((M A - Q A) ^ 2)
  have hM : StronglyMeasurable M :=
    targetMean_stronglyMeasurable H N hN beta hbeta target F hF C
  have hQ : StronglyMeasurable Q :=
    sourceProjectedTargetMean_stronglyMeasurable H N hN beta hbeta source target F hF C
  have hPhi : Measurable Phi :=
    ENNReal.measurable_ofReal.comp ((hM.sub hQ).measurable.pow_const 2)
  have hStationary :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_lintegral_oneLinkFiber
      H N hN beta hbeta C source source source (C source) (C source) Phi hPhi
  simp only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure]
    at hStationary
  unfold conditionalVarianceEnergy fixedBoundaryLeakageEnergy
  change (∫⁻ A, evariance (fun u => M (Function.update A source u))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
        H N hN beta hbeta C A source)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C) =
    ∫⁻ A, Phi A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta C
  rw [← hStationary]
  apply lintegral_congr
  intro A
  rw [evariance_eq_lintegral_ofReal]
  apply lintegral_congr
  intro u
  have hMean := sourceProjectedTargetMean_eq_fiberIntegral H N hN beta hbeta source target F hF C A
  have hFixed := sourceProjectedTargetMean_update_source H N hN beta hbeta source target F C A u
  change ENNReal.ofReal ((M (Function.update A source u) - _) ^ 2) =
    ENNReal.ofReal ((M (Function.update A source u) - Q (Function.update A source u)) ^ 2)
  change Q A = _ at hMean
  change Q (Function.update A source u) = Q A at hFixed
  rw [hFixed, hMean]

/-- Reuse, rather than reprove, #4929's exact two-sample normalization. -/
theorem pairEnergy_ofReal_eq_two_mul_fixedBoundaryLeakageEnergy (source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) (C : Cfg) :
    ENNReal.ofReal (pairEnergy H N hN beta hbeta source target F C) =
      2 * fixedBoundaryLeakageEnergy H N hN beta hbeta source target F C := by
  rw [pairEnergy_ofReal_eq_two_mul_conditionalVarianceEnergy H N hN beta hbeta source target F hF bound hbound C,
    conditionalVarianceEnergy_eq_fixedBoundaryLeakageEnergy H N hN beta hbeta source target F hF C]

/-- The fixed-boundary residual presentation retains half of the ordered
response coefficient under vacuum integration. The joint-L2 numerator
identification is not an assumption of this theorem. -/
theorem fixedBoundaryLeakageEnergy_vacuum_le_half_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source target : Link) (hne : target ≠ source)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : Cfg) (value : Gauge),
      F (left, Function.update right source value) = F (left, right)) :
    (∫⁻ C, fixedBoundaryLeakageEnergy H N hN beta hbeta source target F C
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
      ((2 : ℝ≥0∞)⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
          H N hN s beta hbeta source target) * ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  have h := conditionalVarianceEnergy_vacuum_two_mul_le_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
    H N hN beta hbeta s hs hcut source target hne F hF bound hbound hInvariant
  have hEnergy :
      (∫⁻ C, conditionalVarianceEnergy H N hN beta hbeta source target F C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) =
      ∫⁻ C, fixedBoundaryLeakageEnergy H N hN beta hbeta source target F C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta :=
    lintegral_congr fun C =>
      conditionalVarianceEnergy_eq_fixedBoundaryLeakageEnergy H N hN beta hbeta source target F hF C
  rw [hEnergy] at h
  have hHalf := (ENNReal.mul_le_iff_le_inv (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤)).mp h
  simpa only [mul_assoc] using hHalf

/-- A single source-invariant representative of the actual source update
satisfies the stationary residual bound for every off-diagonal target. -/
theorem exists_sourceUpdate_representative_fixedBoundaryLeakageEnergy_bound
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
        (∫⁻ C, fixedBoundaryLeakageEnergy H N hN beta hbeta source target F C
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
          ((2 : ℝ≥0∞)⁻¹ *
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
  have h := fixedBoundaryLeakageEnergy_vacuum_le_half_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
    H N hN beta hbeta s hs hcut source target hne F hF bound hbound hInvariant
  simpa only [hRep] using h

end GroundStateSourceFixedPairEnergy

end

end MGAP4D.MathlibAnalytic
