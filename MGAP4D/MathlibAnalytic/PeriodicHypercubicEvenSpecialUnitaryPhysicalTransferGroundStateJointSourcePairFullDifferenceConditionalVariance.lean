import MGAP4D.MathlibAnalytic.RealL2ConditionalIndependentPairVariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedIntegratedResponse
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedKernelSectionPairEnergy
import Mathlib.Tactic

/-!
# Exact conditional-variance normalization of the physical full difference

The old-first and second means are evaluations of ONE source-value target-mean
section. The existing source-pair law draws two independent values from the
same source conditional law. Hence its full-difference L2 norm square equals
exactly twice the integrated source conditional variance of that target mean.

The identity holds for any bounded concrete input. Source invariance is needed
only when composing with the response estimate of #4927. No probability law
is replaced, and the factor two is an equality, not an estimate loss.

The actual kernel-section target-mean and current-value law identities from
#4928 are reused. Its pair energy is exactly twice the actual source
conditional-variance energy, with no auxiliary distinguished source. The
identification of that energy with the genuine joint source leakage norm
remains a separate a.e. projection/disintegration bridge.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance fullDifferenceVarianceIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance fullDifferenceVarianceCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance fullDifferenceVarianceSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance fullDifferenceVarianceMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance fullDifferenceVarianceBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance fullDifferenceVarianceSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- The existing target mean after specifying a single source value. Repeating
that value in the pair is only an evaluation map, not a change of measure. -/
def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (center : ℝ)
    (Au : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean
    H N hN beta hbeta B distinguishedSource source target k g₂ F left center (Au.1, (Au.2, Au.2))

/-- Joint measurability of the one-source-value target-mean section. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (center : ℝ) :
    StronglyMeasurable (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean
      H N hN beta hbeta B distinguishedSource source target k g₂ F left center) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF left center).comp_measurable
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_snd))

/-- The second target mean is the same section evaluated at the second source
value. Both its observable section and its conditional law are kept literal. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean_eq_sourceValueMean
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (center : ℝ)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N × (Matrix.specialUnitaryGroup (Fin N) ℂ × Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean H N hN beta hbeta B distinguishedSource source target k g₂ F left center z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean H N hN beta hbeta B distinguishedSource source target k g₂ F left center (z.1, z.2.2) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondTargetFiberKernel_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply]
  rfl

/-- Exact numerator normalization in the EXISTING source-pair Hilbert space.
No off-diagonal or source-invariance premise is needed for this identity. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_norm_sq_ofReal_eq_two_mul_sourceValueMean_evariance_lintegral
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) (center : ℝ) :
    ENNReal.ofReal (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF bound hbound left center‖ ^ 2) =
      2 * ∫⁻ A, evariance
        (fun u => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean
          H N hN beta hbeta B distinguishedSource source target k g₂ F left center (A, u))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure H N hN beta hbeta B source distinguishedSource source k g₂ A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure H N hN beta hbeta B source distinguishedSource k g₂ := by
  let μ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure H N hN beta hbeta B source distinguishedSource k g₂
  let κ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel H N hN beta hbeta B source distinguishedSource source k g₂
  let M := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean H N hN beta hbeta B distinguishedSource source target k g₂ F left center
  let O := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2 H N hN beta hbeta B distinguishedSource source target k g₂ F hF bound hbound left center
  let S := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanL2 H N hN beta hbeta B distinguishedSource source target k g₂ F hF bound hbound left center
  let L := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2 H N hN beta hbeta B distinguishedSource source target k g₂ F hF bound hbound left center
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource k g₂
  have hM : StronglyMeasurable M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂ F hF left center
  have hFiber : ∀ A, MemLp (fun u => M (A, u)) 2 (κ A) := by
    intro A
    apply MemLp.of_bound
      (hM.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (|bound| + |center|)
    filter_upwards with u
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean_norm_le
      H N hN beta hbeta B distinguishedSource source target k g₂ F bound hbound left center (A, (u, u))
  have hRep : (fun z => L z) =ᵐ[μ ⊗ₘ (κ ×ₖ κ)]
      (fun z => M (z.1, z.2.1) - M (z.1, z.2.2)) := by
    filter_upwards [Lp.coeFn_sub O S,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2_coeFn
        H N hN beta hbeta B distinguishedSource source target k g₂ F hF bound hbound left center,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanL2_coeFn
        H N hN beta hbeta B distinguishedSource source target k g₂ F hF bound hbound left center] with z hSub hOld hSecond
    change (O - S) z = M (z.1, z.2.1) - M (z.1, z.2.2)
    rw [hSub, hOld, hSecond,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean_eq_sourceValueMean]
    rfl
  have h := realL2_conditionalIndependentPair_norm_sq_eq_two_mul_lintegral_evariance
    μ κ M hM hFiber L hRep
  simpa only [L, M, μ, κ,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply] using h

namespace GroundStateSourceFixedPairEnergy

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin N) ℂ

/-- Source conditional variance of the actual target mean, integrated under
its actual fixed-boundary law. No auxiliary distinguished source remains. -/
def conditionalVarianceEnergy (source target : Link) (F : (Cfg × Cfg) → ℝ)
    (C : Cfg) : ℝ≥0∞ :=
  ∫⁻ A, evariance
    (fun u => targetMean H N hN beta hbeta target F C (Function.update A source u))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta C A source)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C

/-- The full L2 norm is exactly twice the actual conditional variance. The
arbitrary-fiber current-value law identifications and target-mean identity
from #4928 are reused, without rewriting a measure-indexed L2 vector. -/
theorem fullDifferenceL2_norm_sq_ofReal_eq_two_mul_conditionalVarianceEnergy
    (C : Cfg) (distinguishedSource source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2) =
      2 * conditionalVarianceEnergy H N hN beta hbeta source target F C := by
  have hEnergy :
      (∫⁻ A, evariance
        (fun u => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F C 0 (A, u))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta C source distinguishedSource source
          (C distinguishedSource) (C source) A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta C source distinguishedSource
          (C distinguishedSource) (C source)) =
        conditionalVarianceEnergy H N hN beta hbeta source target F C := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection]
    unfold conditionalVarianceEnergy
    apply lintegral_congr
    intro A
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure]
    have hM :
        (fun u => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSourceValueMean
          H N hN beta hbeta C distinguishedSource source target
          (C distinguishedSource) (C source) F C 0 (A, u)) =
        (fun u => targetMean H N hN beta hbeta target F C (Function.update A source u)) := by
      funext u
      exact oldFirstMean_diagonal_eq_targetMean
        H N hN beta hbeta C distinguishedSource source target F (A, (u, u))
    rw [hM]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_norm_sq_ofReal_eq_two_mul_sourceValueMean_evariance_lintegral,
    hEnergy]

/-- #4928's actual pair energy has the exact normalization two, not one. -/
theorem pairEnergy_ofReal_eq_two_mul_conditionalVarianceEnergy
    (source target : Link) (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) (C : Cfg) :
    ENNReal.ofReal (pairEnergy H N hN beta hbeta source target F C) =
      2 * conditionalVarianceEnergy H N hN beta hbeta source target F C := by
  rw [← fullDifferenceL2_norm_sq_eq_pairEnergy
    H N hN beta hbeta C source source target F hF bound hbound]
  exact fullDifferenceL2_norm_sq_ofReal_eq_two_mul_conditionalVarianceEnergy
    H N hN beta hbeta C source source target F hF bound hbound

/-- Vacuum integration retains the exact normalization on the actual laws. -/
theorem fullDifferenceL2_vacuum_norm_sq_eq_two_mul_conditionalVarianceEnergy
    (distinguishedSource source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ C, ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) =
      2 * ∫⁻ C, conditionalVarianceEnergy H N hN beta hbeta source target F C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta := by
  calc
    (∫⁻ C, ENNReal.ofReal
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) =
      ∫⁻ C, 2 * conditionalVarianceEnergy H N hN beta hbeta source target F C
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta := by
      apply lintegral_congr
      intro C
      exact fullDifferenceL2_norm_sq_ofReal_eq_two_mul_conditionalVarianceEnergy
        H N hN beta hbeta C distinguishedSource source target F hF bound hbound
    _ = _ := lintegral_const_mul' 2 _ (by simp)

/-- Twice the actual conditional-variance energy is controlled by #4927's
ordered coefficient and genuine target residual. The remaining identification
with the genuine SOURCE leakage norm is not assumed here. -/
theorem conditionalVarianceEnergy_vacuum_two_mul_le_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (source target : Link) (hne : target ≠ source)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : Cfg) (value : Gauge),
      F (left, Function.update right source value) = F (left, right)) :
    2 * (∫⁻ C, conditionalVarianceEnergy H N hN beta hbeta source target F C
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure H N hN beta hbeta) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseResidualCoefficient
        H N hN s beta hbeta source target * ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound)‖ ^ 2) := by
  rw [← fullDifferenceL2_vacuum_norm_sq_eq_two_mul_conditionalVarianceEnergy
    H N hN beta hbeta source source target F hF bound hbound]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_vacuum_norm_sq_le_orderedCoefficient_mul_condExpResidual_of_sourceInvariant
      N hN s hs beta hbeta hcut H source source target hne F hF bound hbound hInvariant

end GroundStateSourceFixedPairEnergy

end

end MGAP4D.MathlibAnalytic
