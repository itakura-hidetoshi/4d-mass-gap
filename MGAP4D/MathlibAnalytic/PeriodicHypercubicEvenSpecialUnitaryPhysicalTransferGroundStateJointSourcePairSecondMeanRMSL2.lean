import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairUpdatedVarianceStationarityReturn
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCanonicalTargetLawSecondCenter
import Mathlib.Tactic

/-!
# Source-pair RMS L2 centered at the actual second-law mean

PR #4779 chooses, pointwise on the source-pair carrier, the actual second
target-law fiber mean as the sharp RMS center.  Its response estimate is already
center-independent and coefficient-preserving, but the variable-center RMS has
not yet been packaged as an L2 vector.

This file packages exactly that object.

For each source-pair point z define

  m₂(z) = actual second-law target-fiber mean,

and

  RMS₂(z) = RMS(z; m₂(z)).

We prove measurability directly, rather than pretending the fixed-center
measurability theorem accepts a variable center.  The first centered energy is
handled by subtracting the measurable mean before kernel integration; the
second centered energy reuses the variable-center variance carrier from PR
#4793.

The resulting source-pair L2 vector satisfies the sharp pin-free response bound

  ||ResponseL2|| <= K_pin(target,source) * ||RMS₂L2||.

No fixed-center fallback, factor two, cardinality factor, or new probability
law is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance secondMeanRMSL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance secondMeanRMSL2SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance secondMeanRMSL2SpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance secondMeanRMSL2SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance secondMeanRMSL2SpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance secondMeanRMSL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- First target-law centered energy with the actual second-law mean used as
the pointwise center. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy
    H N hN beta hbeta B distinguishedSource source target k g₂
    F left
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂
      F left z)
    z

/-- The first-law variable-center energy is strongly measurable on the
source-pair carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left) := by
  let mean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left
  have hZero :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection_stronglyMeasurable
      H N target source F hF left 0
  have hMean : StronglyMeasurable mean := by
    simpa [mean] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier_stronglyMeasurable
        H N hN beta hbeta B distinguishedSource source target k g₂ F hF left
  have hMeanProd :
      StronglyMeasurable
        (fun zg :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          mean zg.1) :=
    hMean.comp_measurable measurable_fst
  have hResidual :
      StronglyMeasurable
        (fun zg :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
              H N target source F left 0 zg -
            mean zg.1) :=
    hZero.sub hMeanProd
  have hSquare :
      StronglyMeasurable
        (fun zg :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
            Matrix.specialUnitaryGroup (Fin N) ℂ =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
              H N target source F left 0 zg -
            mean zg.1) ^ 2) := by
    simpa [pow_two] using hResidual.mul hResidual
  have hIntegrated :
      StronglyMeasurable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (Matrix.specialUnitaryGroup (Fin N) ℂ ×
              Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          ∫ g,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
                H N target source F left 0 (z, g) -
              mean z) ^ 2
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel
              H N hN beta hbeta B distinguishedSource source target k g₂ z) :=
    hSquare.integral_kernel_prod_right'
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstCenteredEnergy,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection,
    mean] using hIntegrated

/-- Exact RMS amplitude using the actual second-law fiber mean pointwise. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier
    H N hN beta hbeta target source F left B distinguishedSource k g₂
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
    z

/-- The pointwise-second-mean RMS is strongly measurable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_stronglyMeasurable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂ F left) := by
  by_cases hEq : target = source
  · subst target
    have hZero :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
            H N hN beta hbeta B distinguishedSource source source k g₂ F left =
          (fun _ :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              (Matrix.specialUnitaryGroup (Fin N) ℂ ×
                Matrix.specialUnitaryGroup (Fin N) ℂ) => (0 : ℝ)) := by
      funext z
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitude_diag
          H N hN beta hbeta source F left B z.1 distinguishedSource
          k g₂ z.2.1 z.2.2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
            H N hN beta hbeta B distinguishedSource source source k g₂ F left z)
    rw [hZero]
    exact stronglyMeasurable_const
  · let firstEnergy :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂ F left
    let secondEnergy :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂ F left
    have hFirst : StronglyMeasurable firstEnergy := by
      simpa [firstEnergy] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstVarianceEnergyAtSecondMeanOnCarrier_stronglyMeasurable
          H N hN beta hbeta B distinguishedSource source target k g₂ F hF left
    have hSecond : StronglyMeasurable secondEnergy := by
      simpa [secondEnergy] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondVarianceEnergyOnCarrier_stronglyMeasurable
          H N hN beta hbeta B distinguishedSource source target k g₂ F hF left
    have hSqrt :
        StronglyMeasurable
          (fun z => Real.sqrt (firstEnergy z + secondEnergy z)) :=
      (Real.continuous_sqrt.measurable.comp
        (hFirst.add hSecond).measurable).stronglyMeasurable
    have hEqFun :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left =
          fun z => Real.sqrt (firstEnergy z + secondEnergy z) := by
      funext z
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier_eq_sqrt_centeredEnergy]
      simp only [hEq, if_false]
      rfl
    rw [hEqFun]
    exact hSqrt

/-- The variable-center RMS stays uniformly bounded on the bounded-concrete
core.  This bound is used only for L2 membership. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂ F left z‖ ≤
      4 * |bound| := by
  let mean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
      H N hN beta hbeta B distinguishedSource source target k g₂ F left z
  have hRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier_norm_le
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left mean z
  have hMeanNorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier_norm_le_of_bounded
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left z
  have hMeanAbs : |mean| ≤ |bound| := by
    simpa [mean, Real.norm_eq_abs] using hMeanNorm
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier
        H N hN beta hbeta target source F left B distinguishedSource
        k g₂ mean z‖ ≤
      2 * (|bound| + |mean|) := hRaw
    _ ≤ 2 * (|bound| + |bound|) := by
      gcongr
    _ = 4 * |bound| := by ring

/-- The pointwise-second-mean RMS belongs to the exact source-pair L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_memLp_two_of_bounded
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂ F left)
      2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) := by
  apply MemLp.of_bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF left).aestronglyMeasurable
    (4 * |bound|)
  exact Filter.Eventually.of_forall fun z =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_norm_le
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left z

/-- L2 vector for the exact pointwise-second-mean RMS amplitude. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairBackgroundL2
      H N hN beta hbeta B distinguishedSource k g₂ source :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_memLp_two_of_bounded
    H N hN beta hbeta B distinguishedSource source target k g₂
    F hF bound hbound left).toLp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂ F left)

/-- The L2 vector has the pointwise-second-mean RMS as an a.e.
representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_coeFn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂]
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂ F left := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier_memLp_two_of_bounded
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left).coeFn_toLp

/-- Sharp L2 response estimate with the actual second-law mean used pointwise
as the RMS center.  The response vector remains at reference center zero by
center independence. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_norm_le_canonicalPinFree_mul_secondMeanRMSAmplitudeL2_norm
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left 0‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source *
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left‖ := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let response :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left 0
  let amplitude :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left
  have hK0 : 0 ≤ K.influence target source :=
    K.influence_nonneg target source
  have hResponseRep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_coeFn
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left 0
  have hAmplitudeRep :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeL2_coeFn
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left
  have hSmul :=
    Lp.coeFn_smul (K.influence target source) amplitude
  have hPoint :
      ∀ᵐ z
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
          H N hN beta hbeta B distinguishedSource source k g₂,
        ‖response z‖ ≤ ‖(K.influence target source • amplitude) z‖ := by
    filter_upwards [hResponseRep, hAmplitudeRep, hSmul] with z hR hA hS
    rw [hR, hS]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hA]
    have hRaw :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_abs_le_canonicalPinFree_mul_rmsAmplitude_secondFiberMean_of_bounded
        N hN s hs beta hbeta hcut H target source F hF bound hbound
        left B distinguishedSource k g₂ 0 z
    have hAmp0 :
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left z := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeOnCarrier_nonneg
          H N hN beta hbeta B distinguishedSource source target k g₂
          F left
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left z)
          z
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hProd0 :
        0 ≤ K.influence target source *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier
            H N hN beta hbeta B distinguishedSource source target k g₂ F left z :=
      mul_nonneg hK0 hAmp0
    rw [abs_of_nonneg hProd0]
    simpa [
      K,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanRMSAmplitudeOnCarrier] using hRaw
  calc
    ‖response‖ ≤ ‖K.influence target source • amplitude‖ :=
      Lp.norm_le_norm_of_ae_le hPoint
    _ = K.influence target source * ‖amplitude‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK0]
    _ = _ := rfl

end

end MGAP4D.MathlibAnalytic
