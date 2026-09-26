import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairFirstCrossEnergyGlobalPythagorean
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Tactic

/-!
# Ordered response-square as the source-pair response L2 norm-square

PR #4783 lifts the first-cross Pythagorean decomposition to the actual ordered
outer law.  Its second summand is

  ∫ ofReal (response(C,v)^2) d rho_ordered(C,v).

The concrete response itself was already realized in the source-pair carrier

  L2(nu_source)

in PR #4776.  The exact law-reordering theorem from PR #4727 identifies
rho_ordered as the pushforward of nu_source.

This file closes that bridge exactly:

  ordered integral of response^2
    = ofReal (||responseL2||^2).

No inequality, response coefficient, factor two, or cardinality factor is
introduced.  After this theorem the global first-cross decomposition contains
only one genuinely new analytic term: the old-target-law variance.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance sourcePairResponseSquareOrderedL2SpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourcePairResponseSquareOrderedL2SpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourcePairResponseSquareOrderedL2SpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourcePairResponseSquareOrderedL2SpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourcePairResponseSquareOrderedL2SpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourcePairResponseSquareOrderedL2SpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Response written directly on the ordered (C,v) carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (Cv :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
    H N hN beta hbeta target source F left B distinguishedSource
    k g₂ 0
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source Cv)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse_stronglyMeasurable
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
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_stronglyMeasurable
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF left 0).comp_measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection_measurable
        H N source)

/-- The first target-law mean also factors through the exact reordered
coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean_zero_eq_ordered
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
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left 0 z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
          H N source z) := by
  let z' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
      H N source
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
        H N source z)
  have hFirstUpdate :
      Function.update z'.1 source z'.2.1 =
        Function.update z.1 source z.2.1 := by
    simp [
      z',
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground]
  have hSecondBackground :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
          H N source z' =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground
          H N source z := by
    simpa [z'] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground_orderedSection_reorderedMap
        H N source z
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedFirstFiberMean
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
  simp only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply]
  rw [hFirstUpdate]
  apply integral_congr_ae
  filter_upwards with g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection
  rw [hSecondBackground]

/-- The concrete source-pair response factors through the exact reordered
source-pair coordinates. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_eq_orderedResponse
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
        H N hN beta hbeta target source F left B distinguishedSource
        k g₂ 0 z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
          H N source z) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_eq]
  simp only [hne, if_false]
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left 0 z -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left z =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse
        H N hN beta hbeta B distinguishedSource source target k g₂
        F left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
          H N source z)
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFirstMean_zero_eq_ordered
      H N hN beta hbeta B distinguishedSource source target k g₂
      F left z,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondFiberMeanOnCarrier_eq_ordered
      H N hN beta hbeta B distinguishedSource source target k g₂
      F left z]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedMeanGap_eq_responseOnCarrier
      H N hN beta hbeta B distinguishedSource source target hne k g₂
      F left
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
        H N source z)

/-- The ordered response-square integral is exactly the squared norm of the
source-pair response L2 vector from PR #4776. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponseSq_lintegral_eq_responseL2_norm_sq_ofReal
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (∫⁻ Cv,
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
            H N hN beta hbeta target source F left B distinguishedSource
            k g₂ 0
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairOrderedSection
              H N source Cv)) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
        H N hN beta hbeta B distinguishedSource source k g₂) =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta B distinguishedSource source target k g₂
            F hF bound hbound left 0‖ ^ 2) := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let ρ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceSecondBackgroundMeasure
      H N hN beta hbeta B distinguishedSource source k g₂
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
      H N hN beta hbeta target source F left B distinguishedSource
      k g₂ 0
  let RO :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse
      H N hN beta hbeta B distinguishedSource source target k g₂
      F left
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
      H N hN beta hbeta B distinguishedSource source target k g₂
      F hF bound hbound left 0
  let Phi : 
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ℝ≥0∞ :=
    fun Cv => ENNReal.ofReal ((RO Cv) ^ 2)
  have hR : MemLp R 2 ν := by
    simpa [R, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_memLp_two_of_bounded
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left 0
  have hROStrong : StronglyMeasurable RO := by
    simpa [RO] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse_stronglyMeasurable
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF left
  have hPhi : Measurable Phi := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (hROStrong.measurable.pow_const 2)
  have hReorder :
      (∫⁻ z,
        Phi
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
            H N source z)
        ∂ν) =
      ∫⁻ Cv, Phi Cv ∂ρ := by
    simpa [ν, ρ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePair_lintegral_reordered
        H N hN beta hbeta B distinguishedSource source k g₂ Phi hPhi
  have hSourceOrdered :
      (∫⁻ z, ENNReal.ofReal ((R z) ^ 2) ∂ν) =
        ∫⁻ Cv, Phi Cv ∂ρ := by
    calc
      (∫⁻ z, ENNReal.ofReal ((R z) ^ 2) ∂ν) =
          ∫⁻ z,
            Phi
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
                H N source z)
            ∂ν := by
        apply lintegral_congr
        intro z
        have hFactor :
            R z =
              RO
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairReorderedMap
                  H N source z) := by
          simpa [R, RO] using
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_eq_orderedResponse
              H N hN beta hbeta B distinguishedSource source target hne k g₂
              F left z
        rw [hFactor]
        rfl
      _ = ∫⁻ Cv, Phi Cv ∂ρ := hReorder
  have hSqInt : Integrable (fun z => (R z) ^ 2) ν := by
    simpa only [Pi.pow_apply] using hR.integrable_sq
  have hOfReal :
      (∫⁻ z, ENNReal.ofReal ((R z) ^ 2) ∂ν) =
        ENNReal.ofReal (∫ z, (R z) ^ 2 ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hSqInt
      (ae_of_all ν fun z => sq_nonneg (R z))).symm
  have hLRep :
      (fun z => L z) =ᵐ[ν] R := by
    simpa [L, R, ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_coeFn
        H N hN beta hbeta B distinguishedSource source target k g₂
        F hF bound hbound left 0
  have hNorm :
      ‖L‖ ^ 2 = ∫ z, (R z) ^ 2 ∂ν := by
    rw [realL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hLRep] with z hz
    rw [hz]
    simp [Real.norm_eq_abs, sq_abs]
  have hMain :
      (∫⁻ Cv, Phi Cv ∂ρ) =
        ENNReal.ofReal (‖L‖ ^ 2) := by
    calc
      (∫⁻ Cv, Phi Cv ∂ρ) =
          ∫⁻ z, ENNReal.ofReal ((R z) ^ 2) ∂ν :=
        hSourceOrdered.symm
      _ = ENNReal.ofReal (∫ z, (R z) ^ 2 ∂ν) := hOfReal
      _ = ENNReal.ofReal (‖L‖ ^ 2) := by rw [← hNorm]
  simpa [
    Phi, RO, ρ, L,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOrderedResponse]
    using hMain

end

end MGAP4D.MathlibAnalytic
