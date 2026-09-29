import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedDirectCancellation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferDiagonalReferenceFullKernelSectionLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Source-fixed response and the actual kernel-section pair energy

At current-value reference parameters, both the full reference law and every
resampled fiber law are the actual fixed-boundary kernel-section laws (#4797).
We identify the full source-pair L2 difference with the difference of the two
actual target means, then disintegrate its squared norm under those laws.
For source-invariant representatives, #4926 identifies this same energy with
the response norm squared. The existing pin-free RMS estimate is retained.

The auxiliary distinguished source disappears from the actual pair energy.
No different L2 carriers are equated. This is not yet the genuine joint-L2
leakage norm: the conditional iid variance identity (with its factor 1/2),
outer vacuum integration, and genuine CondExpL2 identification remain to be
proved. No terminal recurrence or positive-beta mass gap is asserted here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter

noncomputable section

local instance sourceFixedPairEnergyIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sourceFixedPairEnergyCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sourceFixedPairEnergySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sourceFixedPairEnergyMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sourceFixedPairEnergyBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sourceFixedPairEnergySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStateSourceFixedPairEnergy

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "PairSample" => Cfg × (Gauge × Gauge)

/-- Literal target conditional mean under the actual fixed-boundary law. -/
def targetMean (target : Link) (F : (Cfg × Cfg) → ℝ) (C A : Cfg) : ℝ :=
  ∫ g, F (C, Function.update A target g)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
      H N hN beta hbeta C A target

/-- Difference of actual target means at two independently resampled source values. -/
def targetMeanDifference (source target : Link) (F : (Cfg × Cfg) → ℝ)
    (C : Cfg) (z : PairSample) : ℝ :=
  targetMean H N hN beta hbeta target F C (Function.update z.1 source z.2.1) -
    targetMean H N hN beta hbeta target F C (Function.update z.1 source z.2.2)

/-- The actual conditional iid pair energy at one fixed boundary. There is no
auxiliary distinguished-source parameter in this functional. -/
def pairEnergy (source target : Link) (F : (Cfg × Cfg) → ℝ) (C : Cfg) : ℝ :=
  ∫ A,
    ∫ uv : Gauge × Gauge,
      targetMeanDifference H N hN beta hbeta source target F C (A, uv) ^ 2
      ∂(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A source).prod
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousSpatialLinkNormalizedMeasure
          H N hN beta hbeta C A source)
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta C

theorem pairEnergy_nonneg (source target : Link) (F : (Cfg × Cfg) → ℝ) (C : Cfg) :
    0 ≤ pairEnergy H N hN beta hbeta source target F C := by
  unfold pairEnergy
  exact integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

/-- The old-first mean uses the actual target fiber at the first source update.
The zero center avoids any unnecessary integrability premise for this identity. -/
theorem oldFirstMean_diagonal_eq_targetMean
    (C : Cfg) (distinguishedSource source target : Link)
    (F : (Cfg × Cfg) → ℝ) (z : PairSample) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F C 0 z =
      targetMean H N hN beta hbeta target F C (Function.update z.1 source z.2.1) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMean
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairTargetFiberKernel_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure]
  unfold targetMean
  apply integral_congr_ae
  filter_upwards with g
  simp only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldCenteredSection,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairFirstUpdatedBackground,
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection,
    periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update,
    MeasurableEquiv.apply_symm_apply, sub_zero]

/-- The second mean uses the actual target fiber at the second source update. -/
theorem secondMean_diagonal_eq_targetMean
    (C : Cfg) (distinguishedSource source target : Link)
    (F : (Cfg × Cfg) → ℝ) (z : PairSample) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F C 0 z =
      targetMean H N hN beta hbeta target F C (Function.update z.1 source z.2.2) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMean
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondTargetFiberKernel_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure]
  unfold targetMean
  apply integral_congr_ae
  filter_upwards with g
  simp only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawCenteredSection,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourcePairSecondUpdatedBackground,
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection,
    periodicHypercubicEvenSpatialSliceTargetOffTarget_symm_offTargetRestriction_eq_update,
    MeasurableEquiv.apply_symm_apply, sub_zero]

/-- A genuine a.e. representative, not evaluation of an arbitrary joint L2 class. -/
theorem fullDifferenceL2_diagonal_coeFn
    (C : Cfg) (distinguishedSource source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0 z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
        H N hN beta hbeta C distinguishedSource source (C distinguishedSource) (C source)]
      targetMeanDifference H N hN beta hbeta source target F C := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2
      H N hN beta hbeta C distinguishedSource source target
      (C distinguishedSource) (C source) F hF bound hbound C 0
  let V :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanL2
      H N hN beta hbeta C distinguishedSource source target
      (C distinguishedSource) (C source) F hF bound hbound C 0
  change (fun z => (U - V) z) =ᵐ[_]
    targetMeanDifference H N hN beta hbeta source target F C
  filter_upwards [Lp.coeFn_sub U V,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawOldFirstMeanL2_coeFn
      H N hN beta hbeta C distinguishedSource source target
      (C distinguishedSource) (C source) F hF bound hbound C 0,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawSecondMeanL2_coeFn
      H N hN beta hbeta C distinguishedSource source target
      (C distinguishedSource) (C source) F hF bound hbound C 0] with z hSub hU hV
  rw [hSub]
  change U z - V z = targetMeanDifference H N hN beta hbeta source target F C z
  rw [hU, hV,
    oldFirstMean_diagonal_eq_targetMean H N hN beta hbeta C distinguishedSource source target F z,
    secondMean_diagonal_eq_targetMean H N hN beta hbeta C distinguishedSource source target F z]
  rfl

/-- Exact norm-square transport to the actual source-fiber pair law. Only the
existing Bochner disintegration and diagonal law equalities are used. -/
theorem fullDifferenceL2_norm_sq_eq_pairEnergy
    (C : Cfg) (distinguishedSource source target : Link)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2 =
      pairEnergy H N hN beta hbeta source target F C := by
  let v :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2
      H N hN beta hbeta C distinguishedSource source target
      (C distinguishedSource) (C source) F hF bound hbound C 0
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure
      H N hN beta hbeta C distinguishedSource source (C distinguishedSource) (C source)
  let D := targetMeanDifference H N hN beta hbeta source target F C
  have hRep : (fun z => v z) =ᵐ[μ] D :=
    fullDifferenceL2_diagonal_coeFn H N hN beta hbeta C distinguishedSource source target
      F hF bound hbound
  have hSquareRep : (fun z => (v z) ^ 2) =ᵐ[μ] (fun z => D z ^ 2) := by
    filter_upwards [hRep] with z hz
    exact congrArg (fun r : ℝ => r ^ 2) hz
  have hIntV : Integrable (fun z => (v z) ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using
      (L2.integrable_inner (𝕜 := ℝ) v v)
  have hInt : Integrable (fun z => D z ^ 2) μ := hIntV.congr hSquareRep
  have hNorm : ‖v‖ ^ 2 = ∫ z, D z ^ 2 ∂μ := by
    calc
      ‖v‖ ^ 2 = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
      _ = ∫ z, (v z) ^ 2 ∂μ := by
        simp only [L2.inner_def, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      _ = ∫ z, D z ^ 2 ∂μ := integral_congr_ae hSquareRep
  change ‖v‖ ^ 2 = pairEnergy H N hN beta hbeta source target F C
  rw [hNorm]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure_integral_eq_literalPair
    H N hN beta hbeta C distinguishedSource source (C distinguishedSource) (C source)
    (fun z => D z ^ 2) hInt]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_diagonalCurrentValues_eq_kernelSection]
  unfold pairEnergy
  apply integral_congr_ae
  filter_upwards with A
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_diagonalCurrentValues_eq_kernelSectionSpatialLinkNormalizedMeasure]

/-- Source invariance removes only the direct term. The remaining response
energy is exactly the actual conditional-pair energy, not declared zero. -/
theorem responseL2_norm_sq_eq_pairEnergy_of_sourceInvariant
    (C : Cfg) (distinguishedSource source target : Link) (hne : target ≠ source)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : Cfg) (value : Gauge),
      F (left, Function.update right source value) = F (left, right)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ ^ 2 =
      pairEnergy H N hN beta hbeta source target F C := by
  rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFullDifferenceL2_eq_responseL2_of_sourceInvariant
    H N hN beta hbeta C distinguishedSource source target hne
    (C distinguishedSource) (C source) F hF bound hbound hInvariant C 0]
  exact fullDifferenceL2_norm_sq_eq_pairEnergy
    H N hN beta hbeta C distinguishedSource source target F hF bound hbound

/-- The existing RMS bound now controls the actual fixed-boundary pair energy.
The coefficient orientation remains literally `influence target source`. -/
theorem pairEnergy_sqrt_le_canonicalPinFree_mul_rms
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (C : Cfg) (distinguishedSource source target : Link) (hne : target ≠ source)
    (F : (Cfg × Cfg) → ℝ) (hF : StronglyMeasurable F)
    (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hInvariant : ∀ (left right : Cfg) (value : Gauge),
      F (left, Function.update right source value) = F (left, right)) :
    Real.sqrt (pairEnergy H N hN beta hbeta source target F C) ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source *
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawRMSAmplitudeL2
        H N hN beta hbeta C distinguishedSource source target
        (C distinguishedSource) (C source) F hF bound hbound C 0‖ := by
  rw [← responseL2_norm_sq_eq_pairEnergy_of_sourceInvariant
    H N hN beta hbeta C distinguishedSource source target hne F hF bound hbound hInvariant,
    Real.sqrt_sq (norm_nonneg _)]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_norm_le_canonicalPinFree_mul_rmsAmplitudeL2_norm
      N hN s hs beta hbeta hcut H C distinguishedSource source target
      (C distinguishedSource) (C source) F hF bound hbound C 0

end GroundStateSourceFixedPairEnergy

end

end MGAP4D.MathlibAnalytic
