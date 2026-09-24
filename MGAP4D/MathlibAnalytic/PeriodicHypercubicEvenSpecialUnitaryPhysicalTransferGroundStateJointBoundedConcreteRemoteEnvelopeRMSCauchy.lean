import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRemoteCenteredRMSCauchy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkBoundedCoreCondExp
import Mathlib.Tactic

/-!
# Bounded-concrete remote physical RMS transport with the actual envelope

The remote centered RMS theorem from PR #4709 keeps two application receipts
explicit: a strict bound on the targetwise worst-case cross-ratio majorant and
first/second centered-moment integrability.

On the canonical strict physical-sweep interval, the first receipt follows
from the already-proved full physical envelope row bound q_phys < 1.  For a
bounded strongly measurable ground-state concrete section, the second receipts
follow directly from boundedness over the literal probability fiber laws.

This file therefore upgrades the remote RMS estimate to the exact source-
aligned remote entry of the actual physical envelope K.  No new coefficient,
sup-radius substitute, or volume-dependent factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

local instance boundedConcreteRemoteRMSMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundedConcreteRemoteRMSFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance boundedConcreteRemoteRMSNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

private theorem integrable_centered_of_bounded_on_finite_measure
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : StronglyMeasurable X)
    (bound center : ℝ) (hBound : ∀ x, |X x| ≤ bound) :
    Integrable (fun x => X x - center) μ := by
  let M : ℝ := |bound| + |center|
  have hCentered : StronglyMeasurable (fun x => X x - center) :=
    hX.sub stronglyMeasurable_const
  apply Integrable.of_bound hCentered.aestronglyMeasurable M
  filter_upwards with x
  rw [Real.norm_eq_abs]
  calc
    |X x - center| ≤ |X x| + |center| := abs_sub _ _
    _ ≤ |bound| + |center| := by
      exact add_le_add
        ((hBound x).trans (le_abs_self bound))
        (le_refl |center|)
    _ = M := rfl

private theorem integrable_centered_sq_of_bounded_on_finite_measure
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (X : α → ℝ) (hX : StronglyMeasurable X)
    (bound center : ℝ) (hBound : ∀ x, |X x| ≤ bound) :
    Integrable (fun x => (X x - center) ^ 2) μ := by
  let M : ℝ := |bound| + |center|
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hCenteredBound : ∀ x, |X x - center| ≤ M := by
    intro x
    calc
      |X x - center| ≤ |X x| + |center| := abs_sub _ _
      _ ≤ |bound| + |center| := by
        exact add_le_add
          ((hBound x).trans (le_abs_self bound))
          (le_refl |center|)
      _ = M := rfl
  have hCentered : StronglyMeasurable (fun x => X x - center) :=
    hX.sub stronglyMeasurable_const
  have hSq : StronglyMeasurable (fun x => (X x - center) ^ 2) := by
    simpa [pow_two] using hCentered.mul hCentered
  apply Integrable.of_bound hSq.aestronglyMeasurable (M ^ 2)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_pow]
  have hSqBound : |X x - center| ^ 2 ≤ M ^ 2 := by
    nlinarith [abs_nonneg (X x - center), hM0, hCenteredBound x]
  exact hSqBound

/-- On the strict physical-sweep interval every remote targetwise worst-case
cross-ratio majorant is strictly below two.  The proof routes through the
actual full physical envelope entry and its already-proved maximum-row bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_lt_two_of_highTemperature_remote
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ) (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (hNotActive : target ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta A target source < 2 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A
  have hResidualEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_eq_worstCase_of_remote
      H N hN beta hbeta A source target hne hNotActive
  have hEnvelopeEq :
      K.influence target source =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
          H N hN beta hbeta A target source := by
    dsimp [K]
    rw [show target ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source from hNotActive]
    simpa using hResidualEq
  have hEntryLeRow :
      K.influence target source ≤ finiteInfluenceKernelRowSum K target := by
    unfold finiteInfluenceKernelRowSum
    exact Finset.single_le_sum
      (fun source' _ => K.influence_nonneg target source')
      (Finset.mem_univ source)
  have hRowLeMax :=
    finiteInfluenceKernelRowSum_le_maximum K target
  have hMaxLe :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumRow_le_uniformBidirectionalSchurCoefficient
      N hN s hs beta hbeta hcut H A
  have hQLt :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient_lt_one
      s beta hbeta hcut
  have hEntryLtOne :
      K.influence target source < 1 :=
    lt_of_le_of_lt (hEntryLeRow.trans (hRowLeMax.trans hMaxLe)) hQLt
  rw [hEnvelopeEq] at hEntryLtOne
  linarith

/-- A bounded strongly measurable ground-state concrete one-link section obeys
the remote centered RMS estimate with the actual full physical envelope entry.
The remote geometry and high-temperature gate discharge all explicit receipts
left by PR #4709. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_sourceAlignedRemote_centered_integral_sub_abs_le_envelopeKernel_mul_sqrt_energy_of_bounded
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (H : ℕ) (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (hNotActive : target ∉ periodicHypercubicEvenSpatialSliceActiveNeighbors H source)
    (F : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F) (bound : ℝ) (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ) (center : ℝ) :
    |(∫ g,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F left retained g - center
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update A source u)) -
      (∫ g,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F left retained g - center
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update A source v))| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source *
        Real.sqrt
          ((∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N target F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B source distinguishedSource target k g₂
                (Function.update A source u)) +
            ∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N target F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B source distinguishedSource target k g₂
                (Function.update A source v)) := by
  let X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left retained
  have hX : StronglyMeasurable X := by
    simpa [X] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
        H N target F hF left retained
  have hXBound : ∀ g, |X g| ≤ bound := by
    intro g
    have h :=
      hbound
        (left,
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
            ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm g,
              retained))
    simpa [
      X,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection,
      Real.norm_eq_abs] using h
  have hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source := by
    intro hShare
    apply hNotActive
    apply
      (periodicHypercubicEvenSpatialSlice_mem_activeNeighbors_iff
        H source target).mpr
    refine ⟨hne, ?_⟩
    rcases hShare with ⟨p, hTarget, hSource⟩
    exact ⟨p, hSource, hTarget⟩
  have hMajorantLtTwo :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant_lt_two_of_highTemperature_remote
      N hN s hs beta hbeta hcut H A source target hne hNotActive
  let μu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
      (Function.update A source u)
  let μv :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
      (Function.update A source v)
  letI : IsProbabilityMeasure μu := by
    dsimp [μu]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source u)
  letI : IsProbabilityMeasure μv := by
    dsimp [μv]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source v)
  have hFirstU : Integrable (fun g => X g - center) μu :=
    integrable_centered_of_bounded_on_finite_measure
      μu X hX bound center hXBound
  have hFirstV : Integrable (fun g => X g - center) μv :=
    integrable_centered_of_bounded_on_finite_measure
      μv X hX bound center hXBound
  have hEnergyU : Integrable (fun g => (X g - center) ^ 2) μu :=
    integrable_centered_sq_of_bounded_on_finite_measure
      μu X hX bound center hXBound
  have hEnergyV : Integrable (fun g => (X g - center) ^ 2) μv :=
    integrable_centered_sq_of_bounded_on_finite_measure
      μv X hX bound center hXBound
  have hRemote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_centered_integral_sub_abs_le_worstCaseCrossRatioInfluenceMajorant_mul_sqrt_energy
      H N hN beta hbeta B
      source distinguishedSource target source
      hne hne.symm hNoShare
      k g₂ u v A X hX center hMajorantLtTwo
      (by simpa [μu] using hFirstU)
      (by simpa [μv] using hFirstV)
      (by simpa [μu] using hEnergyU)
      (by simpa [μv] using hEnergyV)
  have hResidualEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual_eq_worstCase_of_remote
      H N hN beta hbeta A source target hne hNotActive
  have hEnvelopeEq :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
          H N hN beta hbeta A target source := by
    change
      (if target ∈ periodicHypercubicEvenSpatialSliceActiveNeighbors H source then
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence beta
      else 0) +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
          H N hN beta hbeta A source target =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
          H N hN beta hbeta A target source
    rw [if_neg hNotActive, hResidualEq]
    norm_num
  rw [hEnvelopeEq]
  simpa [X] using hRemote

end

end MGAP4D.MathlibAnalytic
