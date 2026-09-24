import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceBackgroundUpdateRMSCauchy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkBoundedCoreCondExp
import Mathlib.Tactic

/-!
# Bounded-concrete ground-state sections satisfy the physical RMS Harnack bound

PR #4703 proves the centered RMS background-update estimate for the actual
continuous-vacuum one-link fiber law, with first- and second-moment
integrability receipts left explicit.

This file discharges those receipts automatically for the bounded strongly
measurable concrete representatives used by the genuine ground-state L2 core.
The only inputs are the existing pointwise bound on the concrete joint
representative and the already-proved integrability of the physical one-link
fiber weight.

No arbitrary L2 quotient representative is evaluated pointwise.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

local instance boundedConcreteRMSCauchySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundedConcreteRMSCauchySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundedConcreteRMSCauchySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundedConcreteRMSCauchySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundedConcreteRMSCauchySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance boundedConcreteRMSCauchySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem integrable_weight_mul_centered_of_bounded
    {α : Type*}
    [MeasurableSpace α]
    {μ : Measure α}
    (w X : α → ℝ)
    (hwInt : Integrable w μ)
    (hX : StronglyMeasurable X)
    (bound center : ℝ)
    (hXBound : ∀ x, |X x| ≤ bound) :
    Integrable (fun x => w x * (X x - center)) μ := by
  let M : ℝ := |bound| + |center|
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hCenteredBound : ∀ x, |X x - center| ≤ M := by
    intro x
    calc
      |X x - center| ≤ |X x| + |center| := abs_sub _ _
      _ ≤ |bound| + |center| := by
        exact add_le_add_right ((hXBound x).trans (le_abs_self bound)) _
      _ = M := rfl
  have hMeas :
      AEStronglyMeasurable (fun x => w x * (X x - center)) μ := by
    exact hwInt.aestronglyMeasurable.mul
      (hX.sub stronglyMeasurable_const).aestronglyMeasurable
  have hDom : Integrable (fun x => M * |w x|) μ := by
    simpa [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] using
      hwInt.norm.smul M
  apply hDom.mono' hMeas
  filter_upwards with x
  change |w x * (X x - center)| ≤ M * |w x|
  rw [abs_mul]
  calc
    |w x| * |X x - center| ≤ |w x| * M :=
      mul_le_mul_of_nonneg_left (hCenteredBound x) (abs_nonneg _)
    _ = M * |w x| := by ring

private theorem integrable_weight_mul_centered_sq_of_bounded
    {α : Type*}
    [MeasurableSpace α]
    {μ : Measure α}
    (w X : α → ℝ)
    (hwInt : Integrable w μ)
    (hX : StronglyMeasurable X)
    (bound center : ℝ)
    (hXBound : ∀ x, |X x| ≤ bound) :
    Integrable (fun x => w x * (X x - center) ^ 2) μ := by
  let M : ℝ := |bound| + |center|
  have hM0 : 0 ≤ M := by
    dsimp [M]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hCenteredBound : ∀ x, |X x - center| ≤ M := by
    intro x
    calc
      |X x - center| ≤ |X x| + |center| := abs_sub _ _
      _ ≤ |bound| + |center| := by
        exact add_le_add_right ((hXBound x).trans (le_abs_self bound)) _
      _ = M := rfl
  have hCenteredStrong : StronglyMeasurable (fun x => X x - center) :=
    hX.sub stronglyMeasurable_const
  have hSqStrong : StronglyMeasurable (fun x => (X x - center) ^ 2) := by
    simpa [pow_two] using hCenteredStrong.mul hCenteredStrong
  have hMeas :
      AEStronglyMeasurable (fun x => w x * (X x - center) ^ 2) μ :=
    hwInt.aestronglyMeasurable.mul hSqStrong.aestronglyMeasurable
  have hDom : Integrable (fun x => M ^ 2 * |w x|) μ := by
    simpa [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] using
      hwInt.norm.smul (M ^ 2)
  apply hDom.mono' hMeas
  filter_upwards with x
  have hSqBound : |X x - center| ^ 2 ≤ M ^ 2 := by
    nlinarith [abs_nonneg (X x - center), hM0, hCenteredBound x]
  change |w x * (X x - center) ^ 2| ≤ M ^ 2 * |w x|
  rw [abs_mul, abs_pow]
  calc
    |w x| * |X x - center| ^ 2 ≤ |w x| * M ^ 2 :=
      mul_le_mul_of_nonneg_left hSqBound (abs_nonneg _)
    _ = M ^ 2 * |w x| := by ring

/-- A bounded strongly measurable concrete ground-state one-link section
automatically satisfies all moment hypotheses of the physical RMS Harnack
theorem.

This is the form consumed by sweep-stage representatives returned by the
bounded-concrete invariance/sharp-Haar spine. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_backgroundUpdate_centered_integral_sub_abs_le_harnackInfluence_mul_sqrt_energy_of_bounded
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H fiber →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource backgroundFiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber ≠ backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ) :
    |(∫ g,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N fiber F left retained g - center
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber u)) -
      (∫ g,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N fiber F left retained g - center
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber v))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta *
        Real.sqrt
          ((∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N fiber F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
                (Function.update A backgroundFiber u)) +
            ∫ g,
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                  H N fiber F left retained g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
                (Function.update A backgroundFiber v)) := by
  let μHaar : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N fiber F left retained
  let Au : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A backgroundFiber u
  let Av : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A backgroundFiber v
  let wU : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au
  let wV : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av

  have hX : StronglyMeasurable X := by
    simpa [X] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
        H N fiber F hF left retained
  have hXBound : ∀ g, |X g| ≤ bound := by
    intro g
    have h :=
      hbound
        (left,
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) fiber).symm
            ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) fiber).symm g,
              retained))
    simpa [
      X,
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection,
      Real.norm_eq_abs] using h

  have hwUInt : Integrable wU μHaar := by
    simpa [wU, μHaar, Au] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au
  have hwVInt : Integrable wV μHaar := by
    simpa [wV, μHaar, Av] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av

  have hFirstU : Integrable (fun g => wU g * (X g - center)) μHaar :=
    integrable_weight_mul_centered_of_bounded
      wU X hwUInt hX bound center hXBound
  have hFirstV : Integrable (fun g => wV g * (X g - center)) μHaar :=
    integrable_weight_mul_centered_of_bounded
      wV X hwVInt hX bound center hXBound
  have hEnergyU : Integrable (fun g => wU g * (X g - center) ^ 2) μHaar :=
    integrable_weight_mul_centered_sq_of_bounded
      wU X hwUInt hX bound center hXBound
  have hEnergyV : Integrable (fun g => wV g * (X g - center) ^ 2) μHaar :=
    integrable_weight_mul_centered_sq_of_bounded
      wV X hwVInt hX bound center hXBound

  have hRMS :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_centered_integral_sub_abs_le_harnackInfluence_mul_sqrt_energy
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber backgroundFiber
      hDistinct k g₂ u v A X hX center
      (by simpa [wU, X, μHaar, Au] using hFirstU)
      (by simpa [wV, X, μHaar, Av] using hFirstV)
      (by simpa [wU, X, μHaar, Au] using hEnergyU)
      (by simpa [wV, X, μHaar, Av] using hEnergyV)

  simpa [X] using hRMS

end

end MGAP4D.MathlibAnalytic
