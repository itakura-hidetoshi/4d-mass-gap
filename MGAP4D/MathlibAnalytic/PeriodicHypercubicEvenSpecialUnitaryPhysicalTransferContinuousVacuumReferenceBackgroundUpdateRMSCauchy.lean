import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityCenteredExpectationCauchy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
import Mathlib.Tactic

/-!
# RMS Harnack transport for the physical continuous-vacuum one-link fiber

The existing background-update Harnack theorem controls bounded tests in
sup norm.  The quadratic likelihood-ratio/Cauchy spine now permits the same
normalized-law coefficient to act on centered L2 energy instead.

For two source-background values u and v and a distinct resampled fiber, the
literal continuous-vacuum reference fiber weights are mutually
exp(32 beta)-comparable.  Normalization therefore costs one further factor,
and the resulting centered expectation difference is controlled by the already
canonical BackgroundUpdateHarnackInfluence beta times the square root of the
sum of the two actual centered fiber energies.

No new influence coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance physicalFiberRMSCauchySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalFiberRMSCauchySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalFiberRMSCauchySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalFiberRMSCauchySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalFiberRMSCauchySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalFiberRMSCauchySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The literal continuous-vacuum reference one-link fiber weight is measurable
in the inserted compact-group coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A) := by
  let replace : Matrix.specialUnitaryGroup (Fin N) ℂ →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun g =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N A fiber g
  have hReplace : Continuous replace := by
    simpa [replace] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N A fiber
  have hOmega :
      Continuous
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta (replace g)) :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta).comp hReplace
  have hLocal :
      Continuous
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta (replace g) B target g₂) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_left
      H N beta B target g₂).comp hReplace
  have hKernel :
      Continuous
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta (replace g) (Function.update B source k)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp (hReplace.prodMk continuous_const)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
  simpa [replace] using ((hOmega.mul hLocal).mul hKernel).measurable

/-- RMS version of the physical background-update Harnack estimate.

The first- and second-moment integrability receipts are explicit here.  The
next bounded-concrete wrapper discharges them automatically for the actual
ground-state sweep-stage representatives. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_centered_integral_sub_abs_le_harnackInfluence_mul_sqrt_energy
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource fiber backgroundFiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : fiber ≠ backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : StronglyMeasurable X)
    (center : ℝ)
    (hFirstU :
      Integrable
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
                (Function.update A backgroundFiber u) g *
            (X g - center))
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (hFirstV :
      Integrable
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
                (Function.update A backgroundFiber v) g *
            (X g - center))
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (hEnergyU :
      Integrable
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
                (Function.update A backgroundFiber u) g *
            (X g - center) ^ 2)
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (hEnergyV :
      Integrable
        (fun g =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
              H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
                (Function.update A backgroundFiber v) g *
            (X g - center) ^ 2)
        (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    |(∫ g, X g - center
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber u)) -
      (∫ g, X g - center
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
          (Function.update A backgroundFiber v))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta *
        Real.sqrt
          ((∫ g, (X g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
                (Function.update A backgroundFiber u)) +
            ∫ g, (X g - center) ^ 2
              ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂
                (Function.update A backgroundFiber v)) := by
  classical
  let μHaar : Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let Au : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A backgroundFiber u
  let Av : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    Function.update A backgroundFiber v
  let w : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au
  let vWeight : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av
  let R : ℝ := Real.exp (32 * beta)

  have hwMeas : Measurable w := by
    simpa [w, Au] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_measurable
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au
  have hvMeas : Measurable vWeight := by
    simpa [vWeight, Av] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_measurable
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av
  have hwInt : Integrable w μHaar := by
    simpa [w, μHaar, Au] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au
  have hvInt : Integrable vWeight μHaar := by
    simpa [vWeight, μHaar, Av] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av
  have hw0 : ∀ g, 0 ≤ w g := by
    intro g
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au g).le
  have hv0 : ∀ g, 0 ≤ vWeight g := by
    intro g
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_pos
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av g).le
  have hwMassPos : 0 < ∫ g, w g ∂μHaar := by
    simpa [
      w, μHaar, Au,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Au
  have hvMassPos : 0 < ∫ g, vWeight g ∂μHaar := by
    simpa [
      vWeight, μHaar, Av,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
        H N hN beta hbeta B distinguishedTarget distinguishedSource fiber k g₂ Av
  have hR : 1 ≤ R := by
    dsimp [R]
    exact Real.one_le_exp (mul_nonneg (by norm_num) hbeta)

  have hComm :
      ∀ (z x : Matrix.specialUnitaryGroup (Fin N) ℂ),
        Function.update (Function.update A backgroundFiber z) fiber x =
          Function.update (Function.update A fiber x) backgroundFiber z := by
    intro z x
    funext e
    by_cases hef : e = fiber
    · subst e
      simp [hDistinct]
    · by_cases heb : e = backgroundFiber
      · subst e
        simp [hef]
      · simp [hef, heb]

  have hwv : ∀ x, w x ≤ R * vWeight x := by
    intro x
    have hRaw :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
        H N hN beta hbeta B distinguishedTarget distinguishedSource backgroundFiber
        k g₂ (Function.update A fiber x) u v).1
    dsimp [w, vWeight, Au, Av, R]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    rw [hComm u x, hComm v x]
    exact hRaw

  have hvw : ∀ x, vWeight x ≤ R * w x := by
    intro x
    have hRaw :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_update_left_pairwise_harnack
        H N hN beta hbeta B distinguishedTarget distinguishedSource backgroundFiber
        k g₂ (Function.update A fiber x) u v).2
    dsimp [w, vWeight, Au, Av, R]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    rw [hComm v x, hComm u x]
    exact hRaw

  have hCore :=
    HaarLikelihoodRatioInfluence.realIntegralWeightedProbabilityMeasure_centered_integral_sub_abs_le_fullL1_coefficient_mul_sqrt_energy
      μHaar w vWeight X hwMeas hvMeas hwInt hvInt hw0 hv0
      hwMassPos hvMassPos R hR hwv hvw hX center
      (by simpa [w, μHaar, Au] using hFirstU)
      (by simpa [vWeight, μHaar, Av] using hFirstV)
      (by simpa [w, μHaar, Au] using hEnergyU)
      (by simpa [vWeight, μHaar, Av] using hEnergyV)

  simpa [
    μHaar, w, vWeight, Au, Av, R,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence,
    HaarLikelihoodRatioInfluence.coefficient] using hCore

end

end MGAP4D.MathlibAnalytic
