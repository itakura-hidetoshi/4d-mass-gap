import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanDoeblinGeometricIteration
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

local instance referenceRestrictedRandomScanDoeblinStationaryBlockLimitSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance referenceRestrictedRandomScanDoeblinStationaryBlockLimitSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanDoeblinStationaryBlockLimitSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanDoeblinStationaryBlockLimitSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanDoeblinStationaryBlockLimitSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanDoeblinStationaryBlockLimitSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- One complete restricted random-scan block preserves the reference mean of
every integrable real observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation_integral_referenceProbabilityMeasure_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hfInt :
      Integrable f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂)) :
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
        H N hN beta hbeta B target source k g₂ f A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) =
      ∫ A, f A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
      H N hN beta hbeta B target source k g₂
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  have hStationary : K ∘ₘ μ = μ := by
    dsimp [K, μ]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel_comp_referenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length
  have hCompInt : Integrable f (K ∘ₘ μ) := by
    rw [hStationary]
    simpa [μ] using hfInt
  rw [Measure.comp_eq_comp_const_apply] at hCompInt
  have hFubini :=
    ProbabilityTheory.Kernel.integral_comp
      (η := K)
      (κ := Kernel.const Unit μ)
      (a := ()) hCompInt
  calc
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
        H N hN beta hbeta B target source k g₂ f A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) =
      ∫ A, ∫ C, f C ∂K A ∂μ := by
        rfl
    _ = ∫ C, f C ∂(K ∘ₘ μ) := by
      rw [Measure.comp_eq_comp_const_apply]
      simpa [Kernel.const_apply] using hFubini.symm
    _ = ∫ C, f C ∂μ := by rw [hStationary]
    _ = ∫ A, f A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂ := by
      rfl

/-- Every complete-block expectation iterate preserves the exact reference
mean for a strongly measurable observable with a finite global pairwise
oscillation bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_integral_referenceProbabilityMeasure_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X - f Y| ≤ R)
    (n : ℕ) :
    (∫ A,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
        H N hN beta hbeta B target source k g₂ f n A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
        H N hN beta hbeta B target source k g₂) =
      ∫ A, f A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂ := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source k g₂
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      let fn :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
          H N hN beta hbeta B target source k g₂ f n
      let rho : ℝ :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
          H beta).toReal
      have hfnStrong : StronglyMeasurable fn := by
        dsimp [fn]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_stronglyMeasurable
            H N hN beta hbeta B target source k g₂ f hf n
      have hfnOsc :
          ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            |fn X - fn Y| ≤ rho ^ n * R := by
        intro X Y
        dsimp [fn, rho]
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_difference_abs_le_pow_residualMass_mul
            H N hN beta hbeta B target source k g₂ f hf R hR hOsc n X Y
      let A₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
        fun _ => 1
      have hfnInt : Integrable fn μ := by
        refine
          Integrable.of_bound
            hfnStrong.aestronglyMeasurable
            (rho ^ n * R + |fn A₀|) ?_
        exact
          Filter.Eventually.of_forall fun X => by
            calc
              ‖fn X‖ = |fn X| := Real.norm_eq_abs _
              _ = |(fn X - fn A₀) + fn A₀| := by
                congr 1
                ring
              _ ≤ |fn X - fn A₀| + |fn A₀| := abs_add_le _ _
              _ ≤ rho ^ n * R + |fn A₀| :=
                add_le_add (hfnOsc X A₀) le_rfl
      calc
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
            H N hN beta hbeta B target source k g₂ f (n + 1) A
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B target source k g₂) =
          ∫ A,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
              H N hN beta hbeta B target source k g₂ fn A ∂μ := by
            rfl
        _ = ∫ A, fn A ∂μ := by
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation_integral_referenceProbabilityMeasure_eq
              H N hN beta hbeta B target source k g₂ fn hfnInt
        _ = ∫ A, f A
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source k g₂ := by
          simpa [μ] using ih

/-- Complete-block iterates approach the exact stationary reference expectation
with the explicit geometric error inherited from the Doeblin coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_sub_referenceMean_abs_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X - f Y| ≤ R)
    (n : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
        H N hN beta hbeta B target source k g₂ f n A -
      ∫ X, f X
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta).toReal ^ n * R := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
      H N hN beta hbeta B target source k g₂
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target source k g₂
  let fn :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
      H N hN beta hbeta B target source k g₂ f n
  let rho : ℝ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
      H beta).toReal
  have hfnStrong : StronglyMeasurable fn := by
    dsimp [fn]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_stronglyMeasurable
        H N hN beta hbeta B target source k g₂ f hf n
  have hfnOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |fn X - fn Y| ≤ rho ^ n * R := by
    intro X Y
    dsimp [fn, rho]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_difference_abs_le_pow_residualMass_mul
        H N hN beta hbeta B target source k g₂ f hf R hR hOsc n X Y
  let A₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun _ => 1
  have hfnInt : Integrable fn μ := by
    refine
      Integrable.of_bound
        hfnStrong.aestronglyMeasurable
        (rho ^ n * R + |fn A₀|) ?_
    exact
      Filter.Eventually.of_forall fun X => by
        calc
          ‖fn X‖ = |fn X| := Real.norm_eq_abs _
          _ = |(fn X - fn A₀) + fn A₀| := by
            congr 1
            ring
          _ ≤ |fn X - fn A₀| + |fn A₀| := abs_add _ _
          _ ≤ rho ^ n * R + |fn A₀| :=
            add_le_add_right (hfnOsc X A₀) _
  have hConstInt : Integrable (fun _X :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => fn A) μ :=
    integrable_const (fn A)
  have hDiffInt :
      Integrable
        (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          fn A - fn X) μ :=
    hConstInt.sub' hfnInt
  have hAbsDiffInt :
      Integrable
        (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          |fn A - fn X|) μ := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hBoundInt :
      Integrable
        (fun _X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          rho ^ n * R) μ :=
    integrable_const (rho ^ n * R)
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_integral_referenceProbabilityMeasure_eq
      H N hN beta hbeta B target source k g₂ f hf R hR hOsc n
  change |fn A - ∫ X, f X ∂μ| ≤ rho ^ n * R
  rw [← hMean]
  calc
    |fn A - ∫ X, fn X ∂μ| =
        |(∫ _X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N, fn A ∂μ) -
          ∫ X, fn X ∂μ| := by simp
    _ = |∫ X, fn A - fn X ∂μ| := by
      rw [integral_sub hConstInt hfnInt]
    _ ≤ ∫ X, |fn A - fn X| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          rho ^ n * R ∂μ := by
      apply integral_mono hAbsDiffInt hBoundInt
      intro X
      exact hfnOsc A X
    _ = rho ^ n * R := by simp

/-- At every fixed finite volume, repeated complete restricted random-scan
blocks converge pointwise to the exact stationary reference expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_tendsto_referenceMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hf : StronglyMeasurable f)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hOsc :
      ∀ X Y : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X - f Y| ≤ R)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Tendsto
      (fun n =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
          H N hN beta hbeta B target source k g₂ f n A)
      atTop
      (𝓝
        (∫ X, f X
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
            H N hN beta hbeta B target source k g₂)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hBound :
      ∀ n : ℕ,
        dist
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate
            H N hN beta hbeta B target source k g₂ f n A)
          (∫ X, f X
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
              H N hN beta hbeta B target source k g₂) ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
          H beta).toReal ^ n * R := by
    intro n
    simpa [Real.dist_eq] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectationIterate_sub_referenceMean_abs_le
        H N hN beta hbeta B target source k g₂ f hf R hR hOsc n A
  have hPow :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_toReal_pow_tendsto_zero
      H beta
  have hLimit :
      Tendsto
        (fun n : ℕ =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
            H beta).toReal ^ n * R)
        atTop
        (𝓝 0) := by
    have hMul :
        Tendsto
          (fun n : ℕ =>
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
              H beta).toReal ^ n * R)
          atTop
          (𝓝 (0 * R)) :=
      hPow.mul_const R
    simpa using hMul
  exact squeeze_zero (fun _ => dist_nonneg) hBound hLimit

end

end MathlibAnalytic
end MGAP4D
