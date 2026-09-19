import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanDoeblinCoupling
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceRestrictedRandomScanDoeblinObservableContractionSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance referenceRestrictedRandomScanDoeblinObservableContractionSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanDoeblinObservableContractionSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanDoeblinObservableContractionSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanDoeblinObservableContractionSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanDoeblinObservableContractionSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceRestrictedRandomScanDoeblinObservableContractionSpecialUnitaryT2Space
    (N : ℕ) : T2Space (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  infer_instance

/-- Expectation of a real observable after one complete-length restricted
random-scan block. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (f : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ X, f X ∂
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
      H N hN beta hbeta B target source k g₂
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length A

/-- One complete Doeblin block contracts every declared global pairwise
oscillation bound by the exact residual mass `rho = 1 - delta`.

The proof uses the explicit full-block coupling.  The common Haar component is
diagonal, so only the non-diagonal coupling mass contributes to the observable
difference.  No terminal covariance decay or downstream contraction estimate
is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation_difference_abs_le_residualMass_mul
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
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
        H N hN beta hbeta B target source k g₂ f A -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
        H N hN beta hbeta B target source k g₂ f C| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta).toReal * R := by
  let gamma :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure
      H N hN beta hbeta B target source k g₂ A C
  let rho : ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
      H beta
  let mismatch :
      Set
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    {z | z.1 ≠ z.2}
  let A₀ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun _ => 1
  letI : IsProbabilityMeasure gamma := by
    dsimp [gamma]
    infer_instance
  have hfBound :
      ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |f X| ≤ R + |f A₀| := by
    intro X
    calc
      |f X| = |(f X - f A₀) + f A₀| := by
        congr 1
        ring
      _ ≤ |f X - f A₀| + |f A₀| := abs_add_le _ _
      _ ≤ R + |f A₀| := add_le_add (hOsc X A₀) le_rfl
  have hFstIntegrable :
      Integrable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          f z.1)
        gamma := by
    refine
      Integrable.of_bound
        (hf.comp_measurable measurable_fst).aestronglyMeasurable
        (R + |f A₀|) ?_
    exact
      Filter.Eventually.of_forall fun z => by
        simpa [Real.norm_eq_abs] using hfBound z.1
  have hSndIntegrable :
      Integrable
        (fun z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          f z.2)
        gamma := by
    refine
      Integrable.of_bound
        (hf.comp_measurable measurable_snd).aestronglyMeasurable
        (R + |f A₀|) ?_
    exact
      Filter.Eventually.of_forall fun z => by
        simpa [Real.norm_eq_abs] using hfBound z.2
  have hMapFst :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure_map_fst
      H N hN beta hbeta B target source k g₂ A C
  have hMapSnd :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure_map_snd
      H N hN beta hbeta B target source k g₂ A C
  have hLeftExpectation :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
          H N hN beta hbeta B target source k g₂ f A =
        ∫ z, f z.1 ∂gamma := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
    rw [← hMapFst]
    rw [
      MeasureTheory.integral_map
        measurable_fst.aemeasurable
        hf.aestronglyMeasurable]
  have hRightExpectation :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
          H N hN beta hbeta B target source k g₂ f C =
        ∫ z, f z.2 ∂gamma := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockExpectation
    rw [← hMapSnd]
    rw [
      MeasureTheory.integral_map
        measurable_snd.aemeasurable
        hf.aestronglyMeasurable]
  have hMismatchMeasurable : MeasurableSet mismatch := by
    dsimp [mismatch]
    exact (isClosed_eq continuous_fst continuous_snd).isOpen_compl.measurableSet
  have hIntegralLocalizes :
      (∫ z, f z.1 - f z.2 ∂gamma) =
        ∫ z in mismatch, f z.1 - f z.2 ∂gamma := by
    calc
      (∫ z, f z.1 - f z.2 ∂gamma) =
          ∫ z in Set.univ, f z.1 - f z.2 ∂gamma := by
            rw [setIntegral_univ]
      _ = ∫ z in mismatch ∪ mismatchᶜ, f z.1 - f z.2 ∂gamma := by
            rw [union_compl_self]
      _ = ∫ z in mismatch, f z.1 - f z.2 ∂gamma := by
            apply integral_union_eq_left_of_forall hMismatchMeasurable.compl
            intro z hz
            have hzEq : z.1 = z.2 := by
              simpa [mismatch] using hz
            simp [hzEq]
  have hSetIntegralBound :
      ‖∫ z in mismatch, f z.1 - f z.2 ∂gamma‖ ≤
        R * gamma.real mismatch := by
    apply norm_setIntegral_le_of_norm_le_const
    · exact measure_lt_top gamma mismatch
    · intro z _hz
      simpa [Real.norm_eq_abs] using hOsc z.1 z.2
  have hMismatchMass :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure_ne_diagonal_le
      H N hN beta hbeta B target source k g₂ A C
  have hMismatchReal :
      gamma.real mismatch ≤ rho.toReal := by
    unfold Measure.real
    exact
      (ENNReal.toReal_le_toReal
        (measure_ne_top gamma mismatch)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_ne_top
          H beta)).2
        (by simpa [gamma, mismatch, rho] using hMismatchMass)
  rw [hLeftExpectation, hRightExpectation]
  rw [← integral_sub hFstIntegrable hSndIntegrable]
  rw [hIntegralLocalizes]
  change
    ‖∫ z in mismatch, f z.1 - f z.2 ∂gamma‖ ≤ rho.toReal * R
  calc
    ‖∫ z in mismatch, f z.1 - f z.2 ∂gamma‖ ≤
        R * gamma.real mismatch := hSetIntegralBound
    _ ≤ R * rho.toReal :=
      mul_le_mul_of_nonneg_left hMismatchReal hR
    _ = rho.toReal * R := by ring

end

end MathlibAnalytic
end MGAP4D
