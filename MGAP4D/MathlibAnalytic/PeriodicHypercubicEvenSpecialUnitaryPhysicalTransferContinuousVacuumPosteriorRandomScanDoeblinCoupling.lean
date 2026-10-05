import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorRandomScanDoeblinResidual
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-!
# Posterior full-block Doeblin coupling

The common full-Haar component is coupled diagonally.  The remaining positive
residual rows, each of total mass rho = 1 - delta, are coupled by their
normalized product.  This gives a coupling whose mismatch mass is at most rho.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance posteriorRandomScanDoeblinCouplingSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance posteriorRandomScanDoeblinCouplingTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorRandomScanDoeblinCouplingCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorRandomScanDoeblinCouplingSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorRandomScanDoeblinCouplingMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorRandomScanDoeblinCouplingBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance posteriorRandomScanDoeblinCouplingT2Space
    (N : ℕ) :
    T2Space (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  infer_instance

/-- Doeblin coupling of two posterior complete-block rows. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  let delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let left :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B A
  let right :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B C
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
      H beta
  Measure.map
      (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
      (delta • nu) +
    if rho = 0 then
      (0 : Measure
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    else
      rho⁻¹ • left.prod right

/-- First marginal of the posterior Doeblin coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure_map_fst
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure.map Prod.fst
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure
          H N hN beta hbeta B A C) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A := by
  let delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let common := delta • nu
  let left :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B A
  let right :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B C
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
      H beta
  haveI : IsFiniteMeasure left := by dsimp [left]; infer_instance
  haveI : IsFiniteMeasure right := by dsimp [right]; infer_instance
  change Measure.map Prod.fst
      (Measure.map
          (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
          common +
        if rho = 0 then
          (0 : Measure
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
        else rho⁻¹ • left.prod right) = _
  rw [Measure.map_add _ _ measurable_fst]
  have hDiagMeas :
      Measurable
        (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X)) :=
    measurable_id.prodMk measurable_id
  have hDiagonal :
      Measure.map Prod.fst
          (Measure.map
            (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
            common) = common := by
    calc
      Measure.map Prod.fst
          (Measure.map
            (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
            common) =
        Measure.map
          (Prod.fst ∘
            fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
          common := Measure.map_map measurable_fst hDiagMeas
      _ = common := by
        simpa [Function.comp_def] using (Measure.map_id (μ := common))
  rw [hDiagonal]
  by_cases hrho : rho = 0
  · rw [if_pos hrho]
    have hLeftZero : left = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [show left Set.univ = rho by
        simpa [left, rho] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_univ_eq_residualMass
            H N hN beta hbeta B A]
      exact hrho
    simpa [common, left, hLeftZero, add_comm] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_add_commonHaar
        H N hN beta hbeta B A
  · rw [if_neg hrho, Measure.map_smul, Measure.map_fst_prod]
    rw [show right Set.univ = rho by
      simpa [right, rho] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_univ_eq_residualMass
          H N hN beta hbeta B C]
    rw [smul_smul,
      ENNReal.inv_mul_cancel hrho
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_ne_top
          H beta),
      one_smul]
    simpa [common, left, add_comm] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_add_commonHaar
        H N hN beta hbeta B A

/-- Second marginal of the posterior Doeblin coupling. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure_map_snd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure.map Prod.snd
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure
          H N hN beta hbeta B A C) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length C := by
  let delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let common := delta • nu
  let left :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B A
  let right :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B C
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
      H beta
  haveI : IsFiniteMeasure left := by dsimp [left]; infer_instance
  haveI : IsFiniteMeasure right := by dsimp [right]; infer_instance
  change Measure.map Prod.snd
      (Measure.map
          (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
          common +
        if rho = 0 then
          (0 : Measure
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
        else rho⁻¹ • left.prod right) = _
  rw [Measure.map_add _ _ measurable_snd]
  have hDiagMeas :
      Measurable
        (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X)) :=
    measurable_id.prodMk measurable_id
  have hDiagonal :
      Measure.map Prod.snd
          (Measure.map
            (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
            common) = common := by
    calc
      Measure.map Prod.snd
          (Measure.map
            (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
            common) =
        Measure.map
          (Prod.snd ∘
            fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
          common := Measure.map_map measurable_snd hDiagMeas
      _ = common := by
        simpa [Function.comp_def] using (Measure.map_id (μ := common))
  rw [hDiagonal]
  by_cases hrho : rho = 0
  · rw [if_pos hrho]
    have hRightZero : right = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [show right Set.univ = rho by
        simpa [right, rho] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_univ_eq_residualMass
            H N hN beta hbeta B C]
      exact hrho
    simpa [common, right, hRightZero, add_comm] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_add_commonHaar
        H N hN beta hbeta B C
  · rw [if_neg hrho, Measure.map_smul, Measure.map_snd_prod]
    rw [show left Set.univ = rho by
      simpa [left, rho] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_univ_eq_residualMass
          H N hN beta hbeta B A]
    rw [smul_smul,
      ENNReal.inv_mul_cancel hrho
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_ne_top
          H beta),
      one_smul]
    simpa [common, right, add_comm] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_add_commonHaar
        H N hN beta hbeta B C

/-- The posterior full-block Doeblin coupling is a probability measure. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure
        H N hN beta hbeta B A C) := by
  constructor
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure
        H N hN beta hbeta B A C Set.univ =
      Measure.map Prod.fst
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure
          H N hN beta hbeta B A C) Set.univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ]
        rfl
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A Set.univ := by
        rw [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure_map_fst]
    _ = 1 := by
      let K :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanBlockKernel
          H N hN beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H).length
      letI : IsProbabilityMeasure (K A) :=
        (inferInstance : IsMarkovKernel K).isProbabilityMeasure A
      exact measure_univ

/-- Under the posterior full-block Doeblin coupling, endpoint mismatch has
probability at most rho = 1 - delta. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure_ne_diagonal_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCouplingMeasure
        H N hN beta hbeta B A C
        {z | z.1 ≠ z.2} ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
        H beta := by
  let delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let common := delta • nu
  let left :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B A
  let right :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B C
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
      H beta
  haveI : IsFiniteMeasure left := by dsimp [left]; infer_instance
  haveI : IsFiniteMeasure right := by dsimp [right]; infer_instance
  have hNe :
      MeasurableSet
        {z :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N |
          z.1 ≠ z.2} :=
    (isClosed_eq continuous_fst continuous_snd).isOpen_compl.measurableSet
  change
    Measure.map
        (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
        common {z | z.1 ≠ z.2} +
      (if rho = 0 then
        (0 : Measure
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
      else rho⁻¹ • left.prod right) {z | z.1 ≠ z.2} ≤ rho
  have hDiagMeas :
      Measurable
        (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X)) :=
    measurable_id.prodMk measurable_id
  have hDiagonalZero :
      Measure.map
          (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
          common {z | z.1 ≠ z.2} = 0 := by
    calc
      Measure.map
          (fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X))
          common {z | z.1 ≠ z.2} =
        common
          ((fun X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => (X, X)) ⁻¹'
            {z | z.1 ≠ z.2}) :=
              Measure.map_apply hDiagMeas hNe
      _ = 0 := by simp
  rw [hDiagonalZero, zero_add]
  by_cases hrho : rho = 0
  · rw [if_pos hrho]
    simp [hrho]
  · rw [if_neg hrho, Measure.smul_apply, smul_eq_mul]
    calc
      rho⁻¹ * (left.prod right) {z | z.1 ≠ z.2} ≤
          rho⁻¹ * (left.prod right) Set.univ := by
        gcongr
        exact subset_univ _
      _ = rho := by
        rw [← univ_prod_univ, Measure.prod_prod,
          show left Set.univ = rho by
            simpa [left, rho] using
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_univ_eq_residualMass
                H N hN beta hbeta B A,
          show right Set.univ = rho by
            simpa [right, rho] using
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMeasure_univ_eq_residualMass
                H N hN beta hbeta B C]
        calc
          rho⁻¹ * (rho * rho) = (rho⁻¹ * rho) * rho := by
            ac_rfl
          _ = rho := by
            rw [
              ENNReal.inv_mul_cancel hrho
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass_ne_top
                  H beta),
              one_mul]

end

end MathlibAnalytic
end MGAP4D
