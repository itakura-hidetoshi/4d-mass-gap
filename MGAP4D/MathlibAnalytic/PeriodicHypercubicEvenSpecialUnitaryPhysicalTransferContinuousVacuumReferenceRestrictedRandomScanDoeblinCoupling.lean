import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRestrictedRandomScanDoeblinResidual
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceRestrictedRandomScanDoeblinCouplingSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance referenceRestrictedRandomScanDoeblinCouplingSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceRestrictedRandomScanDoeblinCouplingSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceRestrictedRandomScanDoeblinCouplingSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceRestrictedRandomScanDoeblinCouplingSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceRestrictedRandomScanDoeblinCouplingSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceRestrictedRandomScanDoeblinCouplingSpecialUnitaryT2Space
    (N : ℕ) : T2Space (Matrix.specialUnitaryGroup (Fin N) ℂ) := by
  infer_instance

/-- Residual mass of one complete random-scan Doeblin block. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
    (H : ℕ)
    (beta : ℝ) : ℝ≥0∞ :=
  1 -
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCoefficient
      H beta

/-- The named residual mass agrees with every full-block residual row mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_univ_eq_residualMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure
        H N hN beta hbeta B target source k g₂ A Set.univ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_univ
      H N hN beta hbeta B target source k g₂ A

/-- The full-block residual mass is finite. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_ne_top
    (H : ℕ)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta ≠ ∞ := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass]

/-- The full-block residual mass is a strict contraction factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_named_lt_one
    (H : ℕ)
    (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta < 1 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_lt_one
      H beta

/-- Doeblin coupling of two complete restricted random-scan block rows.

The common full-Haar component is coupled diagonally.  If residual mass is
nonzero, the two positive residual rows are coupled by their normalized
product. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  let delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let left :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B target source k g₂ A
  let right :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B target source k g₂ C
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
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

/-- The first marginal of the full-block Doeblin coupling is the exact block
row started at the first configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure_map_fst
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure.map Prod.fst
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure
          H N hN beta hbeta B target source k g₂ A C) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A := by
  let delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let common := delta • nu
  let left :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B target source k g₂ A
  let right :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B target source k g₂ C
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
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
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_univ_eq_residualMass
            H N hN beta hbeta B target source k g₂ A]
      exact hrho
    simpa [common, left, hLeftZero, add_comm] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_add_commonHaar
        H N hN beta hbeta B target source k g₂ A
  · rw [if_neg hrho, Measure.map_smul, Measure.map_fst_prod]
    rw [show right Set.univ = rho by
      simpa [right, rho] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_univ_eq_residualMass
          H N hN beta hbeta B target source k g₂ C]
    rw [smul_smul,
      ENNReal.inv_mul_cancel hrho
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_ne_top
          H beta),
      one_smul]
    simpa [common, left, add_comm] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_add_commonHaar
        H N hN beta hbeta B target source k g₂ A

/-- The second marginal of the full-block Doeblin coupling is the exact block
row started at the second configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure_map_snd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure.map Prod.snd
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure
          H N hN beta hbeta B target source k g₂ A C) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length C := by
  let delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let common := delta • nu
  let left :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B target source k g₂ A
  let right :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B target source k g₂ C
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
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
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_univ_eq_residualMass
            H N hN beta hbeta B target source k g₂ C]
      exact hrho
    simpa [common, right, hRightZero, add_comm] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_add_commonHaar
        H N hN beta hbeta B target source k g₂ C
  · rw [if_neg hrho, Measure.map_smul, Measure.map_snd_prod]
    rw [show left Set.univ = rho by
      simpa [left, rho] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_univ_eq_residualMass
          H N hN beta hbeta B target source k g₂ A]
    rw [smul_smul,
      ENNReal.inv_mul_cancel hrho
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_ne_top
          H beta),
      one_smul]
    simpa [common, right, add_comm] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_add_commonHaar
        H N hN beta hbeta B target source k g₂ C

/-- The full-block Doeblin coupling is a probability measure. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure
        H N hN beta hbeta B target source k g₂ A C) := by
  constructor
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure
        H N hN beta hbeta B target source k g₂ A C Set.univ =
      Measure.map Prod.fst
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure
          H N hN beta hbeta B target source k g₂ A C) Set.univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ]
        rfl
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
        H N hN beta hbeta B target source k g₂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length A Set.univ := by
        rw [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure_map_fst]
    _ = 1 := by
      let K :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanBlockKernel
          H N hN beta hbeta B target source k g₂
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H).length
      letI : IsProbabilityMeasure (K A) :=
        (inferInstance : IsMarkovKernel K).isProbabilityMeasure A
      exact measure_univ

/-- Under the full-block Doeblin coupling, unequal endpoint configurations have
probability at most the residual mass `1 - δ`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure_ne_diagonal_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCouplingMeasure
        H N hN beta hbeta B target source k g₂ A C
        {z | z.1 ≠ z.2} ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
        H beta := by
  let delta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockDoeblinCoefficient
      H beta
  let nu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
      H N
  let common := delta • nu
  let left :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B target source k g₂ A
  let right :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure
      H N hN beta hbeta B target source k g₂ C
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
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
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_univ_eq_residualMass
                H N hN beta hbeta B target source k g₂ A,
          show right Set.univ = rho by
            simpa [right, rho] using
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMeasure_univ_eq_residualMass
                H N hN beta hbeta B target source k g₂ C]
        calc
          rho⁻¹ * (rho * rho) = (rho⁻¹ * rho) * rho := by
            ac_rfl
          _ = rho := by
            rw [
              ENNReal.inv_mul_cancel hrho
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_ne_top
                  H beta),
              one_mul]

end

end MathlibAnalytic
end MGAP4D
