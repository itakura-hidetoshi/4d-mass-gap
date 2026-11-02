import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSampledDensityNormBudgetV5_PZ37AEH
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEI — original Wilson kernel transfer norm and density variation

The genuine unnormalized physical one-slab transfer norm has a direct
upper bound from the original Wilson kernel on normalized Haar L2.
No proxy operator, altered coupling, numerical samples or uniform gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AEI_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AEI_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AEI_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AEI_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AEI_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2PZ37AEI_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The literal single-slab Wilson kernel on genuine spatial pair-Haar
has L2 norm at most one at any finite H and nonnegative coupling. -/
theorem p4Q2PZ37AEI_originalWilsonSingleSlabKernelL2_norm_le_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta‖ ≤ 1 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  have hOne :
      MemLp
        (fun _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          (1 : ℝ)) 2 μ := memLp_const 1
  have hKernelAE :
      (fun p =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H N hN beta hbeta p) =ᵐ[μ]
        (fun p =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta p.1 p.2) := by
    simpa [μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        H N hN beta hbeta
  have hle :
      ∀ᵐ p ∂μ,
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
            H N hN beta hbeta p‖ ≤
          ‖hOne.toLp (fun _ :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            (1 : ℝ)) p‖ := by
    filter_upwards [hKernelAE, hOne.coeFn_toLp] with p hp hOnep
    rw [hp, hOnep]
    simpa [Real.norm_eq_abs] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta p.1 p.2
  calc
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta‖ ≤
      ‖hOne.toLp (fun _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          (1 : ℝ))‖ := Lp.norm_le_norm_of_ae_le hle
    _ = 1 := by
      rw [MemLp.toLp_const]
      have hConst :=
        Lp.norm_const'
          (μ := μ) (p := (2 : ENNReal)) (c := (1 : ℝ))
          (by norm_num) (by norm_num)
      simpa using hConst

/-- The genuine unnormalized Gauss-law physical one-slab transfer
operator has norm at most one by its ambient Hilbert-Schmidt bound. -/
theorem p4Q2PZ37AEI_originalPhysicalTransfer_norm_le_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ≤ 1 := by
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_le_ambient
        H N hN beta hbeta
    _ ≤ ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
        H N hN beta hbeta‖ :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_le
        H N hN beta hbeta
    _ ≤ 1 :=
      p4Q2PZ37AEI_originalWilsonSingleSlabKernelL2_norm_le_one
        H N hN beta hbeta

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEI_originalWilsonSingleSlabKernelL2_norm_le_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEI_originalPhysicalTransfer_norm_le_one
