import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferKernelUnitNormDensityModulusV5_PZ37AEI
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEJ — literal original Wilson action controls the physical transfer norm

For every finite H, positive SU(N) rank and nonnegative Wilson coupling beta,
the original one-slab action obeys a global finite-volume bound
  A_H <= 2 * (length spatial plaquettes + length spatial crossing links).
Consequently the actual literal one-slab Wilson kernel obeys
  exp(-beta * globalActionBudget H) <= K_H(A,B) <= 1.

The lower bound is transferred through the ACTUAL Haar L2 matrix coefficient
on the genuine Gauss-law constant unit vector. Together with AEI's genuine
unnormalized physical operator U=1 this gives a TWO-SIDED finite-volume norm
certificate. No spectral gap, H-uniform norm floor, numerical finite net,
replacement transfer law or continuum mass gap is assumed or asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AEJ_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AEJ_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AEJ_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AEJ_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AEJ_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2PZ37AEJ_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The ACTUAL unnormalized physical Gauss-law transfer norm is at least
the explicit positive lower bound of the literal Wilson one-slab kernel.
The constant-one Haar vector lies in the real physical Hilbert subspace,
so this is not an ambient-only assertion. -/
theorem p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let v := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let k := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
    H beta
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  have hK :
      ∀ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        k ≤ periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2 := by
    intro p
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
      H N hN beta hbeta p.1 p.2
  have hKernelIntegrable :
      Integrable (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2) μ := by
    simpa only [μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_integrable
        H N hN beta hbeta
  have hIntegral :
      k ≤ ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2 ∂μ := by
    have hMono :=
      integral_mono (integrable_const k) hKernelIntegrable hK
    have hConst :
        (∫ _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          k ∂μ) = k := by simp
    exact hConst ▸ hMono
  have hPair : k ≤ inner ℝ (T v) v := by
    change k ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ)))
      (Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ))
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_const_one_eq_integral]
    exact hIntegral
  have hv : ‖v‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  have hApply : ‖T v‖ ≤ ‖T‖ * ‖v‖ :=
    ContinuousLinearMap.le_opNorm T v
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta =
        k := rfl
    _ ≤ inner ℝ (T v) v := hPair
    _ ≤ ‖T v‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hApply (norm_nonneg v)
    _ = ‖T‖ := by rw [hv]; ring

/-- Genuine unnormalized physical transfer, arbitrary rank and finite volume:
explicit strictly positive lower and upper unit norm bounds. -/
theorem p4Q2PZ37AEJ_originalPhysicalTransfer_explicitTwoSidedNorm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ∧
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ≤ 1 := by
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H beta,
    p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
      H N hN beta hbeta,
    p4Q2PZ37AEI_originalPhysicalTransfer_norm_le_one
      H N hN beta hbeta⟩

/-- Quantitative reciprocal bound for the ORIGINAL unnormalized physical
transfer. Its volume dependence is explicit in the ACTUAL Wilson action. -/
theorem p4Q2PZ37AEJ_originalPhysicalTransfer_inverseNorm_le_expAction
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ ≤
      Real.exp (beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) := by
  have hLower :=
    p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
      H N hN beta hbeta
  have hk :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H beta
  have ht : 0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    hk.trans_le hLower
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta)⁻¹ := (inv_le_inv₀ hk ht).2 hLower
    _ = Real.exp (beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) := by
      unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      rw [Real.exp_neg, inv_inv]

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEJ_originalPhysicalTransfer_explicitTwoSidedNorm
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEJ_originalPhysicalTransfer_inverseNorm_le_expAction
