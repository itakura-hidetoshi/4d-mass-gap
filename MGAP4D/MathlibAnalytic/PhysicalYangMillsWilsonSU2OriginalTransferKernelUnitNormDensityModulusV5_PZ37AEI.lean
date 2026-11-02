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


/-- Real reciprocal variation through a true positive density floor,
with the original transfer inverse magnitude retained explicitly. -/
theorem p4Q2PZ37AEI_realInverseOverDensity_variation
    (t a b m delta : ℝ)
    (ht : 0 < t) (hm : 0 < m)
    (hma : m ≤ a) (hmb : m ≤ b)
    (hdelta : |a - b| ≤ delta) :
    |t⁻¹ / a - t⁻¹ / b| ≤ ((t⁻¹ / m) * delta) / m := by
  have hb : 0 < b := hm.trans_le hmb
  have hInv : 0 < t⁻¹ := inv_pos.mpr ht
  have hAmp : |t⁻¹ / b| ≤ t⁻¹ / m :=
    p4Q2PZ37AEF_realAbsQuotient_le_of_denFloor
      (t⁻¹) b m (t⁻¹) hm hmb
      (by simpa only [abs_of_pos hInv] using (le_refl (t⁻¹)))
  have hVar :=
    p4Q2PZ37AEF_realQuotientVariation_le
      (t⁻¹) (t⁻¹) a b m 0 delta (t⁻¹ / m)
      hm hma hb (by simp) hdelta hAmp
  simpa only [zero_add] using hVar

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "rho" => continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "N" => p4Q2PZ37AEF_originalCenteredCovarianceNumerator H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Tnorm" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖

/-- The true fixed-coupling unnormalized Perron/transfer norm lies
in the positive unit interval, not merely its normalized version. -/
theorem p4Q2PZ37AEI_originalFixedCouplingTransfer_norm_in_pos_unit :
    0 < Tnorm ∧ Tnorm ≤ 1 := by
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b0 hb0,
    p4Q2PZ37AEI_originalPhysicalTransfer_norm_le_one
      H 2 (by norm_num) b0 hb0⟩

/-- The original physical density's q-modulus follows from rho's
oscillation and an actual positive rho lower floor. No proxy law. -/
theorem p4Q2PZ37AEI_originalDensity_variation_fromTrueSqrtDensity
    (m delta R : ℝ)
    (hm : 0 < m)
    (hRhoLower : ∀ z : Pair, m ≤ rho z)
    (hRhoMod : ∀ z w : Pair, D z w < R →
      |rho z - rho w| ≤ delta) :
    ∀ z w : Pair, D z w < R →
      |q b0 hb0 z - q b0 hb0 w| ≤
        ((Tnorm⁻¹ / m) * delta) / m := by
  intro z w hzw
  rw [p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H z,
      p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H w]
  exact p4Q2PZ37AEI_realInverseOverDensity_variation
    Tnorm (rho z) (rho w) m delta
    (p4Q2PZ37AEI_originalFixedCouplingTransfer_norm_in_pos_unit H).1
    hm (hRhoLower z) (hRhoLower w) (hRhoMod z w hzw)

end GroundStatePosteriorJoint

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEI_originalWilsonSingleSlabKernelL2_norm_le_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEI_originalPhysicalTransfer_norm_le_one

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEI_realInverseOverDensity_variation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEI_originalFixedCouplingTransfer_norm_in_pos_unit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEI_originalDensity_variation_fromTrueSqrtDensity
