import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllPositivePowersHaarCauchyFloorV5_PZ37AKC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExactPowerAJABudgetResidualV5_PZ37AJZ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalQFreeFullTopVarianceV5_PZ37AJV
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKE — original AJA finite-power witness tail and geometric test

AKC establishes positive lower Haar floors for all positive Wilson powers,
but a positive lower floor is NOT a witness for the strict original AJA
upper test. This new append-only leaf uses the actual normalized finite-H
Wilson transfer S, the unchanged centered physical ZW source f0, the
entire original fixed top subspace Q and the unchanged Haar budget B.

We establish stability: if ANY genuine strict AJA power witness exists,
then EVERY later natural Wilson power is also a strict witness. Thus the
already certified AJI equivalence to ||Q f0||^2 < B can be strengthened
to an exact eventual-all-powers criterion. An additional directly
checkable finite-power sufficient test uses the actual top-orthogonal
restriction norm and exact AJZ squared orthogonal decomposition.

Separately AJV's genuine positive q-free defect correction implies an
UNCONDITIONAL eventual decrease below V-C/2, where V=||f0||^2 and
C>0 is the actual original defect correction. This is weaker than B:
it is NOT an unconditional AJA witness.

The original Wilson/Haar/ZW/AJA definitions, finite H, beta>0, top
multiplicity and imported axioms are unchanged. Top-vs-B remains OPEN.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- If an operator is norm-nonexpansive, its actual squared-norm power
orbit is stepwise nonincreasing. This is independent of spectral rank. -/
theorem realHilbert_contracting_power_normSq_succ_le_ake
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E) (hS : ‖S‖ ≤ 1) (x : E) (n : ℕ) :
    ‖(S ^ (n + 1)) x‖ ^ 2 ≤ ‖(S ^ n) x‖ ^ 2 := by
  have hEq : (S ^ (n + 1)) x = S ((S ^ n) x) := by
    rw [show n + 1 = 1 + n by omega, pow_add, pow_one]
    rfl
  have hStep : ‖(S ^ (n + 1)) x‖ ≤ ‖(S ^ n) x‖ := by
    rw [hEq]
    calc
      ‖S ((S ^ n) x)‖ ≤ ‖S‖ * ‖(S ^ n) x‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1 : ℝ) * ‖(S ^ n) x‖ :=
        mul_le_mul_of_nonneg_right hS (norm_nonneg _)
      _ = ‖(S ^ n) x‖ := one_mul _
  exact pow_le_pow_left₀ (norm_nonneg _) hStep 2

/-- A strict power-budget witness cannot disappear at any later
power under an actual norm-one transfer. -/
theorem realHilbert_contracting_power_normSq_antitone_ake
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E) (hS : ‖S‖ ≤ 1) (x : E)
    (n m : ℕ) (hnm : n ≤ m) :
    ‖(S ^ m) x‖ ^ 2 ≤ ‖(S ^ n) x‖ ^ 2 := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
      exact (realHilbert_contracting_power_normSq_succ_le_ake S hS x k).trans ih

local notation "GE" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKE_group : IsTopologicalGroup GE :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKE_compact : CompactSpace GE :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKE_secondCountable : SecondCountableTopology GE :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKE_measurable : MeasurableSpace GE :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKE_borel : BorelSpace GE :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKE_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "PhysE" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muE" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fE" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SE" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "TopE" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "RE" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "VE" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "uE" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mE" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "CE" =>
  p4Q2PZ37AJV_originalQFreeCorrection H

local instance p4Q2PZ37AKE_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AKE_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- The original normalized Wilson operator has norm exactly one, hence
the genuine physical source's powers are monotone in squared L2 energy. -/
theorem p4Q2PZ37AKE_originalSource_power_energy_antitone
    (beta : ℝ) (hbeta : 0 < beta)
    (n k : ℕ) (hnk : n ≤ k) :
    ‖((SE beta hbeta.le) ^ k) fE‖ ^ 2 ≤
      ‖((SE beta hbeta.le) ^ n) fE‖ ^ 2 := by
  have hS : ‖(SE beta hbeta.le : PhysE →L[ℝ] PhysE)‖ ≤ 1 := by
    rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
      H 2 (by norm_num) beta hbeta.le]
  exact realHilbert_contracting_power_normSq_antitone_ake
    (SE beta hbeta.le) hS fE n k hnk

/-- Persistence is for the unchanged ORIGINAL signed ZW source and
unchanged negative Haar region; not for a substitute test or source. -/
theorem p4Q2PZ37AKE_originalAJA_witness_persists
    (beta : ℝ) (hbeta : 0 < beta) (n k : ℕ) (hnk : n ≤ k)
    (hWitness :
      ‖((SE beta hbeta.le) ^ n) fE‖ ^ 2 <
        (mE beta hbeta.le) ^ 2 *
          Measure.real muE
            {U : CfgE | uE beta hbeta.le U < -(mE beta hbeta.le)}) :
    ‖((SE beta hbeta.le) ^ k) fE‖ ^ 2 <
      (mE beta hbeta.le) ^ 2 *
        Measure.real muE
          {U : CfgE | uE beta hbeta.le U < -(mE beta hbeta.le)} :=
  (p4Q2PZ37AKE_originalSource_power_energy_antitone
    H beta hbeta n k hnk).trans_lt hWitness

/-- A genuine strict finite AJA power witness exists iff there is
a fixed starting exponent N>=2 after which ALL powers are witnesses.
No claim that either side actually holds is made here. -/
theorem p4Q2PZ37AKE_originalAJA_exists_iff_eventual_all_power_witnesses
    (beta : ℝ) (hbeta : 0 < beta) :
    (∃ n : ℕ, 0 < n ∧
      ‖((SE beta hbeta.le) ^ n) fE‖ ^ 2 <
        (mE beta hbeta.le) ^ 2 *
          Measure.real muE
            {U : CfgE | uE beta hbeta.le U < -(mE beta hbeta.le)}) ↔
    (∃ N : ℕ, 2 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      ‖((SE beta hbeta.le) ^ k) fE‖ ^ 2 <
        (mE beta hbeta.le) ^ 2 *
          Measure.real muE
            {U : CfgE | uE beta hbeta.le U < -(mE beta hbeta.le)}) := by
  constructor
  · rintro ⟨n, hn, hWitness⟩
    have hNotOne : n ≠ 1 := by
      intro heq
      subst n
      exact (p4Q2PZ37AJI_no_firstPower_budget H beta hbeta)
        (by simpa only [pow_one] using hWitness)
    have hnTwo : 2 ≤ n := by omega
    exact ⟨n, hnTwo, fun k hnk =>
      p4Q2PZ37AKE_originalAJA_witness_persists
        H beta hbeta n k hnk hWitness⟩
  · rintro ⟨N, hN, hEvery⟩
    exact ⟨N, by omega, hEvery N le_rfl⟩

/-- Exact ORIGINAL AJA conditional goal expressed as an eventual entire
power tail: stronger quantifier form than AJI's mere existence. -/
theorem p4Q2PZ37AKE_originalFullTop_small_iff_eventual_all_power_witnesses
    (beta : ℝ) (hbeta : 0 < beta) :
    (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mE beta hbeta.le) ^ 2 *
        Measure.real muE
          {U : CfgE | uE beta hbeta.le U < -(mE beta hbeta.le)}) ↔
    (∃ N : ℕ, 2 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      ‖((SE beta hbeta.le) ^ k) fE‖ ^ 2 <
        (mE beta hbeta.le) ^ 2 *
          Measure.real muE
            {U : CfgE | uE beta hbeta.le U < -(mE beta hbeta.le)}) := by
  exact (p4Q2PZ37AJI_fullTop_small_iff_exists_transferPower_budget
    H beta hbeta).trans
      (p4Q2PZ37AKE_originalAJA_exists_iff_eventual_all_power_witnesses
        H beta hbeta)

/-- For any explicit finite n>0, an actual geometric top-tail numerical
certificate would suffice for a genuine AJA witness at that very n.
The premise is an OPEN measurement, not an unconditional estimate. -/
theorem p4Q2PZ37AKE_originalExactPower_geometric_square_test
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) (hn : 0 < n)
    (hBudget :
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
        (‖RE beta hbeta.le‖ ^ n *
          ‖((TopE beta hbeta.le)ᗮ).starProjection fE‖) ^ 2 <
          (mE beta hbeta.le) ^ 2 *
            Measure.real muE
              {U : CfgE | uE beta hbeta.le U < -(mE beta hbeta.le)}) :
    ‖((SE beta hbeta.le) ^ n) fE‖ ^ 2 <
      (mE beta hbeta.le) ^ 2 *
        Measure.real muE
          {U : CfgE | uE beta hbeta.le U < -(mE beta hbeta.le)} := by
  have hSplit :=
    p4Q2PZ37AJZ_originalSource_power_sq_eq_fullTop_add_exactTail
      H beta hbeta n
  have hTail :=
    p4Q2PZ37AJI_originalSource_power_sub_fullTop_norm_le
      H beta hbeta n hn
  have hTailSq :
      ‖((SE beta hbeta.le) ^ n) fE -
        p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 ≤
        (‖RE beta hbeta.le‖ ^ n *
          ‖((TopE beta hbeta.le)ᗮ).starProjection fE‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hTail 2
  linarith only [hSplit, hTailSq, hBudget]

/-- Unconditional (but weaker-than-AJA) strict finite-power decay from
the TRUE AJV q-free source defect. The bound V-C/2 may exceed B;
this theorem does not claim an AJA witness. -/
theorem p4Q2PZ37AKE_originalQFree_exists_finite_variance_drop
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ n : ℕ, 2 ≤ n ∧
      ‖((SE beta hbeta.le) ^ n) fE‖ ^ 2 <
        VE - CE beta / 2 := by
  have hBudget :=
    p4Q2PZ37AJV_originalFullTop_sq_add_qfree_le_variance H beta hbeta
  have hC : 0 < CE beta :=
    p4Q2PZ37AJV_originalQFreeCorrection_pos H beta hbeta
  have hTop :
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
        VE - CE beta / 2 := by
    linarith only [hBudget, hC]
  have hlim :=
    p4Q2PZ37AJI_originalSource_power_succ_tendsto_fullTop H beta hbeta
  have hSq :
      Tendsto (fun n : ℕ => ‖((SE beta hbeta.le) ^ (n + 1)) fE‖ ^ 2)
        atTop
        (nhds (‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2)) :=
    hlim.norm.pow 2
  have hEvent :
      ∀ᶠ n : ℕ in atTop,
        ‖((SE beta hbeta.le) ^ (n + 1)) fE‖ ^ 2 <
          VE - CE beta / 2 :=
    hSq.eventually (isOpen_Iio.mem_nhds hTop)
  obtain ⟨N, hEvery⟩ := (Filter.eventually_atTop.1 hEvent)
  refine ⟨(max N 1) + 1, by omega, ?_⟩
  exact hEvery (max N 1) (le_max_left _ _)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Eight independent kernel axiom audits, no new axioms or admitted goals. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_contracting_power_normSq_succ_le_ake
#print axioms MGAP4D.MathlibAnalytic.realHilbert_contracting_power_normSq_antitone_ake
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKE_originalSource_power_energy_antitone
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKE_originalAJA_witness_persists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKE_originalAJA_exists_iff_eventual_all_power_witnesses
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKE_originalFullTop_small_iff_eventual_all_power_witnesses
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKE_originalExactPower_geometric_square_test
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKE_originalQFree_exists_finite_variance_drop
