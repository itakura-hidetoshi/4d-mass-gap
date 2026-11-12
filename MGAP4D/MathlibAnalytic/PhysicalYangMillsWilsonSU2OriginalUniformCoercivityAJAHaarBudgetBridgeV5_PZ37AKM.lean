import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUniformTopOrthogonalCoercivityV5_PZ37AKL
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAJAEventualPowerWitnessV5_PZ37AKE
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalMassSquaredWardFullTopFloorV5_PZ37AKK
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAJAAbsoluteSixteenthSectorCriterionV5_PZ37AJX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKM: the original AJA Haar budget versus uniform coercivity

No source, operator, Haar region, margin or coupling is replaced.
For every original finite H and every positive beta in AKL's common interval,
the actual Wilson orbit is trapped between the AKK mass-squared Ward floor
and an explicit uniform-rate full-top-plus-excited-tail envelope.

    L_(H,beta) <= ||S^n f0||²
       <= ||Q f0||² + ((3071/3072)^n ||Q^perp f0||)².

The unchanged original AJA budget B satisfies B<=V/16. An upper-envelope
comparison strictly below B is sufficient for the ORIGINAL finite-power
witness. Conversely, B<=L excludes every such witness. Small-coupling AKI
no-witness and AKL coercivity can hold simultaneously.

In particular, neither H-uniform coercivity nor the positive AKK floor
certifies that ||Q f0||² < B. No unconditional AJA witness, numerical beta0
inclusion, common uniform witness exponent, Hamiltonian or continuum gap
is claimed. No existing imported declaration or proof is weakened.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "GM" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKM_group : IsTopologicalGroup GM :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKM_compact : CompactSpace GM :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKM_countable : SecondCountableTopology GM :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKM_measurable : MeasurableSpace GM :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKM_borel : BorelSpace GM :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKM_links (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysM" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgM" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muM" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fM" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SM" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RM" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "TopM" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "uM" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mM" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "VM" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "LM" => p4Q2PZ37AKK_originalMassSquaredWardFloor H
local notation "qM" => (3071 / 3072 : ℝ)

local instance p4Q2PZ37AKM_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AKM_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- The exact ORIGINAL source orbit is bounded above by the full top energy
plus a geometric excited-tail energy, with one H-independent coefficient. -/
theorem p4Q2PZ37AKM_originalPower_uniformGeometricEnvelope
    (beta : ℝ) (hbeta : 0 < beta)
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff)
    (n : ℕ) (hn : 0 < n) :
    ‖((SM beta hbeta.le) ^ n) fM‖ ^ 2 ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
        (qM ^ n *
          ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖) ^ 2 := by
  have hR :
      ‖RM beta hbeta.le‖ ≤ qM :=
    p4Q2PZ37AKL_originalTopOrthogonal_norm_le
      H beta hbeta.le hcut
  have hRnonneg : (0 : ℝ) ≤ ‖RM beta hbeta.le‖ :=
    norm_nonneg (RM beta hbeta.le)
  have hRpow :
      ‖RM beta hbeta.le‖ ^ n ≤ qM ^ n :=
    pow_le_pow_left₀ hRnonneg hR n
  have hMul :
      ‖RM beta hbeta.le‖ ^ n *
        ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖ ≤
      qM ^ n * ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖ :=
    mul_le_mul_of_nonneg_right hRpow (norm_nonneg _)
  have hTail :=
    p4Q2PZ37AJI_originalSource_power_sub_fullTop_norm_le
      H beta hbeta n hn
  have hTailRate :
      ‖((SM beta hbeta.le) ^ n) fM -
        p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ≤
      qM ^ n * ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖ :=
    hTail.trans hMul
  have hTailSq :
      ‖((SM beta hbeta.le) ^ n) fM -
        p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 ≤
      (qM ^ n * ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hTailRate 2
  calc
    ‖((SM beta hbeta.le) ^ n) fM‖ ^ 2 =
        ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
        ‖((SM beta hbeta.le) ^ n) fM -
          p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 :=
      p4Q2PZ37AJZ_originalSource_power_sq_eq_fullTop_add_exactTail
        H beta hbeta n
    _ ≤
        ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
        (qM ^ n *
          ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖) ^ 2 :=
      add_le_add_left hTailSq _

/-- The unconditional ORIGINAL quantitative sandwich and actual Haar
certificate ceiling, for one and the same finite H, beta, physical f0 and S. -/
theorem p4Q2PZ37AKM_originalAJA_HaarWardCoercivitySandwich
    (beta : ℝ) (hbeta : 0 < beta)
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff)
    (n : ℕ) (hn : 0 < n) :
    LM beta hbeta ≤
        ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 ∧
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 ≤
        ‖((SM beta hbeta.le) ^ n) fM‖ ^ 2 ∧
    ‖((SM beta hbeta.le) ^ n) fM‖ ^ 2 ≤
        ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
          (qM ^ n * ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖) ^ 2 ∧
    (mM beta hbeta.le) ^ 2 *
      Measure.real muM
        {A : CfgM | uM beta hbeta.le A < -(mM beta hbeta.le)}
      ≤ VM / 16 := by
  exact ⟨
    p4Q2PZ37AKK_originalFullTop_energy_ge_massSquaredWardFloor H beta hbeta,
    p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower H beta hbeta n,
    p4Q2PZ37AKM_originalPower_uniformGeometricEnvelope H beta hbeta hcut n hn,
    p4Q2PZ37AJX_originalAJA_certificate_le_sixteenth_variance H beta hbeta
  ⟩

/-- A direct computable sufficient test for the strict ORIGINAL AJA Haar
budget, with AKL's universal rate instead of an H-dependent restriction norm.
The numerical premise is not assumed to hold automatically. -/
theorem p4Q2PZ37AKM_originalAJA_witness_of_uniformEnvelope_below_budget
    (beta : ℝ) (hbeta : 0 < beta)
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff)
    (n : ℕ) (hn : 0 < n)
    (hBudget :
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
        (qM ^ n * ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖) ^ 2 <
      (mM beta hbeta.le) ^ 2 *
        Measure.real muM
          {A : CfgM | uM beta hbeta.le A < -(mM beta hbeta.le)}) :
    ‖((SM beta hbeta.le) ^ n) fM‖ ^ 2 <
      (mM beta hbeta.le) ^ 2 *
        Measure.real muM
          {A : CfgM | uM beta hbeta.le A < -(mM beta hbeta.le)} :=
  (p4Q2PZ37AKM_originalPower_uniformGeometricEnvelope
    H beta hbeta hcut n hn).trans_lt hBudget

/-- Any putative actual AJA witness must separately pass the original
AKK Ward floor, the true full-top test and AJX's 15/16 angle test. -/
theorem p4Q2PZ37AKM_originalAJA_witness_necessaryWardTopAngle
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ)
    (hWitness :
      ‖((SM beta hbeta.le) ^ n) fM‖ ^ 2 <
        (mM beta hbeta.le) ^ 2 *
          Measure.real muM
            {A : CfgM | uM beta hbeta.le A < -(mM beta hbeta.le)}) :
    LM beta hbeta <
        (mM beta hbeta.le) ^ 2 *
          Measure.real muM
            {A : CfgM | uM beta hbeta.le A < -(mM beta hbeta.le)} ∧
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
        (mM beta hbeta.le) ^ 2 *
          Measure.real muM
            {A : CfgM | uM beta hbeta.le A < -(mM beta hbeta.le)} ∧
    15 * VM / 16 <
        ‖((TopM beta hbeta.le)ᗮ).starProjection fM‖ ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact p4Q2PZ37AKK_originalAJA_witness_requires_floor_lt_budget
      H beta hbeta ⟨n, hWitness⟩
  · exact (p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower
      H beta hbeta n).trans_lt hWitness
  · exact
      p4Q2PZ37AJX_originalPower_budget_implies_excitedSource_gt_fifteenSixteenths
        H beta hbeta n hWitness

/-- Coercivity and the genuine AKI no-witness theorem coexist on the
overlap with AKI's logarithmic interval. This expressly blocks illicit
promotion from an excitation-sector gap to an unconditional AJA witness. -/
theorem p4Q2PZ37AKM_originalUniformCoercivity_and_logarithmicAJANoGo
    (beta : ℝ) (hbeta : 0 < beta)
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff)
    (hlog : beta ≤ p4Q2PZ37AKI_logarithmicNoWitnessCutoff H) :
    ‖RM beta hbeta.le‖ ≤ qM ∧
    ¬ ∃ n : ℕ, ‖((SM beta hbeta.le) ^ n) fM‖ ^ 2 <
      (mM beta hbeta.le) ^ 2 *
        Measure.real muM
          {A : CfgM | uM beta hbeta.le A < -(mM beta hbeta.le)} := by
  exact ⟨
    p4Q2PZ37AKL_originalTopOrthogonal_norm_le H beta hbeta.le hcut,
    p4Q2PZ37AKI_originalLog_no_AJA_power_witness H beta hbeta hlog
  ⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKM_originalPower_uniformGeometricEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKM_originalAJA_HaarWardCoercivitySandwich
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKM_originalAJA_witness_of_uniformEnvelope_below_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKM_originalAJA_witness_necessaryWardTopAngle
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKM_originalUniformCoercivity_and_logarithmicAJANoGo
