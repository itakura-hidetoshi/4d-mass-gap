import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAJUSecondPowerBudgetNoGoV5_PZ37AJY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalOrthogonalPowerSquareBudgetV5_PZ37AJN
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJZ — exact finite Wilson power vs ORIGINAL AJA Haar budget

AJY has ruled out the coarse AJU sufficient test V-C2<B. Instead of
repeating an impossible sufficient inequality, we use AJN's exact
orthogonal Pythagoras, the actual Wilson S, the full (not rank-one)
fixed top Q, and the original signed centered ZW source f0.

For EVERY finite integer power n, with no approximation:

  ||S^n f0||² = ||Q f0||² + ||S^n f0 - Q f0||².

Therefore the actual AJA budget test is exactly equivalent to:

  ||S^n f0 - Q f0||² < B - ||Q f0||²,

where B is unchanged original AJA positive Haar-margin certificate.
At n=2 this is a literal exact diagnostic, not AJU's loose V-C2
upper-bound surrogate. Any positive n=1 witness is already impossible
by AJI, so a true positive finite AJA witness is equivalent to an
actual residual test at SOME n>=2.

No strict residual estimate versus B, explicit witness, absence of
witnesses, top simplicity, uniform coercivity or 4D mass gap is
asserted here. The unresolved original-Haar numerical comparison
must be retained as NO_DATA, not certified by this equivalence.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Exact squared full-top split for ANY true symmetric transfer whose
complete fixed subspace F is projected orthogonally. Reuses the AJN
Pythagoras theorem with selected direction zero; no scalar surrogate
or triangle-inequality relaxation is introduced. -/
theorem realHilbert_fixedSubspace_power_sq_eq_top_add_exactTail_ajz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hFix : ∀ v : E, v ∈ F → S v = v)
    (n : ℕ) (x : E) :
    ‖(S ^ n) x‖ ^ 2 =
      ‖F.starProjection x‖ ^ 2 +
        ‖(S ^ n) x - F.starProjection x‖ ^ 2 := by
  have h := realHilbert_fixedSubspace_selectedPower_sq_split_ajn
    F S hSymm hFix n x (0 : E) F.zero_mem
  simpa using h

/-- Exact algebraic equivalence of the strict finite-power AJA-like
budget with a true Hilbert tail budget; no positive budget is assumed. -/
theorem realHilbert_fixedSubspace_power_lt_budget_iff_exactTail_ajz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hFix : ∀ v : E, v ∈ F → S v = v)
    (n : ℕ) (x : E) (B : ℝ) :
    (‖(S ^ n) x‖ ^ 2 < B) ↔
      (‖(S ^ n) x - F.starProjection x‖ ^ 2 <
        B - ‖F.starProjection x‖ ^ 2) := by
  have hSplit :=
    realHilbert_fixedSubspace_power_sq_eq_top_add_exactTail_ajz
      F S hSymm hFix n x
  constructor
  · intro hSmall
    linarith only [hSplit, hSmall]
  · intro hTail
    linarith only [hSplit, hTail]

local notation "GZ" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AJZ_group : IsTopologicalGroup GZ :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AJZ_compact : CompactSpace GZ :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AJZ_secondCountable : SecondCountableTopology GZ :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AJZ_measurable : MeasurableSpace GZ :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AJZ_borel : BorelSpace GZ :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AJZ_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysZ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgZ" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muZ" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fZ" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SZ" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "uZ" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mZ" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJZ_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJZ_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- EXACT full-top-plus-decaying-tail identity in the original SU(2)
Wilson/Haar physical Hilbert space for the actual signed ZW source.
The entire top fixed space is retained; no rank-one assumption. -/
theorem p4Q2PZ37AJZ_originalSource_power_sq_eq_fullTop_add_exactTail
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    ‖((SZ beta hbeta.le) ^ n) fZ‖ ^ 2 =
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 +
      ‖((SZ beta hbeta.le) ^ n) fZ -
        p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 := by
  let S : PhysZ →L[ℝ] PhysZ := SZ beta hbeta.le
  let F : Submodule ℝ PhysZ := realHilbertTopEigenspace S
  let hS : (S : PhysZ →ₗ[ℝ] PhysZ).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  have hFix : ∀ v : PhysZ, v ∈ F → S v = v := by
    intro v hv
    exact (realHilbertTopEigenspace_mem S v).mp hv
  change
    ‖(S ^ n) fZ‖ ^ 2 =
      ‖F.starProjection fZ‖ ^ 2 +
      ‖(S ^ n) fZ - F.starProjection fZ‖ ^ 2
  exact realHilbert_fixedSubspace_power_sq_eq_top_add_exactTail_ajz
    F S hS hFix n fZ

/-- The ORIGINAL AJA negative-Haar-region budget B is used unchanged.
This is a strict IFF for the ACTUAL finite Wilson power and ACTUAL
orthogonal decaying tail (not the AJU coarse upper estimate). -/
theorem p4Q2PZ37AJZ_originalPower_AJA_iff_exactFullTopTail
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    (‖((SZ beta hbeta.le) ^ n) fZ‖ ^ 2 <
      (mZ beta hbeta.le) ^ 2 *
        Measure.real muZ
          {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)}) ↔
    (‖((SZ beta hbeta.le) ^ n) fZ -
        p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mZ beta hbeta.le) ^ 2 *
        Measure.real muZ
          {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)} -
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2) := by
  have hSplit :=
    p4Q2PZ37AJZ_originalSource_power_sq_eq_fullTop_add_exactTail
      H beta hbeta n
  constructor
  · intro hPower
    linarith only [hSplit, hPower]
  · intro hTail
    linarith only [hSplit, hTail]

/-- Literal n=2 exact AJA diagnostic. Distinct from AJU's unfulfillable
numerical SUFFICIENT threshold V-C2<B. Neither side is proved true. -/
theorem p4Q2PZ37AJZ_originalSecondPower_AJA_iff_exactFullTopTail
    (beta : ℝ) (hbeta : 0 < beta) :
    (‖((SZ beta hbeta.le) ^ 2) fZ‖ ^ 2 <
      (mZ beta hbeta.le) ^ 2 *
        Measure.real muZ
          {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)}) ↔
    (‖((SZ beta hbeta.le) ^ 2) fZ -
        p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mZ beta hbeta.le) ^ 2 *
        Measure.real muZ
          {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)} -
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2) :=
  p4Q2PZ37AJZ_originalPower_AJA_iff_exactFullTopTail H beta hbeta 2

/-- One original AJA finite positive-power witness exists IFF
there is an actual strict residual budget test at some n>=2.
AJI already rules out n=1. This is a conditional test, not an
unconditional witness or a numerical evaluation of either side. -/
theorem p4Q2PZ37AJZ_originalAJA_existsPositivePower_iff_exists_n_ge_two_exactTail
    (beta : ℝ) (hbeta : 0 < beta) :
    (∃ n : ℕ, 0 < n ∧
      ‖((SZ beta hbeta.le) ^ n) fZ‖ ^ 2 <
        (mZ beta hbeta.le) ^ 2 *
          Measure.real muZ
            {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)}) ↔
    (∃ n : ℕ, 2 ≤ n ∧
      ‖((SZ beta hbeta.le) ^ n) fZ -
        p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
        (mZ beta hbeta.le) ^ 2 *
          Measure.real muZ
            {B : CfgZ | uZ beta hbeta.le B < -(mZ beta hbeta.le)} -
        ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2) := by
  constructor
  · rintro ⟨n, hn, hPower⟩
    have hnNeOne : n ≠ 1 := by
      intro hOne
      subst n
      have hFirst := p4Q2PZ37AJI_no_firstPower_budget H beta hbeta
      apply hFirst
      simpa only [pow_one] using hPower
    have hnTwo : 2 ≤ n := by omega
    exact ⟨n, hnTwo,
      (p4Q2PZ37AJZ_originalPower_AJA_iff_exactFullTopTail
        H beta hbeta n).1 hPower⟩
  · rintro ⟨n, hnTwo, hTail⟩
    refine ⟨n, by omega, ?_⟩
    exact (p4Q2PZ37AJZ_originalPower_AJA_iff_exactFullTopTail
      H beta hbeta n).2 hTail

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Six new declarations, all audited against the actual Lean kernel. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fixedSubspace_power_sq_eq_top_add_exactTail_ajz
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fixedSubspace_power_lt_budget_iff_exactTail_ajz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJZ_originalSource_power_sq_eq_fullTop_add_exactTail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJZ_originalPower_AJA_iff_exactFullTopTail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJZ_originalSecondPower_AJA_iff_exactFullTopTail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJZ_originalAJA_existsPositivePower_iff_exists_n_ge_two_exactTail
