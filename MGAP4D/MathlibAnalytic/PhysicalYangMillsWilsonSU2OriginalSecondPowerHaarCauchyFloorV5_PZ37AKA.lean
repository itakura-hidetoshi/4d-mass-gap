import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExactPowerAJABudgetResidualV5_PZ37AJZ
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKA — original Wilson second-power Haar-Cauchy floor

AJZ certified an EXACT full-top/orthogonal-tail criterion for each actual
Wilson source power, without showing the original AJA strict budget holds.

This leaf gives an INDEPENDENT lower bound on the ACTUAL n=2 power.
For a symmetric real-Hilbert continuous linear operator S, Cauchy-Schwarz
and exact symmetry imply

  (||S x||²)² <= ||x||² * ||S² x||².

AJA already provides a strictly positive original Haar certificate
  B = m² * Measure.real(mu)({u < -m}) <= ||S f0||².
AJR identifies V = ||f0||² > 0, so at every fixed finite H, beta>0:

  B² / V <= ||S² f0||², with 0 < B²/V < B.

Thus the original Wilson *second* power is nonzero, and any true
n=2 strict AJA witness would need to lie in the explicit interval
  B²/V <= ||S² f0||² < B.

This floor does NOT prove n=2 exceeds B, nor produce a finite witness.
It is no uniform H bound or Hamiltonian/continuum mass gap.
No definitions of Wilson transfer, source, top, AJA certificate,
physical Hilbert space, Haar measure, Lean pin or root are changed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Cauchy--Schwarz and actual selfadjointness give a lower numerical
second-power energy inequality; no operator positivity or top rank-one
assumption is required. -/
theorem realHilbert_symmetric_secondPower_normSq_Cauchy_aka
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) :
    (‖S x‖ ^ 2) ^ 2 ≤ ‖x‖ ^ 2 * ‖(S ^ 2) x‖ ^ 2 := by
  have hInner : ‖S x‖ ^ 2 = inner ℝ x (S (S x)) := by
    calc
      ‖S x‖ ^ 2 = inner ℝ (S x) (S x) :=
        (real_inner_self_eq_norm_sq (S x)).symm
      _ = inner ℝ x (S (S x)) := hSymm x (S x)
  have hCS : ‖S x‖ ^ 2 ≤ ‖x‖ * ‖S (S x)‖ := by
    calc
      ‖S x‖ ^ 2 = inner ℝ x (S (S x)) := hInner
      _ ≤ ‖x‖ * ‖S (S x)‖ := real_inner_le_norm x (S (S x))
  have hNonneg : 0 ≤ ‖x‖ * ‖S (S x)‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hCSsq :
      (‖S x‖ ^ 2) ^ 2 ≤ (‖x‖ * ‖S (S x)‖) ^ 2 :=
    (sq_le_sq₀ (sq_nonneg _) hNonneg).2 hCS
  have hTwo : (S ^ 2) x = S (S x) := by
    rw [pow_two]
    rfl
  calc
    (‖S x‖ ^ 2) ^ 2 ≤ (‖x‖ * ‖S (S x)‖) ^ 2 := hCSsq
    _ = ‖x‖ ^ 2 * ‖(S ^ 2) x‖ ^ 2 := by
      rw [hTwo]
      ring

/-- Transports an already certified nonnegative one-step margin through
the exact Cauchy lower inequality. This does not assume a witness. -/
theorem realHilbert_oneStep_margin_secondPower_Cauchy_aka
    (B a V w : ℝ)
    (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hBA : B ≤ a) (hCS : a ^ 2 ≤ V * w) :
    B ^ 2 ≤ V * w := by
  exact ((sq_le_sq₀ hB ha).2 hBA).trans hCS

local notation "GA" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKA_group : IsTopologicalGroup GA :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKA_compact : CompactSpace GA :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKA_secondCountable : SecondCountableTopology GA :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKA_measurable : MeasurableSpace GA :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKA_borel : BorelSpace GA :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKA_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysA" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgA" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muA" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fA" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SA" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "VA" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "uA" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mA" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AKA_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

/-- ORIGINAL exact physical second Wilson power has an unconditional
strict-Haar-certificate squared lower bound. This is a bound on the
ACTUAL n=2 energy, not on the AJU loose upper threshold. -/
theorem p4Q2PZ37AKA_originalSecondPower_sq_mul_variance_ge_AJA_sq
    (beta : ℝ) (hbeta : 0 < beta) :
    ((mA beta hbeta.le) ^ 2 *
      Measure.real muA
        {B : CfgA | uA beta hbeta.le B < -(mA beta hbeta.le)}) ^ 2 ≤
      VA * ‖((SA beta hbeta.le) ^ 2) fA‖ ^ 2 := by
  let S : PhysA →L[ℝ] PhysA := SA beta hbeta.le
  have hSymm : (S : PhysA →ₗ[ℝ] PhysA).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hCS :
      (‖S fA‖ ^ 2) ^ 2 ≤ ‖fA‖ ^ 2 * ‖(S ^ 2) fA‖ ^ 2 :=
    realHilbert_symmetric_secondPower_normSq_Cauchy_aka S hSymm fA
  have hVariance := p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance H
  have hCS' :
      (‖S fA‖ ^ 2) ^ 2 ≤ VA * ‖(S ^ 2) fA‖ ^ 2 := by
    calc
      (‖S fA‖ ^ 2) ^ 2 ≤ ‖fA‖ ^ 2 * ‖(S ^ 2) fA‖ ^ 2 := hCS
      _ = VA * ‖(S ^ 2) fA‖ ^ 2 := by rw [hVariance]
  let B : ℝ :=
    (mA beta hbeta.le) ^ 2 *
      Measure.real muA
        {U : CfgA | uA beta hbeta.le U < -(mA beta hbeta.le)}
  have hBA : B ≤ ‖S fA‖ ^ 2 :=
    p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
      H beta hbeta
  have hBpos : 0 < B :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hFloor := realHilbert_oneStep_margin_secondPower_Cauchy_aka
    B (‖S fA‖ ^ 2) VA (‖(S ^ 2) fA‖ ^ 2)
    hBpos.le (sq_nonneg _) hBA hCS'
  exact hFloor

/-- Division by the genuine positive Haar variance yields a real
positive quantitative original second-power norm floor. -/
theorem p4Q2PZ37AKA_originalSecondPower_sq_ge_AJA_square_div_variance
    (beta : ℝ) (hbeta : 0 < beta) :
    (((mA beta hbeta.le) ^ 2 *
      Measure.real muA
        {B : CfgA | uA beta hbeta.le B < -(mA beta hbeta.le)}) ^ 2) / VA ≤
      ‖((SA beta hbeta.le) ^ 2) fA‖ ^ 2 := by
  have hV : 0 < VA :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hBound :=
    p4Q2PZ37AKA_originalSecondPower_sq_mul_variance_ge_AJA_sq
      H beta hbeta
  apply (div_le_iff₀ hV).2
  nlinarith only [hBound]

/-- Physical second-power nonvanishing follows with no unknown top rank
or AJA strict upper criterion: B>0, V>0 and B²/V<=||S²f0||². -/
theorem p4Q2PZ37AKA_originalSecondPower_sq_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < ‖((SA beta hbeta.le) ^ 2) fA‖ ^ 2 := by
  have hV : 0 < VA :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hB :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hFloor :=
    p4Q2PZ37AKA_originalSecondPower_sq_ge_AJA_square_div_variance
      H beta hbeta
  have hPos :
      0 <
      (((mA beta hbeta.le) ^ 2 *
        Measure.real muA
          {B : CfgA | uA beta hbeta.le B < -(mA beta hbeta.le)}) ^ 2) / VA :=
    div_pos (sq_pos_of_pos hB) hV
  exact hPos.trans_le hFloor

/-- The certified n=2 energy floor is itself BELOW the AJA margin
certificate, so this new lower bound does not rule out an n=2 witness. -/
theorem p4Q2PZ37AKA_originalAJA_square_div_variance_lt_AJA
    (beta : ℝ) (hbeta : 0 < beta) :
    (((mA beta hbeta.le) ^ 2 *
      Measure.real muA
        {B : CfgA | uA beta hbeta.le B < -(mA beta hbeta.le)}) ^ 2) / VA <
    (mA beta hbeta.le) ^ 2 *
      Measure.real muA
        {B : CfgA | uA beta hbeta.le B < -(mA beta hbeta.le)} := by
  let B : ℝ :=
    (mA beta hbeta.le) ^ 2 *
      Measure.real muA
        {U : CfgA | uA beta hbeta.le U < -(mA beta hbeta.le)}
  have hB : 0 < B :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hV : 0 < VA :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hCap : B ≤ VA / 16 :=
    p4Q2PZ37AJX_originalAJA_certificate_le_sixteenth_variance
      H beta hbeta
  have hLess : B < VA := by linarith only [hCap, hV]
  have hProduct : 0 < B * (VA - B) :=
    mul_pos hB (sub_pos.mpr hLess)
  have hSq : B ^ 2 < B * VA := by
    nlinarith only [hProduct]
  apply (div_lt_iff₀ hV).2
  nlinarith only [hSq]

/-- If an original second-power AJA witness is separately proved,
its exact genuine energy has a narrow but nonempty necessary interval.
Neither the antecedent nor unconditional AJA witness is proved here. -/
theorem p4Q2PZ37AKA_originalSecondPower_AJA_witness_interval
    (beta : ℝ) (hbeta : 0 < beta)
    (hPower :
      ‖((SA beta hbeta.le) ^ 2) fA‖ ^ 2 <
      (mA beta hbeta.le) ^ 2 *
        Measure.real muA
          {B : CfgA | uA beta hbeta.le B < -(mA beta hbeta.le)}) :
    (((mA beta hbeta.le) ^ 2 *
      Measure.real muA
        {B : CfgA | uA beta hbeta.le B < -(mA beta hbeta.le)}) ^ 2) / VA ≤
      ‖((SA beta hbeta.le) ^ 2) fA‖ ^ 2 ∧
    ‖((SA beta hbeta.le) ^ 2) fA‖ ^ 2 <
      (mA beta hbeta.le) ^ 2 *
        Measure.real muA
          {B : CfgA | uA beta hbeta.le B < -(mA beta hbeta.le)} :=
  ⟨p4Q2PZ37AKA_originalSecondPower_sq_ge_AJA_square_div_variance
      H beta hbeta, hPower⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Seven new statements, seven independent actual kernel axiom audits. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_symmetric_secondPower_normSq_Cauchy_aka
#print axioms MGAP4D.MathlibAnalytic.realHilbert_oneStep_margin_secondPower_Cauchy_aka
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKA_originalSecondPower_sq_mul_variance_ge_AJA_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKA_originalSecondPower_sq_ge_AJA_square_div_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKA_originalSecondPower_sq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKA_originalAJA_square_div_variance_lt_AJA
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKA_originalSecondPower_AJA_witness_interval
