import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGIMinorNonzeroFineSlopeV5_PZ37ZJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZK — genuine physical Gauss-law source has a linear fine floor

The original SU(2) Wilson normalization scalar is NOT differentiated.
PZ37ZJ proves that the determinant of two genuine interacting-Wilson-
posterior signed GI receiver rows, applied to the constant spatial Haar
unit and the raw fine Wilson Haar row, has a strictly positive first-
order lower envelope |minor_raw(t)| >= c t at actual contexts.

This file packages the SAME true Wilson receiver rows into a bounded
real-linear functional K on the actual full spatial Haar-L²:
 K(f) := G_e(U) G_e'(f) - G_e'(U) G_e(f).
Thus K(U)=0 IDENTICALLY: its response is transverse to any scalar
normalization of the constant unit.

The literal physical normalized fine transfer source F_t=U-T_t U
satisfies K(F_t)=-||Raw_t||^-1 minor_raw(t). The true raw Wilson
operator norm has the original finite-H action-budget bound
||Raw_t|| <= 1+B_H on the small positive fine window 0<t<1.
By the actual continuous-linear detector op-norm inequality, obtain
an UNCONDITIONAL finite-volume physical Hilbert linear slope

    exists delta_H,b,c_H,b>0:
      c_H,b * t <= ||U-T_t U|| <= 2 B_H t,  0<t<delta_H,b.

This is the SAME Gauss-law physical Hilbert source and original
interacting-Wilson posterior; the constants depend on H,b and the
actual link/context witnesses. No artificial source, no independent
Haar posterior, no scalar normalization derivative, no new axiom,
sorry, admit, native_decide, no volume-uniform mass gap, endpoint E,
arbitrary-depth F or H1-H4. The normalized GL Rayleigh fine-limit
remains OPEN, distinct from this positive physical source slope.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37ZK_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZK_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZK_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZK_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZK_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37ZK_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The actual TWO-interacting-original-Wilson-posterior GI receiver
rows define a genuine continuous REAL-linear transverse functional
on the original full spatial Haar-L². Its source is NOT a new model. -/
noncomputable def p4Q2PZ37ZK_originalGITransverseCLM
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) →L[ℝ] ℝ :=
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let unitLp := ContinuousMap.toLp 2 haar ℝ
    (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))
  let G := p4Q2JH_originalGIResponseCLM H b hb.le
  (G e z unitLp) • G e' z' - (G e' z' unitLp) • G e z

/-- The determinant detector kills the exact Haar constant physical
source, so it is unaffected by ANY scalar multiple of that unit. -/
theorem p4Q2PZ37ZK_originalGITransverseCLM_constant_zero
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    p4Q2PZ37ZK_originalGITransverseCLM H b hb e e' z z'
      (ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))) = 0 := by
  unfold p4Q2PZ37ZK_originalGITransverseCLM
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- The TRUE physical cancellation, embedded isometrically in the
original spatial Haar L², has the exact normalization-free response.
The scalar Wilson transfer norm appears ONLY multiplicatively and
is not differentiated. -/
theorem p4Q2PZ37ZK_originalGITransverseCLM_cancellation_eq_rawMinor
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (z z' : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (t : Set.Ici (0 : ℝ)) :
    p4Q2PZ37ZK_originalGITransverseCLM H b hb e e' z z'
      ((p4Q2PZ37ZE_originalPhysicalCancellation H t :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
      -‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property‖⁻¹ *
        p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' (t : ℝ) := by
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ) →L[ℝ]
      Lp ℝ 2 haar := ContinuousMap.toLp 2 haar ℝ
  let F := p4Q2JF_originalWilsonHaarRowContinuous H
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let Raw := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let V := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property U
  let c : ℝ := ‖Raw‖⁻¹
  let G := p4Q2JH_originalGIResponseCLM H b hb.le
  let unitLp := L (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))
  let K := p4Q2PZ37ZK_originalGITransverseCLM H b hb e e' z z'
  have hU : (U : Lp ℝ 2 haar) = unitLp :=
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H
  have hV : (V : Lp ℝ 2 haar) = c • L (F (t : ℝ)) := by
    change c • ((Raw U :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 haar) = c • L (F (t : ℝ))
    rw [p4Q2JI_actualRawFineUnit_coe_eq_HaarRow H (t : ℝ) t.property]
  have hF :
      ((p4Q2PZ37ZE_originalPhysicalCancellation H t :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 haar) = (U : Lp ℝ 2 haar) - (V : Lp ℝ 2 haar) := by
    change ((U - V :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 haar) = (U : Lp ℝ 2 haar) - (V : Lp ℝ 2 haar)
    rfl
  have hUnitK : K unitLp = 0 :=
    p4Q2PZ37ZK_originalGITransverseCLM_constant_zero H b hb e e' z z'
  change K _ = -c * p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' (t : ℝ)
  rw [hF, map_sub, hU, hV, map_smul, hUnitK]
  dsimp [K, p4Q2PZ37ZK_originalGITransverseCLM,
    p4Q2JI_originalGIRawFineRowMinor, G, unitLp, L]
  ring

/-- The ORIGINAL raw one-slab physical Wilson operator norm is bounded
on 0≤fine≤1 by 1 plus its true finite-volume action budget. No
normalization differentiability or hidden volume-independent constant. -/
theorem p4Q2PZ37ZK_originalRawOperator_norm_le_one_add_budget
    (H : ℕ) (t : Set.Ici (0 : ℝ)) (ht : (t : ℝ) ≤ 1) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property‖ ≤
      1 + periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
  let R := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let Q := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
  let B := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hPert : ‖R - Q‖ ≤ B * (t : ℝ) := by
    simpa only [R, Q, B] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
        H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property)
  have hQ : ‖Q‖ = (1 : ℝ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm
      H 2 specialUnitaryTwoWilsonRankPositive
  have hNorm : ‖R‖ ≤ ‖R - Q‖ + ‖Q‖ := by
    calc
      ‖R‖ = ‖(R - Q) + Q‖ := by congr 1; abel
      _ ≤ ‖R - Q‖ + ‖Q‖ := norm_add_le (R - Q) Q
  have hScale : B * (t : ℝ) ≤ B := by
    nlinarith [mul_nonneg hB (sub_nonneg.mpr ht)]
  change ‖R‖ ≤ 1 + B
  linarith

/-- The actual original Gauss-law physical norm has both a positive
linear lower envelope and the previously proved explicit AQ/Zi upper
linear envelope, at fixed finite H,b for the same authentic Wilson
transfer. The lower witness comes from the ORIGINAL two-posterior GI
minor and a BOUNDED physical linear detector, not a rank hypothesis. -/
theorem p4Q2PZ37ZK_originalPhysicalCancellation_twoSided_linearFine
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink H)
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧
      ∀ t : Set.Ici (0 : ℝ), 0 < (t : ℝ) → (t : ℝ) < delta →
        c * (t : ℝ) ≤ ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ ∧
        ‖p4Q2PZ37ZE_originalPhysicalCancellation H t‖ ≤
          2 * p4Q2PZ37ZI_originalPhysicalWilsonActionBudget H * (t : ℝ) := by
  obtain ⟨z, z', delta₀, c₀, hDelta₀, hc₀, hMinor⟩ :=
    p4Q2PZ37ZJ_originalRawGIMinor_exists_linearLower
      H b hb e e' left₀ right₀
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  let K := p4Q2PZ37ZK_originalGITransverseCLM H b hb e e' z z'
  let C : ℝ := (1 + B) * (‖K‖ + 1)
  have hC : 0 < C := mul_pos (by dsimp [B]; linarith) (by positivity)
  let c : ℝ := c₀ / C
  have hc : 0 < c := div_pos hc₀ hC
  let delta : ℝ := min delta₀ 1
  have hdelta : 0 < delta := lt_min hDelta₀ (by norm_num)
  refine ⟨delta, c, hdelta, hc, ?_⟩
  intro t ht hsmall
  let Raw := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let f := p4Q2PZ37ZE_originalPhysicalCancellation H t
  have ht0 : (t : ℝ) < delta₀ :=
    lt_of_lt_of_le hsmall (min_le_left _ _)
  have ht1 : (t : ℝ) ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hsmall (min_le_right _ _))
  have hMinorLower :
      c₀ * (t : ℝ) ≤
        |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' (t : ℝ)| :=
    hMinor (t : ℝ) ht ht0
  have hRawPos : 0 < ‖Raw‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  have hRawCap : ‖Raw‖ ≤ 1 + B :=
    p4Q2PZ37ZK_originalRawOperator_norm_le_one_add_budget H t ht1
  have hDetector :
      K ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        -‖Raw‖⁻¹ *
          p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' (t : ℝ) := by
    exact p4Q2PZ37ZK_originalGITransverseCLM_cancellation_eq_rawMinor
      H b hb e e' z z' t
  have hExact :
      ‖Raw‖ *
        |K ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))| =
      |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' (t : ℝ)| := by
    rw [hDetector, abs_mul, abs_neg, abs_inv, abs_of_pos hRawPos]
    calc
      ‖Raw‖ * (‖Raw‖⁻¹ *
          |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' (t : ℝ)|) =
        (‖Raw‖ * ‖Raw‖⁻¹) *
          |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' (t : ℝ)| := by ring
      _ = _ := by rw [mul_inv_cancel₀ hRawPos.ne', one_mul]
  have hKBound :
      |K ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))| ≤
        (‖K‖ + 1) * ‖f‖ := by
    have h := K.le_opNorm
      ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
    have hBase :
        |K ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))| ≤
          ‖K‖ * ‖f‖ := by
      simpa only [Real.norm_eq_abs] using h
    nlinarith [norm_nonneg f]
  have hTotal : c₀ * (t : ℝ) ≤ C * ‖f‖ := by
    calc
      c₀ * (t : ℝ) ≤
          |p4Q2JI_originalGIRawFineRowMinor H b hb.le e e' z z' (t : ℝ)| :=
        hMinorLower
      _ = ‖Raw‖ *
            |K ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
              Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))| :=
        hExact.symm
      _ ≤ (1 + B) *
          |K ((f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
            Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))| :=
        mul_le_mul_of_nonneg_right hRawCap (abs_nonneg _)
      _ ≤ (1 + B) * ((‖K‖ + 1) * ‖f‖) :=
        mul_le_mul_of_nonneg_left hKBound (by linarith)
      _ = C * ‖f‖ := by dsimp [C]; ring
  constructor
  · change c * (t : ℝ) ≤ ‖f‖
    dsimp [c]
    calc
      (c₀ / C) * (t : ℝ) = (c₀ * (t : ℝ)) / C := by ring
      _ ≤ ‖f‖ := (div_le_iff₀ hC).2 (by nlinarith [hTotal])
  · exact p4Q2PZ37ZI_originalPhysicalCancellation_norm_le_linearFine H t

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZK_originalGITransverseCLM_constant_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZK_originalGITransverseCLM_cancellation_eq_rawMinor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZK_originalRawOperator_norm_le_one_add_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZK_originalPhysicalCancellation_twoSided_linearFine
