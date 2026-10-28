import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllVolumeFineRayleighErrorGateV5_PZ37ZZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAA — genuine Wilson physical tangent explicit volume-dependent rate

No longer merely pointwise convergence. ZQ's true raw Wilson physical
Taylor remainder, ZV2's true top-normalization slope estimate and
ZT's true error quotient yield an explicit O_H(t) convergence rate
of the ORIGINAL norm-normalized physical cancellation F_t/t to the
ORIGINAL centered Wilson Gauss-law tangent V_H.

For actual one-slab Wilson action budget B_H and d_H =
<raw physical derivative,U>, k_H = original scalar crossing derivative,
W_H = original spatial Wilson physical source, set
 A_H = 2 B_H |d_H + k_H| + B_H ||W_H|| + 20 B_H².
On B_H t <= 1/4 and t>0, the exact original physical tangent satisfies
 ||F_t/t - V_H|| <= A_H t.
This follows from proven raw Wilson operator continuity, without
assuming uniform B_H, V_H norm or an all-volume common fine interval.

In particular the ZZZ actual represented-source displacement obeys
the same bound. No unproved all-H uniform coercivity is asserted.
No replacement posterior, physical source, axiom, sorry/admit/
native_decide, endpoint E/F, H1-H4 or continuum mass-gap theorem.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A purely Hilbert-module scalar decomposition of the true
normalized tangent; keeps the scalar and transverse errors separate. -/
theorem p4Q2PZ37AAA_normedTangent_scalarError_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U W e : E) (hU : ‖U‖ = 1)
    (s q d k B t : ℝ) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (hS : |s - 1| ≤ 2 * B * t)
    (hS2 : |s| ≤ 2)
    (hQ : |q-d| ≤ 9 * B^2 * t)
    (hE : ‖e‖ ≤ B^2 * t) :
    ‖((s * (q+k)) • U + (s/2) • W - s • e) -
       ((d+k) • U + (1/2 : ℝ) • W)‖ ≤
      (2 * B * |d+k| + B * ‖W‖ + 20 * B^2) * t := by
  have hIdentity :
      s * (q+k) - (d+k) = (s-1) * (d+k) + s * (q-d) := by ring
  have hScalar :
      |s * (q+k)-(d+k)| ≤ |s-1| * |d+k| + |s| * |q-d| := by
    rw [hIdentity]
    calc
      |(s-1)*(d+k) + s*(q-d)| ≤
          |(s-1)*(d+k)| + |s*(q-d)| := abs_add_le _ _
      _ = |s-1| * |d+k| + |s| * |q-d| := by rw [abs_mul, abs_mul]
  have hExpand :
      ((s*(q+k)) • U + (s/2) • W - s • e) -
        ((d+k) • U + (1/2 : ℝ) • W) =
      (s*(q+k)-(d+k)) • U + ((s-1)/2) • W - s • e := by
    module
  have hVector :
      ‖((s*(q+k)) • U + (s/2) • W - s • e) -
        ((d+k) • U + (1/2 : ℝ) • W)‖ ≤
      |s*(q+k)-(d+k)| + (|s-1|/2)*‖W‖ + |s|*‖e‖ := by
    rw [hExpand]
    calc
      ‖(s*(q+k)-(d+k)) • U + ((s-1)/2) • W - s • e‖ ≤
          ‖(s*(q+k)-(d+k)) • U + ((s-1)/2) • W‖ + ‖s • e‖ :=
        norm_sub_le _ _
      _ ≤ (‖(s*(q+k)-(d+k)) • U‖ +
          ‖((s-1)/2) • W‖) + ‖s • e‖ :=
        add_le_add_right (norm_add_le _ _) _
      _ = |s*(q+k)-(d+k)| + (|s-1|/2)*‖W‖ + |s|*‖e‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_div,
          abs_of_pos (show (0 : ℝ) < 2 by norm_num), hU]
        ring
  have hA :
      |s-1| * |d+k| ≤ (2*B*t)*|d+k| :=
    mul_le_mul_of_nonneg_right hS (abs_nonneg _)
  have hQBound :
      |s| * |q-d| ≤ 2 * (9*B^2*t) :=
    mul_le_mul hS2 hQ (abs_nonneg _) (by positivity)
  have hWBound :
      (|s-1|/2)*‖W‖ ≤ ((2*B*t)/2)*‖W‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg W)
    exact div_le_div_of_nonneg_right hS (by norm_num)
  have hEBound :
      |s|*‖e‖ ≤ 2 * (B^2*t) :=
    mul_le_mul hS2 hE (norm_nonneg e) (by norm_num)
  calc
    ‖((s*(q+k)) • U + (s/2) • W - s • e) -
       ((d+k) • U + (1/2 : ℝ) • W)‖ ≤
      |s*(q+k)-(d+k)| + (|s-1|/2)*‖W‖ + |s|*‖e‖ := hVector
    _ ≤ (2*B*t)*|d+k| + 2*(9*B^2*t) +
        ((2*B*t)/2)*‖W‖ + 2*(B^2*t) := by
      linarith only [hScalar, hA, hQBound, hWBound, hEBound]
    _ = (2*B*|d+k| + B*‖W‖ + 20*B^2)*t := by ring

local instance p4Q2PZ37AAA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAA_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The true Wilson inverse top normalization is explicitly bounded
by 2, with a genuine action-budget Lipschitz estimate at fine zero.
The top norm is NEVER formally differentiated. -/
theorem p4Q2PZ37AAA_originalInverseNorm_actionBudget_bounds
    (H : ℕ) (t : Set.Ici (0 : ℝ))
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (t : ℝ) ≤ (1/4 : ℝ)) :
    0 < p4Q2PZ37ZS_originalRawInverseNorm H t ∧
    p4Q2PZ37ZS_originalRawInverseNorm H t ≤ 2 ∧
    |p4Q2PZ37ZS_originalRawInverseNorm H t - 1| ≤
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (t : ℝ) := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let R : Phys →L[ℝ] Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let R0 : Phys →L[ℝ] Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have ht : 0 ≤ (t : ℝ) := t.property
  have hR0 : ‖R0‖ = 1 := by
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm
      H 2 specialUnitaryTwoWilsonRankPositive
  have hDist : ‖R-R0‖ ≤ B*(t : ℝ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  have hGap : |‖R‖-1| ≤ B*(t : ℝ) := by
    have hh := abs_norm_sub_norm_le R R0
    rw [hR0] at hh
    exact hh.trans hDist
  have hLower : (1/2 : ℝ) ≤ ‖R‖ := by
    have hh := (abs_le.mp hGap).1
    linarith
  have hRPos : 0 < ‖R‖ :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) hLower
  have hsPos : 0 < ‖R‖⁻¹ := inv_pos.mpr hRPos
  have hsUpper : ‖R‖⁻¹ ≤ 2 := by
    have hh : 1/‖R‖ ≤ 1/(1/2 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hLower
    norm_num at hh ⊢
    exact hh
  have hsDiff : |‖R‖⁻¹ - 1| ≤ 2*B*(t : ℝ) := by
    have hIdentity : ‖R‖⁻¹ - 1 = (1-‖R‖)/‖R‖ := by
      field_simp [ne_of_gt hRPos]
    rw [hIdentity, abs_div, abs_of_pos hRPos, abs_sub_comm]
    calc
      |‖R‖ - 1| / ‖R‖ ≤ (B*(t : ℝ))/‖R‖ :=
        div_le_div_of_nonneg_right hGap hRPos.le
      _ = (B*(t : ℝ))*‖R‖⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (B*(t : ℝ))*2 :=
        mul_le_mul_of_nonneg_left hsUpper (mul_nonneg hB ht)
      _ = 2*B*(t : ℝ) := by ring
  exact ⟨hsPos, hsUpper, hsDiff⟩

/-- True volume-dependent coefficient using the exact original
one-slab action budget, physical Wilson source and vacuum derivative.
No artificial constant or independently imposed estimate. -/
noncomputable def p4Q2PZ37AAA_originalPhysicalTangentRateBudget
    (H : ℕ) : ℝ :=
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let d := inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H) U
  let k := p4Q2JE_originalWilsonHaarZeroDerivativeConstant H
  2*B*|d+k| + B*‖W‖ + 20*B^2

/-- For the ACTUAL original Wilson normalized physical transfer,
the physical source F_t/t converges with a proved explicit O_H(t)
budget. It is not an all-volume or all-scale uniform rate. -/
theorem p4Q2PZ37AAA_originalPhysicalTangent_error_le_linear
    (H : ℕ) (t : Set.Ici (0 : ℝ)) (ht : 0 < (t : ℝ))
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (t : ℝ) ≤ (1/4 : ℝ)) :
    ‖p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H t -
      p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖ ≤
      p4Q2PZ37AAA_originalPhysicalTangentRateBudget H * (t : ℝ) := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let k : ℝ := p4Q2JE_originalWilsonHaarZeroDerivativeConstant H
  let d : ℝ := inner ℝ (p4Q2PZ37ZQ_originalPhysicalRawDerivative H) U
  let s : ℝ := p4Q2PZ37ZS_originalRawInverseNorm H t
  let q : ℝ := p4Q2PZ37ZV2_originalRawNormSlopeExtension H t
  let e : Phys := p4Q2PZ37ZT_originalPhysicalErrorDivFine H t
  have hU : ‖U‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  obtain ⟨hsPos,hsUpper,hsDiff⟩ :=
    p4Q2PZ37AAA_originalInverseNorm_actionBudget_bounds H t hsmall
  have hS2 : |s| ≤ 2 := by
    rw [abs_of_pos hsPos]
    exact hsUpper
  have hQ :
      |q-d| ≤ 9*B^2*(t : ℝ) :=
    p4Q2PZ37ZV2_originalRawNormSlopeExtension_linearError H t hsmall
  have hSmallOne : ‖(t : ℝ)*B‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.le hB)]
    nlinarith [hsmall]
  have hE : ‖e‖ ≤ B^2*(t : ℝ) := by
    calc
      ‖e‖ ≤ (t : ℝ)*B^2 :=
        p4Q2PZ37ZT_originalPhysicalErrorDivFine_norm_le_linear H t ht hSmallOne
      _ = B^2*(t : ℝ) := by ring
  have hd :
      d+k = -(1/2 : ℝ)*inner ℝ W U := by
    have hh := p4Q2PZ37ZV_originalPhysicalRawDerivative_vacuum_coeff H
    change d = -(1/2 : ℝ)*inner ℝ W U-k at hh
    linarith
  have hX :
      p4Q2PZ37ZV2_originalFullPhysicalTangentExtension H t =
        (s*(q+k)) • U + (s/2) • W - s • e := by
    change (s*(q+k)) • U + ((s/2) • W - s • e) =
      (s*(q+k)) • U + (s/2) • W - s • e
    abel
  have hV :
      p4Q2PZ37ZW_originalCenteredPhysicalDirection H =
        (d+k) • U + (1/2 : ℝ) • W := by
    change (1/2 : ℝ) • (W - (inner ℝ W U) • U) =
      (d+k) • U + (1/2 : ℝ) • W
    rw [hd]
    module
  have hPointwise :=
    p4Q2PZ37AAA_normedTangent_scalarError_le
      U W e hU s q d k B (t : ℝ) hB ht.le hsDiff hS2 hQ hE
  rw [hX,hV]
  exact hPointwise

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AAA_normedTangent_scalarError_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAA_originalInverseNorm_actionBudget_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAA_originalPhysicalTangent_error_le_linear
