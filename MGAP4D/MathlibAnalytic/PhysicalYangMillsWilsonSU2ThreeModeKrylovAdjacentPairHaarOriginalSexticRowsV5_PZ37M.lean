import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEighthMinorEstimatesV5_PZ37M
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSeventhPhysicalCoefficientV5_PZ37B

/-!
# PZ37M — genuine sixth Taylor rows with seventh-order remainder

The literal one-slab kernel and the full two-slab product are integrated under
unchanged normalized SU(2) Haar. The sixth term has positive coefficient 1/720.
Q(Y,X,B)=S(Y,X)+S(X,B) retains the middle spatial action twice.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000
local notation "SU" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37M_topologicalGroup : IsTopologicalGroup SU := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37M_compactSpace : CompactSpace SU := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37M_secondCountable : SecondCountableTopology SU := specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37M_measurableSpace : MeasurableSpace SU := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37M_borelSpace : BorelSpace SU := specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
open PZ37MEstimates
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "M" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "T1" => p4Q2PZ2_originalOneSlabQuinticTaylor H
local notation "T2" => p4Q2PZ2_originalTwoSlabQuinticTaylor H
local notation "J1" => p4Q2PZ37B_originalOneSlabTaylor6 H
local notation "J2" => p4Q2PZ37B_originalTwoSlabTaylor6 H

private theorem action_cont (B : Cfg) : Continuous (fun X : Cfg => S X B) := by
  have hp : Continuous (fun X : Cfg => (X,B)) :=
    continuous_id.prodMk continuous_const
  have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hp
  simpa only [Function.comp_def] using h

private theorem double_action_cont (B : Cfg) :
    Continuous (fun p : Cfg × Cfg => Q p.1 p.2 B) := by
  have hs : Continuous (fun p : Cfg × Cfg => S p.1 p.2) :=
    p4Q2IW_originalWilsonOneSlabAction_continuous H
  have hr : Continuous (fun p : Cfg × Cfg => S p.2 B) :=
    (action_cont H B).comp continuous_snd
  change Continuous (fun p : Cfg × Cfg => S p.1 p.2 + S p.2 B)
  exact hs.add hr

private theorem quintic_cont {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (beta : ℝ) :
    Continuous (fun x => 1-beta*f x+(beta*f x)^2/2-(beta*f x)^3/6+
      (beta*f x)^4/24-(beta*f x)^5/120) := by
  fun_prop

/-- The genuine one-Haar sextic polynomial is exactly PZ37B's moment row. -/
theorem p4Q2PZ37M_originalOneSlab_integratedSextic_eq_jet (beta : ℝ) (B : Cfg) :
    (∫ X : Cfg, expTaylor6 (-(beta*S X B)) ∂haar) = J1 beta B := by
  have hS := action_cont H B
  have hT : Continuous (fun X : Cfg => T1 beta X B) := by
    exact quintic_cont _ hS beta
  have hP (X : Cfg) : expTaylor6 (-(beta*S X B)) =
      T1 beta X B + (beta^6/720)*(S X B)^6 := by
    unfold expTaylor6 p4Q2PZ2_originalOneSlabQuinticTaylor
      p4Q2PX2_originalOneSlabQuarticTaylor p4Q2PP_originalOneSlabCubicTaylor
    ring
  simp_rw [hP]
  have hi6 : Integrable (fun X : Cfg => (beta^6/720)*(S X B)^6) haar :=
    ((hS.pow 6).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  rw [integral_add
    (hT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    hi6, integral_const_mul,
    p4Q2PZ3_originalOneSlab_integratedQuintic_eq_jet H beta B]
  rfl

/-- The full interacting two-Haar sextic polynomial is exactly the moment row. -/
theorem p4Q2PZ37M_originalTwoSlab_integratedSextic_eq_jet (beta : ℝ) (B : Cfg) :
    (∫ X : Cfg, ∫ Y : Cfg, expTaylor6 (-(beta*Q Y X B)) ∂haar ∂haar) =
      J2 beta B := by
  have hQ := double_action_cont H B
  have hT : Continuous (fun p : Cfg × Cfg => T2 beta p.1 p.2 B) := by
    exact quintic_cont _ hQ beta
  have hP (Y X : Cfg) : expTaylor6 (-(beta*Q Y X B)) =
      T2 beta Y X B + (beta^6/720)*(Q Y X B)^6 := by
    unfold expTaylor6 p4Q2PZ2_originalTwoSlabQuinticTaylor
      p4Q2PX2_originalTwoSlabQuarticTaylor p4Q2PP_originalTwoSlabCubicTaylor
    ring
  simp_rw [hP]
  rw [double_integral_add haar (fun p : Cfg × Cfg => T2 beta p.1 p.2 B)
    (fun p : Cfg × Cfg => (beta^6/720)*(Q p.1 p.2 B)^6)
    hT (continuous_const.mul (hQ.pow 6))]
  simp_rw [integral_const_mul]
  rw [p4Q2PZ3_originalTwoSlab_integratedQuintic_eq_jet H beta B]
  rfl

private theorem scaled_remainder (beta s m : ℝ) (hs : 0 ≤ s) (hsm : s ≤ m)
    (hsmall : ‖beta*m‖ ≤ 1) :
    ‖Real.exp (-(beta*s)) - expTaylor6 (-(beta*s))‖ ≤ ‖beta*m‖^7 := by
  have hm : 0 ≤ m := hs.trans hsm
  have hn : ‖-(beta*s)‖ ≤ ‖beta*m‖ := by
    simp only [norm_neg, norm_mul, Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg hm]
    exact mul_le_mul_of_nonneg_left hsm (abs_nonneg _)
  exact (expTaylor6_remainder _ (hn.trans hsmall)).trans
    (pow_le_pow_left₀ (norm_nonneg _) hn 7)

/-- Actual one-slab Haar row, with a uniform-in-boundary seventh-order error. -/
theorem p4Q2PZ37M_originalOneSlabHaarRow_sexticJet_seventhRemainder_le
    (beta : ℝ) (hsmall : ‖beta*M‖ ≤ 1) (B : Cfg) :
    ‖p4Q2IV_originalWilsonUnitHaarKernelSection H beta B - J1 beta B‖ ≤
      ‖beta*M‖^7 := by
  have ht : Continuous (fun X : Cfg => -(beta*S X B)) :=
    (continuous_const.mul (action_cont H B)).neg
  have h := integral_error haar
    (fun X : Cfg => Real.exp (-(beta*S X B)))
    (fun X : Cfg => expTaylor6 (-(beta*S X B)))
    ht.rexp (expTaylor6_continuous.comp ht) (‖beta*M‖^7)
    (fun X => scaled_remainder beta (S X B) M
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
        H 2 (by decide) X B)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
        H 2 (by decide) X B) hsmall)
  rw [p4Q2PZ37M_originalOneSlab_integratedSextic_eq_jet H beta B] at h
  have hk : p4Q2IV_originalWilsonUnitHaarKernelSection H beta B =
      ∫ X : Cfg, Real.exp (-(beta*S X B)) ∂haar := by
    unfold p4Q2IV_originalWilsonUnitHaarKernelSection
    apply integral_congr_ae
    filter_upwards with X
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    congr 1
    ring
  rw [hk]
  exact h

/-- Actual two-slab Haar row with all middle-slice interactions retained. -/
theorem p4Q2PZ37M_originalTwoSlabHaarRow_sexticJet_seventhRemainder_le
    (beta : ℝ) (hsmall : ‖beta*(2*M)‖ ≤ 1) (B : Cfg) :
    ‖p4Q2PJ_originalWilsonLiteralTwoSlabKernel H beta B - J2 beta B‖ ≤
      ‖beta*(2*M)‖^7 := by
  have ht : Continuous (fun p : Cfg × Cfg => -(beta*Q p.1 p.2 B)) :=
    (continuous_const.mul (double_action_cont H B)).neg
  have h := double_integral_error haar
    (fun p : Cfg × Cfg => Real.exp (-(beta*Q p.1 p.2 B)))
    (fun p : Cfg × Cfg => expTaylor6 (-(beta*Q p.1 p.2 B)))
    ht.rexp (expTaylor6_continuous.comp ht) (‖beta*(2*M)‖^7)
    (fun Y X => scaled_remainder beta (Q Y X B) (2*M)
      (p4Q2PK_originalTwoSlabAction_nonneg H Y X B)
      (p4Q2PN_originalTwoSlabAction_le_twoBudget H Y X B) hsmall)
  rw [p4Q2PZ37M_originalTwoSlab_integratedSextic_eq_jet H beta B] at h
  have hk : p4Q2PJ_originalWilsonLiteralTwoSlabKernel H beta B =
      ∫ X : Cfg, ∫ Y : Cfg, Real.exp (-(beta*Q Y X B)) ∂haar ∂haar := by
    unfold p4Q2PJ_originalWilsonLiteralTwoSlabKernel
    simp_rw [p4Q2PK_originalTwoSlabKernel_product_eq_exp H beta]
  rw [hk]
  exact h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalOneSlab_integratedSextic_eq_jet
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalTwoSlab_integratedSextic_eq_jet
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalOneSlabHaarRow_sexticJet_seventhRemainder_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37M_originalTwoSlabHaarRow_sexticJet_seventhRemainder_le
