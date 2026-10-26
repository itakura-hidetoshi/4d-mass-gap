import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSixthObstructionCenterReductionV5_PZ37G
import Mathlib.Tactic

/-!
# PZ37H — original centre cuts separate any two distinct temporal trace links

A cut is the ORIGINAL set of spatial links with one fixed direction and
one fixed source coordinate in that direction. Multiplication by the true
SU(2) centre element -I on that cut preserves every full spatial plaquette
holonomy and the original product Haar. If two temporal links have the
same cut key, a centre gauge transformation at one source separates them.
This includes the minimal period: no non-wrapping assumption is used.

Consequently w(X)^i pairs to zero with a single temporal trace and with
any two DISTINCT temporal traces, for every natural i and finite H.
These are original-Haar identities, not posterior independence claims.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "z" => specialUnitaryTwoNegativeIdentity
local instance p4Q2PZ37H_cut_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37H_cut_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37H_cut_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37H_cut_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37H_cut_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37H_cut_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint
section OriginalCentreCut
variable (H : ℕ)
local notation "Vertex" => PeriodicHypercubicEvenSpatialSliceVertex H
local notation "Dir" => PeriodicHypercubicEvenSpatialDirection
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Hol" => periodicHypercubicEvenSpatialSlicePlaquetteHolonomy
local notation "shift" => periodicHypercubicEvenSpatialSliceShift H
local notation "e0" => p4Q2PU3_originalPlaquetteEdge0 H
local notation "e1" => p4Q2PU3_originalPlaquetteEdge1 H
local notation "e2" => p4Q2PU3_originalPlaquetteEdge2 H
local notation "e3" => p4Q2PU3_originalPlaquetteEdge3 H

/-- The true temporal normalized real trace, not a new Wilson observable. -/
noncomputable def p4Q2PZ37H_originalTemporalTrace
    (e : Link) (X B : Cfg) : ℝ :=
  1-E ((X e)⁻¹*B e)
local notation "τ" => p4Q2PZ37H_originalTemporalTrace H

/-- Two original links have the same direction and source coordinate in it. -/
def p4Q2PZ37H_originalOnCut (e f : Link) : Prop :=
  f.2 = e.2 ∧ f.1.1 e.2.1 = e.1.1 e.2.1
local notation "OnCut" => p4Q2PZ37H_originalOnCut H

/-- A genuine centre element on the selected original torus cut. -/
noncomputable def p4Q2PZ37H_originalCutSign (e f : Link) : G := by
  classical
  exact if OnCut e f then z else 1
local notation "sign" => p4Q2PZ37H_originalCutSign H

/-- Cut translation of the unchanged original configuration space. -/
noncomputable def p4Q2PZ37H_originalCutFlip (e : Link) (X : Cfg) : Cfg :=
  fun f => sign e f * X f
local notation "Flip" => p4Q2PZ37H_originalCutFlip H

/-- Parameter Haar change of variables, used below with explicit original symmetries. -/
theorem p4Q2PZ37H_originalHaar_change
    (T : Cfg → Cfg) (hT : MeasurePreserving T haar haar)
    (f : Cfg → ℝ) (hf : Continuous f) :
    (∫ X : Cfg, f X ∂haar) = (∫ X : Cfg, f (T X) ∂haar) := by
  have hmap : Measure.map T haar = haar := hT.map_eq
  have hfm : AEStronglyMeasurable f (Measure.map T haar) := by
    rw [hmap]
    exact hf.measurable.aestronglyMeasurable
  calc
    (∫ X : Cfg, f X ∂haar) = (∫ X : Cfg, f X ∂Measure.map T haar) := by
      rw [hmap]
    _ = (∫ X : Cfg, f (T X) ∂haar) :=
      MeasureTheory.integral_map hT.measurable.aemeasurable hfm

/-- Oddness is invoked only after proving the pointwise symmetry and true Haar preservation. -/
theorem p4Q2PZ37H_originalHaar_odd_zero
    (T : Cfg → Cfg) (hT : MeasurePreserving T haar haar)
    (f : Cfg → ℝ) (hf : Continuous f)
    (hOdd : ∀ X : Cfg, f (T X) = -f X) :
    (∫ X : Cfg, f X ∂haar) = 0 := by
  have h := p4Q2PZ37H_originalHaar_change H T hT f hf
  have hn : (∫ X : Cfg, f (T X) ∂haar) = -(∫ X : Cfg, f X ∂haar) := by
    calc
      (∫ X : Cfg, f (T X) ∂haar) = (∫ X : Cfg, -f X ∂haar) := by
        apply integral_congr_ae
        filter_upwards with X
        exact hOdd X
      _ = _ := integral_neg _
  linarith

/-- Original temporal trace continuity for compact-Haar integration. -/
theorem p4Q2PZ37H_originalTemporalTrace_continuous (e : Link) (B : Cfg) :
    Continuous (fun X : Cfg => τ e X B) :=
  continuous_const.sub ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
    ((continuous_apply e).inv.mul continuous_const))

private theorem p4Q2PZ37H_centerLeftTrace_odd (u b : G) :
    1-E ((z*u)⁻¹*b) = -(1-E (u⁻¹*b)) := by
  rw [mul_inv_rev, p4Q2PV_originalSU2Center_inverse,
    p4Q2PV_originalSU2Center_move_right,
    specialUnitaryWilsonPlaquetteEnergy_two_mul_negativeIdentity]
  ring

private theorem p4Q2PZ37H_cutSign_commutes (e f : Link) (u : G) :
    sign e f*u = u*sign e f := by
  classical
  unfold p4Q2PZ37H_originalCutSign
  split_ifs
  · exact p4Q2PV_originalSU2Center_commutes u
  · simp

private theorem p4Q2PZ37H_cutSign_shift_other
    (e : Link) (v : Vertex) (mu nu : Dir) (h : mu ≠ nu) :
    sign e (shift v nu,mu) = sign e (v,mu) := by
  classical
  by_cases hm : mu = e.2
  · subst mu
    have hv : e.2.1 ≠ nu.1 := by
      intro heq
      exact h (Subtype.ext heq)
    simp [p4Q2PZ37H_originalCutSign, p4Q2PZ37H_originalOnCut,
      periodicHypercubicEvenSpatialSliceShift, periodicHypercubicShift_apply, hv]
  · simp [p4Q2PZ37H_originalCutSign, p4Q2PZ37H_originalOnCut, hm]

private theorem p4Q2PZ37H_central_pair_word
    (a b u0 u1 u2 u3 : G)
    (ha : ∀ u : G, a*u = u*a) (hb : ∀ u : G, b*u = u*b) :
    (a*u0)*(b*u1)*(a*u2)⁻¹*(b*u3)⁻¹ = u0*u1*u2⁻¹*u3⁻¹ := by
  have hconj (u : G) : a*u*a⁻¹ = u := by rw [ha u]; group
  calc
    (a*u0)*(b*u1)*(a*u2)⁻¹*(b*u3)⁻¹ =
        (a*(u0*(b*u1)*u2⁻¹)*a⁻¹)*(b*u3)⁻¹ := by group
    _ = (u0*(b*u1)*u2⁻¹)*(b*u3)⁻¹ := by rw [hconj]
    _ = b*(u0*u1*u2⁻¹*u3⁻¹)*b⁻¹ := by
      rw [← mul_assoc u0 b u1, ← hb u0]
      group
    _ = u0*u1*u2⁻¹*u3⁻¹ := by rw [hb]; group

/-- Opposite true plaquette edges have equal cut signs, including periodic wraparound. -/
theorem p4Q2PZ37H_originalCutFlip_plaquetteHolonomy
    (e : Link) (p : Plaq) (X : Cfg) :
    Hol (Flip e X) p = Hol X p := by
  have hmu : p.2.1.1 ≠ p.2.1.2 := by
    intro heq
    exact (ne_of_lt p.2.2) (congrArg Subtype.val heq)
  have h20 : sign e (e2 p) = sign e (e0 p) :=
    p4Q2PZ37H_cutSign_shift_other H e p.1 p.2.1.1 p.2.1.2 hmu
  have h13 : sign e (e1 p) = sign e (e3 p) :=
    p4Q2PZ37H_cutSign_shift_other H e p.1 p.2.1.2 p.2.1.1 hmu.symm
  change (sign e (e0 p)*X (e0 p))*(sign e (e1 p)*X (e1 p))*
      (sign e (e2 p)*X (e2 p))⁻¹*(sign e (e3 p)*X (e3 p))⁻¹ =
      X (e0 p)*X (e1 p)*(X (e2 p))⁻¹*(X (e3 p))⁻¹
  rw [h20, h13]
  exact p4Q2PZ37H_central_pair_word _ _ _ _ _ _
    (p4Q2PZ37H_cutSign_commutes H e (e0 p))
    (p4Q2PZ37H_cutSign_commutes H e (e3 p))

/-- Every original spatial Wilson term, not only its Haar mean, is preserved. -/
theorem p4Q2PZ37H_originalCutFlip_halfAction (e : Link) (X : Cfg) :
    w (Flip e X) = w X := by
  unfold p4Q2PS_originalHalfSpatialAction
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction
  simp only [p4Q2PZ37H_originalCutFlip_plaquetteHolonomy]

/-- The cut transformation preserves the original normalized spatial product Haar. -/
theorem p4Q2PZ37H_originalCutFlip_Haar (e : Link) :
    MeasurePreserving (Flip e) haar haar :=
  p4Q2IX_actualSpatialHaar_leftTranslate_measurePreserving H (sign e)

/-- The selected original temporal trace changes sign. -/
theorem p4Q2PZ37H_originalCutFlip_trace_self (e : Link) (X B : Cfg) :
    τ e (Flip e X) B = -τ e X B := by
  have hs : sign e e = z := by
    simp [p4Q2PZ37H_originalCutSign, p4Q2PZ37H_originalOnCut]
  change 1-E ((sign e e*X e)⁻¹*B e) = -(1-E ((X e)⁻¹*B e))
  rw [hs]
  exact p4Q2PZ37H_centerLeftTrace_odd _ _

/-- Temporal traces outside the actual cut are unchanged. -/
theorem p4Q2PZ37H_originalCutFlip_trace_other
    (e f : Link) (h : ¬ OnCut e f) (X B : Cfg) :
    τ f (Flip e X) B = τ f X B := by
  have hs : sign e f = 1 := by simp [p4Q2PZ37H_originalCutSign, h]
  change 1-E ((sign e f*X f)⁻¹*B f) = 1-E ((X f)⁻¹*B f)
  rw [hs, one_mul]

/-- All original spatial Wilson powers have zero single-temporal-trace Haar pairing. -/
theorem p4Q2PZ37H_originalSpatialPower_oneTrace_zero
    (i : ℕ) (e : Link) (B : Cfg) :
    (∫ X : Cfg, (w X)^i*τ e X B ∂haar) = 0 := by
  apply p4Q2PZ37H_originalHaar_odd_zero H (Flip e)
    (p4Q2PZ37H_originalCutFlip_Haar H e)
    (fun X : Cfg => (w X)^i*τ e X B)
    (((p4Q2PZ36C_half_continuous H).pow i).mul
      (p4Q2PZ37H_originalTemporalTrace_continuous H e B))
  intro X
  rw [p4Q2PZ37H_originalCutFlip_halfAction H e X,
    p4Q2PZ37H_originalCutFlip_trace_self H e X B]
  ring

/-- The actual original Haar kills any two DISTINCT temporal traces weighted
by any power of the complete spatial action. Cut symmetry handles reciprocal
minimal-period links; the remaining equal-cut case uses a vertex gauge. -/
theorem p4Q2PZ37H_originalSpatialPower_twoDistinctTraces_zero
    (i : ℕ) (e f : Link) (hef : e ≠ f) (B : Cfg) :
    (∫ X : Cfg, (w X)^i*(τ e X B*τ f X B) ∂haar) = 0 := by
  classical
  have hc : Continuous (fun X : Cfg => (w X)^i*(τ e X B*τ f X B)) :=
    ((p4Q2PZ36C_half_continuous H).pow i).mul
      ((p4Q2PZ37H_originalTemporalTrace_continuous H e B).mul
        (p4Q2PZ37H_originalTemporalTrace_continuous H f B))
  by_cases hcut : OnCut e f
  · obtain ⟨hdir,hcoord⟩ := hcut
    have hsrc : f.1 ≠ e.1 := by
      intro hv
      exact hef (Prod.ext hv hdir).symm
    have htar : shift f.1 f.2 ≠ e.1 := by
      intro hv
      have hh := congrArg (fun v : Vertex => v.1 e.2.1) hv
      have hdirval := congrArg Subtype.val hdir
      have hstep : f.1.1 e.2.1+1 = e.1.1 e.2.1 := by
        simpa [periodicHypercubicEvenSpatialSliceShift,
          periodicHypercubicShift_apply, hdirval] using hh
      rw [hcoord] at hstep
      have hz : (1 : ZMod (PeriodicHypercubicEvenSideLength H)) = 0 := by
        apply add_left_cancel (a := e.1.1 e.2.1)
        simpa only [add_zero] using hstep
      apply p4Q2PL_originalSpatialLink_target_ne_source H f
      apply Subtype.ext
      funext j
      simp [periodicHypercubicEvenSpatialSliceShift,
        periodicHypercubicShift_apply, hz]
    let γ : Gauge := fun v => if v = e.1 then z else 1
    let T : Cfg → Cfg :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
    have hTe (X : Cfg) : T X e = z*X e := by
      change γ e.1*X e*(γ (shift e.1 e.2))⁻¹ = z*X e
      simp [γ, p4Q2PL_originalSpatialLink_target_ne_source H e]
    have hTf (X : Cfg) : T X f = X f := by
      change γ f.1*X f*(γ (shift f.1 f.2))⁻¹ = X f
      simp [γ, hsrc, htar]
    have hw (X : Cfg) : w (T X) = w X := by
      unfold p4Q2PS_originalHalfSpatialAction
      rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant]
    have hT : MeasurePreserving T haar haar :=
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H 2 γ
    apply p4Q2PZ37H_originalHaar_odd_zero H T hT
      (fun X : Cfg => (w X)^i*(τ e X B*τ f X B)) hc
    intro X
    rw [hw]
    unfold p4Q2PZ37H_originalTemporalTrace
    rw [hTe, hTf, p4Q2PZ37H_centerLeftTrace_odd]
    ring
  · apply p4Q2PZ37H_originalHaar_odd_zero H (Flip e)
      (p4Q2PZ37H_originalCutFlip_Haar H e)
      (fun X : Cfg => (w X)^i*(τ e X B*τ f X B)) hc
    intro X
    rw [p4Q2PZ37H_originalCutFlip_halfAction H e X,
      p4Q2PZ37H_originalCutFlip_trace_self H e X B,
      p4Q2PZ37H_originalCutFlip_trace_other H e f hcut X B]
    ring

end OriginalCentreCut
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalHaar_change
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalHaar_odd_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalTemporalTrace_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalCutFlip_plaquetteHolonomy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalCutFlip_halfAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalCutFlip_Haar
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalCutFlip_trace_self
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalCutFlip_trace_other
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalSpatialPower_oneTrace_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37H_originalSpatialPower_twoDistinctTraces_zero
