import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUniformNormalizedFirstRowSlopeV5_PZ37APC
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APH — signed double-center estimate on a wider original coupling interval

Candidate only. Use the exact AOY action mixed difference before taking
absolute values. Factor the mixed exponential into a product of single
differences and a signed character term. For 128 beta <= 1, the latter
retains at least (3/2) beta chi^2, while the former costs at most
(289/4) beta^2 |chi|. The inequality |chi| <= chi^2 + 1/4 and the actual
APA weighted second moment then yield I >= beta Z/128 uniformly in H.
This interval contains the original fixed coupling log(3/2)/64.
No change to the original model and no full-sector gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
local notation "T" => p4Q2PZ37ANV_singleLinkCenterTwist
local notation "E" => p4Q2PZ37AMS_primarySpatialSliceEdge
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "Hol" => p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy

local instance p4Q2PZ37APH_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APH_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APH_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APH_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APH_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APH_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37APH_singleExp
    (beta d : ℝ) (hb : 0 ≤ beta) (hs : 128 * beta ≤ 1) (hd : |d| ≤ 8) :
    |1 - Real.exp (-beta * d)| ≤ (17 / 2 : ℝ) * beta := by
  have h := p4Q2PZ37AOH_real_exp_relativeLinearRemainder_abs_le
    beta d hb (by linarith only [hs]) hd
  have hq : 64 * beta^2 ≤ beta / 2 := by
    have hh := mul_nonneg hb (sub_nonneg.mpr hs)
    nlinarith only [hh]
  have heq : 1 - Real.exp (-beta * d) =
      beta * d - (Real.exp (-beta * d) - 1 + beta * d) := by ring
  rw [heq]
  calc
    _ ≤ |beta * d| + |Real.exp (-beta * d) - 1 + beta * d| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (beta * d) (-(Real.exp (-beta * d) - 1 + beta * d)))
    _ ≤ beta * 8 + 64 * beta^2 := by
      rw [abs_mul, abs_of_nonneg hb]
      exact add_le_add (mul_le_mul_of_nonneg_left hd hb) h
    _ ≤ _ := by linarith only [hq]

private theorem p4Q2PZ37APH_signedExp
    (beta x : ℝ) (hb : 0 ≤ beta) (hs : 128 * beta ≤ 1) (hx : |x| ≤ 1) :
    (7 / 4 : ℝ) * beta * x^2 ≤ (Real.exp (2 * beta * x) - 1) * x := by
  let q := 2 * beta * x
  have hq : |q| ≤ 1 := by
    dsimp only [q]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * beta)]
    calc
      _ ≤ (2 * beta) * 1 := mul_le_mul_of_nonneg_left hx (by positivity)
      _ ≤ 1 := by linarith only [hs]
  have hnorm : ‖q‖ ≤ 1 := by simpa only [Real.norm_eq_abs] using hq
  have hr : |Real.exp q - 1 - q| ≤ q^2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Real.norm_exp_sub_one_sub_id_le hnorm)
  have hErr : |(Real.exp q - 1 - q) * x| ≤ 4 * beta^2 * x^2 := by
    rw [abs_mul]
    calc
      _ ≤ q^2 * |x| := mul_le_mul_of_nonneg_right hr (abs_nonneg _)
      _ ≤ q^2 * 1 := mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      _ = _ := by dsimp only [q]; ring
  have hRaw := (abs_le.mp hErr).1
  have hBase : (2 * beta - 4 * beta^2) * x^2 ≤
      (Real.exp q - 1) * x := by
    dsimp only [q] at hRaw ⊢
    nlinarith only [hRaw]
  have hCoef : (7 / 4 : ℝ) * beta ≤ 2 * beta - 4 * beta^2 := by
    have hh := mul_nonneg hb (sub_nonneg.mpr hs)
    nlinarith only [hh, hb]
  exact (mul_le_mul_of_nonneg_right hCoef (sq_nonneg x)).trans hBase

/-- Exact mixed exponential factorization keeps the sign information. -/
theorem p4Q2PZ37APH_signedMixedExp_lower
    (beta d0 d3 x : ℝ) (hb : 0 ≤ beta) (hs : 128 * beta ≤ 1)
    (h0 : |d0| ≤ 8) (h3 : |d3| ≤ 8) (hx : |x| ≤ 1) :
    (3 / 2 : ℝ) * beta * x^2 - (289 / 4 : ℝ) * beta^2 * (x^2 + 1/4) ≤
      (1 - Real.exp (-beta * d0) - Real.exp (-beta * d3) +
        Real.exp (-beta * (d0 + d3 - 2*x))) * x := by
  let a := 1 - Real.exp (-beta * d0)
  let b := 1 - Real.exp (-beta * d3)
  let e := Real.exp (-beta * (d0 + d3))
  let c := (Real.exp (2 * beta * x) - 1) * x
  have ha : |a| ≤ (17 / 2 : ℝ) * beta := p4Q2PZ37APH_singleExp beta d0 hb hs h0
  have hbb : |b| ≤ (17 / 2 : ℝ) * beta := p4Q2PZ37APH_singleExp beta d3 hb hs h3
  have hab : |a*b*x| ≤ (289 / 4 : ℝ) * beta^2 * |x| := by
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (((17 / 2 : ℝ) * beta) * ((17 / 2 : ℝ) * beta)) * |x| :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul ha hbb (abs_nonneg _) (by positivity)) (abs_nonneg _)
      _ = _ := by ring
  have hxq : |x| ≤ x^2 + 1/4 := by
    have hh := sq_nonneg (|x| - (1/2 : ℝ))
    have he := sq_abs x
    nlinarith only [hh, he]
  have hcost : |a*b*x| ≤ (289 / 4 : ℝ) * beta^2 * (x^2 + 1/4) :=
    hab.trans (mul_le_mul_of_nonneg_left hxq (by positivity))
  have he : (7/8 : ℝ) ≤ e := by
    have hd : d0 + d3 ≤ 16 := by linarith only [(abs_le.mp h0).2, (abs_le.mp h3).2]
    have hm := mul_le_mul_of_nonneg_left hd hb
    have he' := Real.add_one_le_exp (-beta * (d0 + d3))
    dsimp only [e]
    linarith only [hm, he', hs]
  have hc : (7/4 : ℝ) * beta * x^2 ≤ c :=
    p4Q2PZ37APH_signedExp beta x hb hs hx
  have hprod : (3/2 : ℝ) * beta * x^2 ≤ e*c := by
    calc
      _ ≤ (7/8 : ℝ) * ((7/4 : ℝ) * beta * x^2) := by
        nlinarith only [mul_nonneg hb (sq_nonneg x)]
      _ ≤ e * ((7/4 : ℝ) * beta * x^2) :=
        mul_le_mul_of_nonneg_right he (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (by dsimp only [e]; positivity)
  have heq1 : Real.exp (-beta * (d0+d3)) =
      Real.exp (-beta*d0) * Real.exp (-beta*d3) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq2 : Real.exp (-beta*(d0+d3-2*x)) =
      Real.exp (-beta*(d0+d3)) * Real.exp (2*beta*x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsplit :
      (1 - Real.exp (-beta * d0) - Real.exp (-beta * d3) +
        Real.exp (-beta * (d0+d3-2*x))) * x = a*b*x + e*c := by
    dsimp only [a,b,e,c]
    rw [heq2, heq1]
    ring
  rw [hsplit]
  linarith only [(abs_le.mp hcost).1, hprod]

private theorem p4Q2PZ37APH_kernelFactor
    (H : ℕ) (beta : ℝ) (A B D : Cfg H 2) :
    K H 2 beta A D = K H 2 beta A B *
      Real.exp (-beta * (S H 2 A D - S H 2 A B)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    ← Real.exp_add]
  congr 1
  ring

private theorem p4Q2PZ37APH_chi_abs (H : ℕ) (B : Cfg H 2) :
    |Chi (Hol H 2 B)| ≤ 1 := by
  rw [p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter]
  unfold GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter
  have hlow := specialUnitaryWilsonPlaquetteEnergy_nonneg
    (by norm_num : 0 < (2 : ℕ))
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
      (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
  have hup := specialUnitaryWilsonPlaquetteEnergy_le_two
    (by norm_num : 0 < (2 : ℕ))
    (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy B
      (p4Q2PZ37AMS_primarySpatialSlicePlaquette H))
  rw [abs_le]
  constructor <;> linarith only [hlow, hup]

/-- A one-sided local estimate on the literal original Wilson kernel. -/
theorem p4Q2PZ37APH_originalMixedKernel_signedLower
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (hs : 128 * beta ≤ 1)
    (A B : Cfg H 2) :
    K H 2 beta A B * ((3/2 : ℝ) * beta * (Chi (Hol H 2 B))^2 -
        (289/4 : ℝ) * beta^2 * ((Chi (Hol H 2 B))^2 + 1/4)) ≤
      (K H 2 beta A B - K H 2 beta A (T H (E H 0) B) -
        K H 2 beta A (T H (E H 3) B) +
        K H 2 beta A (T H (E H 3) (T H (E H 0) B))) * Chi (Hol H 2 B) := by
  let B0 := T H (E H 0) B
  let B3 := T H (E H 3) B
  let B03 := T H (E H 3) B0
  let k := K H 2 beta A B
  let x := Chi (Hol H 2 B)
  let d0 := S H 2 A B0 - S H 2 A B
  let d3 := S H 2 A B3 - S H 2 A B
  let d03 := S H 2 A B03 - S H 2 A B
  have h0 : |d0| ≤ 8 :=
    p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight H (E H 0) A B
  have h3 : |d3| ≤ 8 :=
    p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight H (E H 3) A B
  have hx : |x| ≤ 1 := p4Q2PZ37APH_chi_abs H B
  have hGap : d03 = d0+d3-2*x := by
    have h := p4Q2PZ37AOY_originalOneSlabAction_twoOriginMixedDifference H A B
    change S H 2 A B - S H 2 A B0 - S H 2 A B3 + S H 2 A B03 = -2*x at h
    dsimp only [d0,d3,d03]
    linarith only [h]
  have hk : 0 ≤ k := by
    dsimp only [k]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    exact Real.exp_nonneg _
  have hf0 : K H 2 beta A B0 = k * Real.exp (-beta*d0) :=
    p4Q2PZ37APH_kernelFactor H beta A B B0
  have hf3 : K H 2 beta A B3 = k * Real.exp (-beta*d3) :=
    p4Q2PZ37APH_kernelFactor H beta A B B3
  have hf03 : K H 2 beta A B03 = k * Real.exp (-beta*d03) :=
    p4Q2PZ37APH_kernelFactor H beta A B B03
  change k * ((3/2 : ℝ)*beta*x^2 - (289/4 : ℝ)*beta^2*(x^2+1/4)) ≤
    (k-K H 2 beta A B0-K H 2 beta A B3+K H 2 beta A B03)*x
  rw [hf0, hf3, hf03, hGap]
  calc
    _ ≤ k * ((1 - Real.exp (-beta*d0) - Real.exp (-beta*d3) +
        Real.exp (-beta*(d0+d3-2*x)))*x) :=
      mul_le_mul_of_nonneg_left (p4Q2PZ37APH_signedMixedExp_lower beta d0 d3 x hb hs h0 h3 hx) hk
    _ = _ := by ring

private theorem p4Q2PZ37APH_twist_continuous
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Continuous (T H e) := by
  classical
  unfold p4Q2PZ37ANV_singleLinkCenterTwist
  apply continuous_pi
  intro i
  exact (continuous_apply i).mul continuous_const

private theorem p4Q2PZ37APH_character_continuous (H : ℕ) :
    Continuous (fun B : Cfg H 2 => Chi (Hol H 2 B)) := by
  have heq :
      (fun B : Cfg H 2 => Chi (Hol H 2 B)) =
      (fun B => GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter H
        (p4Q2PZ37AMS_primarySpatialSlicePlaquette H) B) := by
    funext B
    exact p4Q2PZ37ANV_cyclicCharacter_eq_nativeCharacter H B
  rw [heq]
  exact GroundStatePosteriorJoint.p4Q2PV_originalPlaquetteRealCharacter_continuous
    H (p4Q2PZ37AMS_primarySpatialSlicePlaquette H)

/-- The signed original row moment has a positive uniform lower coefficient
on a wider interval, with the genuine row mass retained. -/
theorem p4Q2PZ37APH_originalFirstRow_ge_beta_rowMass_div128
    (H : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (hs : 128 * beta ≤ 1)
    (A : Cfg H 2) :
    beta * (∫ B, K H 2 beta A B ∂(Mu H 2)) / 128 ≤
      ∫ B, K H 2 beta A B * Chi (Hol H 2 B) ∂(Mu H 2) := by
  let mu := Mu H 2
  let k : Cfg H 2 → ℝ := fun B => K H 2 beta A B
  let x : Cfg H 2 → ℝ := fun B => Chi (Hol H 2 B)
  let t0 := T H (E H 0)
  let t3 := T H (E H 3)
  let mixed : Cfg H 2 → ℝ := fun B => k B - k (t0 B) - k (t3 B) + k (t3 (t0 B))
  let q : Cfg H 2 → ℝ := fun B => k B * (x B)^2
  let z : ℝ := ∫ B, k B ∂mu
  let m : ℝ := ∫ B, q B ∂mu
  let i : ℝ := ∫ B, k B * x B ∂mu
  have hk : Continuous k := by
    have hp : Continuous (fun B : Cfg H 2 => (A,B)) :=
      (continuous_const : Continuous (fun _ : Cfg H 2 => A)).prodMk continuous_id
    change Continuous ((fun p : Cfg H 2 × Cfg H 2 => K H 2 beta p.1 p.2) ∘
      (fun B : Cfg H 2 => (A,B)))
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 beta).comp hp
  have hx : Continuous x := p4Q2PZ37APH_character_continuous H
  have ht0 : Continuous t0 := p4Q2PZ37APH_twist_continuous H _
  have ht3 : Continuous t3 := p4Q2PZ37APH_twist_continuous H _
  have hmixed : Continuous mixed :=
    ((hk.sub (hk.comp ht0)).sub (hk.comp ht3)).add ((hk.comp ht3).comp ht0)
  have hq : Continuous q := hk.mul (hx.pow 2)
  have hkI : Integrable k mu := hk.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hqI : Integrable q mu := hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmI : Integrable (fun B => mixed B*x B) mu :=
    (hmixed.mul hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let a : ℝ := (3/2 : ℝ)*beta
  let b : ℝ := (289/4 : ℝ)*beta^2
  have hAux : Integrable (fun B => q B + (1/4 : ℝ)*k B) mu :=
    hqI.add (hkI.const_mul (1/4 : ℝ))
  have hL : Integrable (fun B => a*q B - b*(q B+(1/4 : ℝ)*k B)) mu :=
    (hqI.const_mul a).sub (hAux.const_mul b)
  have hPoint (B : Cfg H 2) :
      a*q B - b*(q B+(1/4 : ℝ)*k B) ≤ mixed B*x B := by
    have h := p4Q2PZ37APH_originalMixedKernel_signedLower H beta hb hs A B
    change k B * (a*(x B)^2-b*((x B)^2+1/4)) ≤ mixed B*x B at h
    have heq : a*q B - b*(q B+(1/4 : ℝ)*k B) =
        k B * (a*(x B)^2-b*((x B)^2+1/4)) := by dsimp only [q]; ring
    rw [heq]
    exact h
  have hInt : (∫ B, a*q B-b*(q B+(1/4 : ℝ)*k B) ∂mu) ≤
      ∫ B, mixed B*x B ∂mu :=
    integral_mono_ae hL hmI (Filter.Eventually.of_forall hPoint)
  have hSum : (∫ B, q B+(1/4 : ℝ)*k B ∂mu) = m+z/4 := by
    calc
      _ = (∫ B, q B ∂mu) + (∫ B, (1/4 : ℝ)*k B ∂mu) :=
        integral_add hqI (hkI.const_mul (1/4 : ℝ))
      _ = _ := by rw [integral_const_mul]; dsimp only [m,z]; ring
  have hLeft : (∫ B, a*q B-b*(q B+(1/4 : ℝ)*k B) ∂mu) =
      a*m-b*(m+z/4) := by
    calc
      _ = (∫ B, a*q B ∂mu) - (∫ B, b*(q B+(1/4 : ℝ)*k B) ∂mu) :=
        integral_sub (hqI.const_mul a) (hAux.const_mul b)
      _ = a*m-b*(m+z/4) := by
        rw [integral_const_mul, integral_const_mul, hSum]
  have hAnti : (∫ B, mixed B*x B ∂mu) = 4*i :=
    p4Q2PZ37APB_originalHaarPrimaryCharacter_doubleAntisymmetrization H k hk
  rw [hLeft, hAnti] at hInt
  have hz : 0 ≤ z := by
    dsimp only [z,k]
    apply integral_nonneg
    intro B
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    exact Real.exp_nonneg _
  have hMoment : |m-z/4| ≤ 3*beta*z :=
    p4Q2PZ37APA_originalWeightedCharacterSquare_error_le H beta hb
      (by linarith only [hs]) A
  have hErr : 3*beta*z ≤ (3/128 : ℝ)*z :=
    mul_le_mul_of_nonneg_right (by linarith only [hs]) hz
  have hmLo : (29/128 : ℝ)*z ≤ m := by
    linarith only [(abs_le.mp hMoment).1,hErr]
  have hmUp : m ≤ (35/128 : ℝ)*z := by
    linarith only [(abs_le.mp hMoment).2,hErr]
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hbb : 0 ≤ b := by dsimp only [b]; positivity
  have hPosPart := mul_le_mul_of_nonneg_left hmLo ha
  have hNegPart := mul_le_mul_of_nonneg_left
    (add_le_add hmUp (le_refl (z/4))) hbb
  have hBZ : beta^2*z ≤ (1/128 : ℝ)*(beta*z) := by
    have hh := mul_le_mul_of_nonneg_right
      (by linarith only [hs] : beta ≤ (1/128 : ℝ)) (mul_nonneg hb hz)
    nlinarith only [hh]
  change beta*z/128 ≤ i
  dsimp only [a,b] at hInt hPosPart hNegPart
  nlinarith only [hInt,hPosPart,hNegPart,hBZ,mul_nonneg hb hz]

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APH_signedMixedExp_lower
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APH_originalMixedKernel_signedLower
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APH_originalFirstRow_ge_beta_rowMass_div128
