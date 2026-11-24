import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoOriginHaarLocalityV5_PZ37AOX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37APA — one-origin Haar resampling and original row second moment

The second AOX shift is fixed at identity. Thus only one actual native
spatial link changes and the original kernel has two-sided Harnack
comparison with exp(8 beta), not exp(16 beta). The AOX conditional Haar
holonomy law then gives the exact unweighted fiber moment 1/4.
Integrate both comparisons on the actual Haar product via Fubini.
No independence assumption about interacting plaquettes or new model.
The proposed conclusion is an original unnormalized row second-moment
error at most 3 beta times its actual row mass for 16 beta <= 1.
It is separate from the pending AOZ mixed kernel expansion.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "nu" => normalizedCompactHaar G
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "Mu" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
local notation "E" => p4Q2PZ37AMS_primarySpatialSliceEdge
local notation "R" => p4Q2PZ37AOX_twoOriginShift
local notation "Hol" => p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
local notation "Rep" => periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink

local instance p4Q2PZ37APA_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37APA_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37APA_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37APA_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37APA_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37APA_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37APA_haarProbability : IsProbabilityMeasure nu :=
  normalizedCompactHaar_isProbabilityMeasure G

private theorem p4Q2PZ37APA_replace_originalValue
    (H : ℕ) (B : Cfg H 2) (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Rep H 2 B target (B target) = B := by
  classical
  funext e
  by_cases he : e = target
  · subst e
    exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self
      H 2 B target (B target)
  · exact periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
      H 2 B target e (B target) he

/-- Fixing the second AOX shift at identity is exactly a single native
link replacement, not an approximation. -/
theorem p4Q2PZ37APA_oneOriginShift_eq_replace
    (H : ℕ) (B : Cfg H 2) (u : G) :
    R H B u 1 = Rep H 2 B (E H 0) (B (E H 0) * u) := by
  classical
  funext e
  by_cases he : e = E H 0
  · subst e
    rw [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_self]
    simp [p4Q2PZ37AOX_twoOriginShift]
  · rw [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
      H 2 B (E H 0) e (B (E H 0) * u) he]
    simp [p4Q2PZ37AOX_twoOriginShift, he]

/-- Two-sided original one-link kernel comparison, at every nonnegative beta. -/
theorem p4Q2PZ37APA_oneOriginShift_kernel_comparable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg H 2) (u : G) :
    K H 2 beta A (R H B u 1) ≤ Real.exp (8 * beta) * K H 2 beta A B ∧
    K H 2 beta A B ≤ Real.exp (8 * beta) * K H 2 beta A (R H B u 1) := by
  have hs := p4Q2PZ37APA_oneOriginShift_eq_replace H B u
  have hb := p4Q2PZ37APA_replace_originalValue H B (E H 0)
  have h0 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
      H 2 (by norm_num) beta hbeta A B (E H 0) (B (E H 0) * u) (B (E H 0))
  have h1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_reverse_le_exp_eight_mul
      H 2 (by norm_num) beta hbeta A B (E H 0) (B (E H 0) * u) (B (E H 0))
  rw [← hs, hb] at h0 h1
  exact ⟨h0, h1⟩

private theorem p4Q2PZ37APA_shift_continuous (H : ℕ) :
    Continuous (fun p : Cfg H 2 × G => R H p.1 p.2 1) := by
  classical
  apply continuous_pi
  intro e
  have hc : Continuous (fun p : Cfg H 2 × G => p.1 e) :=
    (continuous_apply e).comp continuous_fst
  by_cases he : e = E H 0
  · simpa [p4Q2PZ37AOX_twoOriginShift, he] using
      hc.mul (continuous_snd : Continuous (fun p : Cfg H 2 × G => p.2))
  · simpa [p4Q2PZ37AOX_twoOriginShift, he] using hc

private theorem p4Q2PZ37APA_character_continuous (H : ℕ) :
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

private theorem p4Q2PZ37APA_kernel_continuous
    (H : ℕ) (beta : ℝ) (A : Cfg H 2) :
    Continuous (fun B : Cfg H 2 => K H 2 beta A B) := by
  have hPair : Continuous (fun B : Cfg H 2 => (A, B)) :=
    (continuous_const : Continuous (fun _ : Cfg H 2 => A)).prodMk
      (continuous_id : Continuous (fun B : Cfg H 2 => B))
  change Continuous ((fun p : Cfg H 2 × Cfg H 2 => K H 2 beta p.1 p.2) ∘
    (fun B : Cfg H 2 => (A, B)))
  exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 beta).comp hPair

/-- Original primary Haar character squared has fiber mean 1/4 under
only one true origin link shift, for every fixed original configuration. -/
theorem p4Q2PZ37APA_oneOriginShift_characterSquare_haarMean
    (H : ℕ) (B : Cfg H 2) :
    (∫ u : G, (Chi (Hol H 2 (R H B u 1)))^2 ∂nu) = (1 / 4 : ℝ) := by
  let f : G → ℝ := fun g => (Chi g)^2
  let phi : G → G := fun u => Hol H 2 (R H B u 1)
  have hMP : MeasurePreserving phi nu nu :=
    p4Q2PZ37AOX_twoOriginShift_primaryHolonomy_haarMeasurePreserving H B 1
  have hf : AEStronglyMeasurable f nu :=
    (GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.pow 2).measurable.aestronglyMeasurable
  have hMap : AEStronglyMeasurable f (Measure.map phi nu) := by
    rw [hMP.map_eq]
    exact hf
  change (∫ u : G, f (phi u) ∂nu) = _
  calc
    _ = ∫ g : G, f g ∂Measure.map phi nu :=
      (integral_map hMP.measurable.aemeasurable hMap).symm
    _ = ∫ g : G, f g ∂nu := by rw [hMP.map_eq]
    _ = _ := GroundStatePosteriorJoint.p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment

/-- Original interacting row weighted second moment lies between the
two Harnack comparisons with its exact Haar value, without a global action
bound. Fubini here uses the genuine configuration Haar and auxiliary
single-link Haar; the weighted row itself is not asserted to be product. -/
theorem p4Q2PZ37APA_originalWeightedCharacterSquare_comparable
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (A : Cfg H 2) :
    (∫ B, K H 2 beta A B * (Chi (Hol H 2 B))^2 ∂(Mu H 2)) ≤
      Real.exp (8 * beta) * ((∫ B, K H 2 beta A B ∂(Mu H 2)) / 4) ∧
    (∫ B, K H 2 beta A B ∂(Mu H 2)) / 4 ≤
      Real.exp (8 * beta) * (∫ B, K H 2 beta A B * (Chi (Hol H 2 B))^2 ∂(Mu H 2)) := by
  let mu := Mu H 2
  let k : Cfg H 2 → ℝ := fun B => K H 2 beta A B
  let q : Cfg H 2 → ℝ := fun B => (Chi (Hol H 2 B))^2
  let rho : Cfg H 2 × G → Cfg H 2 := fun p => R H p.1 p.2 1
  let F : Cfg H 2 × G → ℝ := fun p => k (rho p) * q (rho p)
  let J : Cfg H 2 × G → ℝ := fun p => k p.1 * q (rho p)
  let c := Real.exp (8 * beta)
  have hk : Continuous k := p4Q2PZ37APA_kernel_continuous H beta A
  have hq : Continuous q := (p4Q2PZ37APA_character_continuous H).pow 2
  have hrho : Continuous rho := p4Q2PZ37APA_shift_continuous H
  have hF : Continuous F := (hk.comp hrho).mul (hq.comp hrho)
  have hJ : Continuous J := (hk.comp continuous_fst).mul (hq.comp hrho)
  have hFI : Integrable F (mu.prod nu) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJI : Integrable J (mu.prod nu) :=
    hJ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFixed (u : G) :
      (∫ B : Cfg H 2, F (B,u) ∂mu) = ∫ B : Cfg H 2, k B * q B ∂mu := by
    have hMP : MeasurePreserving (fun B : Cfg H 2 => R H B u 1) mu mu :=
      p4Q2PZ37AOX_twoOriginShift_haarMeasurePreserving H u 1
    have hMap :
        (∫ B : Cfg H 2, k B * q B ∂Measure.map (fun B => R H B u 1) mu) =
          ∫ B : Cfg H 2, F (B,u) ∂mu :=
      integral_map hMP.measurable.aemeasurable (hk.mul hq).measurable.aestronglyMeasurable
    rw [hMP.map_eq] at hMap
    exact hMap.symm
  have hFiber (B : Cfg H 2) :
      (∫ u : G, q (rho (B,u)) ∂nu) = (1 / 4 : ℝ) :=
    p4Q2PZ37APA_oneOriginShift_characterSquare_haarMean H B
  have hFIeq :
      (∫ p, F p ∂(mu.prod nu)) = ∫ B : Cfg H 2, k B * q B ∂mu := by
    calc
      _ = ∫ u : G, (∫ B : Cfg H 2, F (B,u) ∂mu) ∂nu :=
        MeasureTheory.integral_prod_symm F hFI
      _ = _ := by simp_rw [hFixed]; simp
  have hJIeq :
      (∫ p, J p ∂(mu.prod nu)) = (∫ B : Cfg H 2, k B ∂mu) / 4 := by
    calc
      _ = ∫ B : Cfg H 2, (∫ u : G, J (B,u) ∂nu) ∂mu :=
        MeasureTheory.integral_prod J hJI
      _ = ∫ B : Cfg H 2, k B * (1 / 4 : ℝ) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with B
        change (∫ u : G, k B * q (rho (B,u)) ∂nu) = _
        rw [integral_const_mul, hFiber]
      _ = _ := by rw [integral_mul_const]; ring
  have hUpper (p : Cfg H 2 × G) : F p ≤ c * J p := by
    have hp := (p4Q2PZ37APA_oneOriginShift_kernel_comparable H beta hbeta A p.1 p.2).1
    change k (rho p) ≤ c * k p.1 at hp
    have h := mul_le_mul_of_nonneg_right hp (sq_nonneg (Chi (Hol H 2 (rho p))))
    change k (rho p) * q (rho p) ≤ (c * k p.1) * q (rho p) at h
    change k (rho p) * q (rho p) ≤ c * (k p.1 * q (rho p))
    rw [← mul_assoc]
    exact h
  have hLower (p : Cfg H 2 × G) : J p ≤ c * F p := by
    have hp := (p4Q2PZ37APA_oneOriginShift_kernel_comparable H beta hbeta A p.1 p.2).2
    change k p.1 ≤ c * k (rho p) at hp
    have h := mul_le_mul_of_nonneg_right hp (sq_nonneg (Chi (Hol H 2 (rho p))))
    change k p.1 * q (rho p) ≤ (c * k (rho p)) * q (rho p) at h
    change k p.1 * q (rho p) ≤ c * (k (rho p) * q (rho p))
    rw [← mul_assoc]
    exact h
  have hUp := integral_mono_ae hFI (hJI.const_mul c) (Filter.Eventually.of_forall hUpper)
  have hLo := integral_mono_ae hJI (hFI.const_mul c) (Filter.Eventually.of_forall hLower)
  rw [integral_const_mul, hFIeq, hJIeq] at hUp
  rw [integral_const_mul, hFIeq, hJIeq] at hLo
  exact ⟨hUp, hLo⟩

/-- For 16 beta <= 1 the weighted second moment differs from one quarter
of the original row mass by at most 3 beta times that same row mass. -/
theorem p4Q2PZ37APA_originalWeightedCharacterSquare_error_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 16 * beta ≤ 1)
    (A : Cfg H 2) :
    |(∫ B, K H 2 beta A B * (Chi (Hol H 2 B))^2 ∂(Mu H 2)) -
        (∫ B, K H 2 beta A B ∂(Mu H 2)) / 4| ≤
      3 * beta * (∫ B, K H 2 beta A B ∂(Mu H 2)) := by
  let z : ℝ := ∫ B, K H 2 beta A B ∂(Mu H 2)
  let m : ℝ := ∫ B, K H 2 beta A B * (Chi (Hol H 2 B))^2 ∂(Mu H 2)
  let c := Real.exp (8 * beta)
  obtain ⟨hUp, hLo⟩ := p4Q2PZ37APA_originalWeightedCharacterSquare_comparable H beta hbeta A
  change m ≤ c * (z / 4) at hUp
  change z / 4 ≤ c * m at hLo
  have hz : 0 ≤ z := by
    apply integral_nonneg
    intro B
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    exact Real.exp_nonneg _
  have hc : 1 ≤ c := by
    dsimp [c]
    exact Real.one_le_exp_iff.mpr (by positivity)
  have hscalar := p4Q2PZ37AOH_real_exp_relativeLinearRemainder_abs_le
    beta (-8) hbeta (by linarith only [hbeta, hsmall]) (by norm_num)
  have heq : -beta * (-8 : ℝ) = 8 * beta := by ring
  have hlin : beta * (-8 : ℝ) = -(8 * beta) := by ring
  rw [heq, hlin, ← sub_eq_add_neg] at hscalar
  have hquad : 64 * beta^2 ≤ 4 * beta := by
    have hh := mul_nonneg hbeta (sub_nonneg.mpr hsmall)
    nlinarith only [hh]
  have hcBound : c - 1 ≤ 12 * beta := by
    dsimp [c]
    linarith only [(abs_le.mp hscalar).2, hquad]
  have hAbs : |m - z / 4| ≤ (c - 1) * (z / 4) := by
    rw [abs_le]
    constructor
    · by_cases hm : m ≤ z / 4
      · have h := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr hc)
        nlinarith only [hLo, h]
      · have h := mul_nonneg (sub_nonneg.mpr hc) (div_nonneg hz (by norm_num : (0 : ℝ) ≤ 4))
        linarith only [not_le.mp hm, h]
    · nlinarith only [hUp]
  change |m - z / 4| ≤ 3 * beta * z
  calc
    _ ≤ (c - 1) * (z / 4) := hAbs
    _ ≤ (12 * beta) * (z / 4) := mul_le_mul_of_nonneg_right hcBound (div_nonneg hz (by norm_num))
    _ = _ := by ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APA_oneOriginShift_eq_replace
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APA_oneOriginShift_kernel_comparable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APA_oneOriginShift_characterSquare_haarMean
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APA_originalWeightedCharacterSquare_comparable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37APA_originalWeightedCharacterSquare_error_le
