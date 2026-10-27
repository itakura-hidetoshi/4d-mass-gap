import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIActivePlaquetteDensityV5_MB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLSharpPhysicalD3MassV5_PZ37Y
import Mathlib.Tactic

/-!
# P4-Q2-PZ37Z — original Wilson GI U0 candidate and absolute spatial activity

The fully original SU(2) Wilson interacting-posterior, transfer-compensated
local spatial GI minors are d(H,b,e,e',z,z',p). Their authentic finite
square energy is Q = sum_p d_p^2 over original plaquettes, N_H the actual
plaquette count. MA proves the UNIFORM-IN-H one-plaquette upper bound
d_p^2 <= M_b = (4 E_b^2)^2 for fixed positive frozen coupling b.

MB established a finite-H active response with MOVING threshold Q/(2N_H).
PZ37Z first fixes an ABSOLUTE positive threshold independent of H.
It proves, with no unproved volume-uniform premise:

  ε <= Q/N_H  =>
    (ε/(2M_b)) <= #{p : d_p^2 >= ε/2}/N_H

and, in the reverse direction,

  ρ <= #{p : d_p^2 >= τ}/N_H =>
    τρ <= Q/N_H, for τ >= 0.

Hence the CONTEXT-SELECTABLE normalized GI U0 criterion
  exists ε>0, forall H, exists ORIGINAL e,e',z,z' with Q/N_H >= ε
is equivalent to the existence of fixed τ,ρ>0 such that at every H
some ORIGINAL contexts have a fraction >=ρ of genuine plaquettes with
d_p^2>=τ. Witness contexts are explicitly quantified after H;
no claim of a fixed cross-volume boundary configuration is made.

This is a criterion, NOT a proof that those genuinely uniform contexts
exist. PZ37Y's separate three-Krylov GL Gram certificate does not
automatically imply this genuinely different local GI condition.
No surrogate Wilson detectors, changed posterior, new axioms or
continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37Z_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37Z_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37Z_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37Z_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37Z_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

private abbrev p4Q2PZ37Z_Cfg (H : ℕ) :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
private abbrev p4Q2PZ37Z_Link (H : ℕ) :=
  PeriodicHypercubicEvenSpatialSliceLink H

section FixedVolume
variable (H : ℕ) (b : ℝ) (hb : 0 ≤ b)

local notation "Cfg" => p4Q2PZ37Z_Cfg H
local notation "Link" => p4Q2PZ37Z_Link H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "N" => (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)
local notation "E" => p4Q2LW_originalHarnackContrastScale b
local notation "d" => p4Q2LW_originalCompensatedLocalGIMinor H b hb
local notation "Q" => p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb
local notation "M" => (4 * E ^ 2) ^ 2

/-- Original SU(2) spatial plaquettes with an ABSOLUTE genuine GI
squared-response threshold, unlike MB's moving half-energy threshold. -/
noncomputable def p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes
    (τ : ℝ) (e e' : Link) (z z' : Cfg × Cfg) : Finset Plaq :=
  Finset.univ.filter (fun p => τ ≤ (d e e' z z' p) ^ 2)

/-- Quantitative NECESSARY fixed-threshold spatial delocalization.
An original normalized GI energy density >= ε forces a positive
density of true GI plaquettes above the same absolute ε/2 at every H.
The amplitude M_b is MA's H-independent actual Wilson ceiling. -/
theorem p4Q2PZ37Z_originalGI_energyFloor_implies_absoluteActive_density
    (hpos : 0 < b) (hN : 0 < N) (ε : ℝ)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hEnergy : ε ≤ Q e e' z z' / N) :
    ε / (2 * M) ≤
      ((p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes
        H b hb (ε / 2) e e' z z').card : ℝ) / N := by
  classical
  have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hpos
  have hM : 0 < M := by
    dsimp only
    positivity
  have hDen : 0 < 2 * M := mul_pos (by norm_num) hM
  have hThreshold : ε / 2 ≤ Q e e' z z' / (2 * N) := by
    calc
      ε / 2 ≤ (Q e e' z z' / N) / 2 :=
        (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr hEnergy
      _ = Q e e' z z' / (2 * N) := by
        field_simp [ne_of_gt hN]
        ring
  have hSubset :
      p4Q2MB_originalActiveGISpatialPlaquettes H b hb e e' z z' ⊆
        p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes
          H b hb (ε / 2) e e' z z' := by
    intro p hp
    have hOld : Q e e' z z' / (2 * N) ≤ (d e e' z z' p) ^ 2 := by
      exact (Finset.mem_filter.mp hp).2
    change p ∈ (Finset.univ : Finset Plaq).filter
      (fun q => ε / 2 ≤ (d e e' z z' q) ^ 2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, le_trans hThreshold hOld⟩
  have hCard :
      ((p4Q2MB_originalActiveGISpatialPlaquettes H b hb e e' z z').card : ℝ) ≤
      ((p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes
        H b hb (ε / 2) e e' z z').card : ℝ) :=
    by exact_mod_cast Finset.card_le_card hSubset
  have hCardDiv := (div_le_div_iff_of_pos_right hN).mpr hCard
  have hMB :=
    p4Q2MB_originalActiveGI_density_ge_energy_fraction
      H b hb hpos hN e e' z z'
  calc
    ε / (2 * M) ≤ (Q e e' z z' / N) / (2 * M) :=
      (div_le_div_iff_of_pos_right hDen).mpr hEnergy
    _ ≤ ((p4Q2MB_originalActiveGISpatialPlaquettes
          H b hb e e' z z').card : ℝ) / N := hMB
    _ ≤ ((p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes
          H b hb (ε / 2) e e' z z').card : ℝ) / N := hCardDiv

/-- Quantitative SUFFICIENT fixed-threshold spatial criterion.
If a positive fraction of the ORIGINAL plaquettes has actual original
Wilson compensated GI response squared >= τ, then the true normalized
cancellation-free original local GI energy is >= τ times that fraction.
This direction does not require the amplitude ceiling. -/
theorem p4Q2PZ37Z_originalGI_absoluteActive_implies_energyFloor
    (hN : 0 < N) (τ ρ : ℝ) (hτ : 0 ≤ τ)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hActivity : ρ ≤
      ((p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes
        H b hb τ e e' z z').card : ℝ) / N) :
    τ * ρ ≤ Q e e' z z' / N := by
  classical
  let active : Finset Plaq :=
    p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes H b hb τ e e' z z'
  have hThreshold (p : Plaq) (hp : p ∈ active) :
      τ ≤ (d e e' z z' p) ^ 2 := by
    exact (Finset.mem_filter.mp hp).2
  have hOn : (∑ p ∈ active, τ) ≤
      ∑ p ∈ active, (d e e' z z' p) ^ 2 :=
    Finset.sum_le_sum (fun p hp => hThreshold p hp)
  have hAll : (∑ p ∈ active, (d e e' z z' p) ^ 2) ≤
      ∑ p : Plaq, (d e e' z z' p) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ active)
    intro p _hp _hn
    exact sq_nonneg _
  have hLower : τ * (active.card : ℝ) ≤ Q e e' z z' := by
    calc
      τ * (active.card : ℝ) = ∑ p ∈ active, τ := by
        simp only [Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ∑ p ∈ active, (d e e' z z' p) ^ 2 := hOn
      _ ≤ ∑ p : Plaq, (d e e' z z' p) ^ 2 := hAll
      _ = Q e e' z z' := rfl
  have hCount : ρ * N ≤ (active.card : ℝ) :=
    (le_div_iff₀ hN).mp hActivity
  apply (le_div_iff₀ hN).mpr
  calc
    τ * ρ * N = τ * (ρ * N) := by ring
    _ ≤ τ * (active.card : ℝ) :=
      mul_le_mul_of_nonneg_left hCount hτ
    _ ≤ Q e e' z z' := hLower

end FixedVolume

/-- A context-selectable variant of the U0 question, WITH ALL
quantifiers explicit. At each H, links and actual original boundary
configurations may differ; ε itself is H-independent.
This is a DEFINITION of the needed uniform statement, not a proof. -/
def p4Q2PZ37Z_contextSelectableOriginalGIUniformDensity
    (b : ℝ) (hb : 0 ≤ b) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ,
    ∃ e e' : p4Q2PZ37Z_Link H,
    ∃ z z' : p4Q2PZ37Z_Cfg H × p4Q2PZ37Z_Cfg H,
      ε ≤
        p4Q2LY_originalCompensatedLocalGISquareEnergy H b hb e e' z z' /
          (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)

/-- An equivalent SPATIAL criterion: fixed absolute squared threshold
τ>0 and fixed fraction ρ>0 at genuine Wilson contexts for EVERY H.
No new physical response nor auxiliary statistical distribution. -/
def p4Q2PZ37Z_contextSelectableOriginalGIUniformAbsoluteActivity
    (b : ℝ) (hb : 0 ≤ b) : Prop :=
  ∃ τ ρ : ℝ, 0 < τ ∧ 0 < ρ ∧ ∀ H : ℕ,
    ∃ e e' : p4Q2PZ37Z_Link H,
    ∃ z z' : p4Q2PZ37Z_Cfg H × p4Q2PZ37Z_Cfg H,
      ρ ≤
        ((p4Q2PZ37Z_originalGIAbsoluteActivePlaquettes
          H b hb τ e e' z z').card : ℝ) /
          (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)

/-- Exact U0-type criterion for the unchanged ORIGINAL Wilson spatial
GI minors. The size of the threshold and of the active fraction is
uniform in H, but the existence of such witnesses is NOT proved here.
The count-positivity premise concerns the genuine original plaquette
carrier; it is independent of any spectral lower or frame hypothesis. -/
theorem p4Q2PZ37Z_contextSelectableOriginalGI_uniformDensity_iff_absoluteActivity
    (b : ℝ) (hb : 0 ≤ b) (hbpos : 0 < b)
    (hcount : ∀ H : ℕ,
      0 < (p4Q2LP_originalSpatialPlaquetteCount H : ℝ)) :
    p4Q2PZ37Z_contextSelectableOriginalGIUniformDensity b hb ↔
      p4Q2PZ37Z_contextSelectableOriginalGIUniformAbsoluteActivity b hb := by
  constructor
  · rintro ⟨ε, hε, hWit⟩
    let E : ℝ := p4Q2LW_originalHarnackContrastScale b
    let M : ℝ := (4 * E ^ 2) ^ 2
    have hE : 0 < E := p4Q2LW_originalHarnackContrastScale_pos b hbpos
    have hM : 0 < M := by
      dsimp [M]
      positivity
    have hDen : 0 < 2 * M := mul_pos (by norm_num) hM
    refine ⟨ε / 2, ε / (2 * M),
      div_pos hε (by norm_num), div_pos hε hDen, ?_⟩
    intro H
    obtain ⟨e, e', z, z', hEnergy⟩ := hWit H
    refine ⟨e, e', z, z', ?_⟩
    simpa only [M, E] using
      (p4Q2PZ37Z_originalGI_energyFloor_implies_absoluteActive_density
        H b hb hbpos (hcount H) ε e e' z z' hEnergy)
  · rintro ⟨τ, ρ, hτ, hρ, hWit⟩
    refine ⟨τ * ρ, mul_pos hτ hρ, ?_⟩
    intro H
    obtain ⟨e, e', z, z', hActivity⟩ := hWit H
    exact ⟨e, e', z, z',
      p4Q2PZ37Z_originalGI_absoluteActive_implies_energyFloor
        H b hb (hcount H) τ ρ hτ.le e e' z z' hActivity⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Z_originalGI_energyFloor_implies_absoluteActive_density
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Z_originalGI_absoluteActive_implies_energyFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Z_contextSelectableOriginalGI_uniformDensity_iff_absoluteActivity
