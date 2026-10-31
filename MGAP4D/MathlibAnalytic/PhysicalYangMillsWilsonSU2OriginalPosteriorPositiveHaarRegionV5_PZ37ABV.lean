import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyHaarCapsV5_PZ37ABV
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorDeterminantBoundsV5_PZ37ABU
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABV — quantitative genuine posterior positive Haar region

Keep ABU's two ORIGINAL interacting posterior densities and determinant.
The exact SU(2) antipodal energy identity makes the temporal crossing
`2*b*(E h-E g)`. Its variation from the original identity/pi pair is
explicit. The fixed low/high energy cap pair is a neighborhood of that
pair, has original auxiliary product-Haar mass at least 1/64, and has
crossing at least 2*b. The actual determinant integral over that region
is therefore at least `b*exp(-32*b)/32`, uniformly in finite H, actual
link and right background, and is strictly positive when b>0.

The auxiliary two-copy Haar is the same one used in ABT. This is a
restricted integral of the actual determinant, not a positive signed GI
response or an outer physical boundary pair-Haar floor. No sign of the
physical response difference is asserted; negative-tail cancellation,
all-Hilbert coercivity and continuum mass gap remain open.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "rot" => specialUnitaryTwoRotation Real.pi
local notation "cross" => p4Q2PZ37ABU_temporalCrossLog
local notation "cap" => p4Q2PZ37ABV_pairCap

local instance p4Q2PZ37ABV_region_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABV_region_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABV_region_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABV_region_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABV_region_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABV_region_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Exact original temporal crossing in actual SU(2) Wilson energies. -/
theorem p4Q2PZ37ABV_temporalCrossLog_eq_energy
    (b : ℝ) (g h : G) :
    cross b g h = 2 * b * (E h - E g) := by
  unfold p4Q2PZ37ABU_temporalCrossLog
  rw [p4Q2PZ37ABV_piInv_mul_energy, p4Q2PZ37ABV_piInv_mul_energy]
  ring

/-- Continuity of the exact original crossing on both auxiliary copies. -/
theorem p4Q2PZ37ABV_temporalCrossLog_continuous (b : ℝ) :
    Continuous (fun w : G × G => cross b w.1 w.2) := by
  simp_rw [p4Q2PZ37ABV_temporalCrossLog_eq_energy]
  exact continuous_const.mul
    (((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp continuous_snd).sub
      ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp continuous_fst))

/-- Exact variation from the identity/pi value; no volume or background enters. -/
theorem p4Q2PZ37ABV_temporalCrossLog_deficit
    (b : ℝ) (g h : G) :
    4 * b - cross b g h = 2 * b * (E g + (2 - E h)) := by
  rw [p4Q2PZ37ABV_temporalCrossLog_eq_energy]
  ring

/-- Quantitative absolute variation in the two original energy coordinates. -/
theorem p4Q2PZ37ABV_temporalCrossLog_abs_deviation
    (b : ℝ) (hb : 0 ≤ b) (g h : G) :
    |cross b g h - 4 * b| = 2 * b * (E g + (2 - E h)) := by
  have hnonneg : 0 ≤ 2 * b * (E g + (2 - E h)) :=
    mul_nonneg (mul_nonneg (by norm_num) hb)
      (add_nonneg (specialUnitaryWilsonPlaquetteEnergy_nonneg (by norm_num) g)
        (sub_nonneg.mpr (specialUnitaryWilsonPlaquetteEnergy_le_two (by norm_num) h)))
  rw [abs_sub_comm, p4Q2PZ37ABV_temporalCrossLog_deficit, abs_of_nonneg hnonneg]

/-- The fixed measurable cap pair contains a genuine neighborhood of (1,rot). -/
theorem p4Q2PZ37ABV_pairCap_mem_nhds : cap ∈ 𝓝 ((1 : G), rot) := by
  have hE := continuous_specialUnitaryWilsonPlaquetteEnergy 2
  have ho : IsOpen {w : G × G | E w.1 < (1 / 2 : ℝ) ∧ (3 / 2 : ℝ) < E w.2} :=
    (isOpen_lt (hE.comp continuous_fst) continuous_const).inter
      (isOpen_lt continuous_const (hE.comp continuous_snd))
  have hm : ((1 : G), rot) ∈
      {w : G × G | E w.1 < (1 / 2 : ℝ) ∧ (3 / 2 : ℝ) < E w.2} := by
    change E (1 : G) < (1 / 2 : ℝ) ∧ (3 / 2 : ℝ) < E rot
    rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num),
      GroundStatePosteriorJoint.originalWilsonExplicitPiRotation_energy_eq_two]
    norm_num
  exact Filter.mem_of_superset (ho.mem_nhds hm) (fun _ hw => ⟨hw.1.le, hw.2.le⟩)

/-- On the fixed positive-mass cap pair, the exact temporal crossing is at least 2*b. -/
theorem p4Q2PZ37ABV_temporalCrossLog_lower_on_pairCap
    (b : ℝ) (hb : 0 ≤ b) (g h : G) (hcap : (g, h) ∈ cap) :
    2 * b ≤ cross b g h := by
  have hg : E g ≤ (1 / 2 : ℝ) := hcap.1
  have hh : (3 / 2 : ℝ) ≤ E h := hcap.2
  have hgap : (1 : ℝ) ≤ E h - E g := by linarith
  rw [p4Q2PZ37ABV_temporalCrossLog_eq_energy]
  calc
    2 * b = 2 * b * 1 := by ring
    _ ≤ 2 * b * (E h - E g) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local instance p4Q2PZ37ABV_region_links : Fintype Link := Fintype.ofFinite _
local notation "left0" => originalWilsonExplicitIdentityBoundary H
local notation "left1" => p4Q2FQ_originalSU2LeftPiRotationAtLink H
local notation "density" => p4Q2PZ37ABT_originalPosteriorDensity H
local notation "det" => p4Q2PZ37ABU_originalPosteriorDet H

/-- Continuity of the actual determinant of the two unchanged density rows. -/
theorem p4Q2PZ37ABV_originalDet_continuous
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Continuous (fun w : G × G => det b hb B e w.1 w.2) := by
  have h0 := p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb left0 B e
  have h1 := p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb (left1 e) B e
  change Continuous (fun w : G × G =>
    density b hb left0 B e w.1 * density b hb (left1 e) B e w.2 -
      density b hb (left1 e) B e w.1 * density b hb left0 B e w.2)
  exact ((h0.comp continuous_fst).mul (h1.comp continuous_snd)).sub
    ((h1.comp continuous_fst).mul (h0.comp continuous_snd))

/-- Genuine product-Haar integrability before taking any restricted integral. -/
theorem p4Q2PZ37ABV_originalDet_integrable
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Integrable (fun w : G × G => det b hb B e w.1 w.2) (Measure.prod μ μ) :=
  (p4Q2PZ37ABV_originalDet_continuous H b hb B e).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The actual determinant has a uniform quantitative floor on the fixed cap. -/
theorem p4Q2PZ37ABV_originalDet_lower_on_pairCap
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G)
    (hcap : (g, h) ∈ cap) :
    Real.exp (-32 * b) * (2 * b) ≤ det b hb B e g h := by
  have hc := p4Q2PZ37ABV_temporalCrossLog_lower_on_pairCap b hb g h hcap
  have hc0 : 0 ≤ cross b g h := le_trans (by positivity) hc
  exact (mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)).trans
    (p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg H b hb B e g h hc0)

/-- Actual restricted determinant integral: all finite H, links and backgrounds. -/
theorem p4Q2PZ37ABV_originalDet_pairCap_integral_lower
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    b * Real.exp (-32 * b) / 32 ≤
      ∫ w in cap, det b hb B e w.1 w.2 ∂(Measure.prod μ μ) := by
  have hset : (Real.exp (-32 * b) * (2 * b)) * Measure.real (Measure.prod μ μ) cap ≤
      ∫ w in cap, det b hb B e w.1 w.2 ∂(Measure.prod μ μ) :=
    setIntegral_ge_of_const_le_real p4Q2PZ37ABV_pairCap_measurable
      (measure_ne_top _ _)
      (fun w hw => p4Q2PZ37ABV_originalDet_lower_on_pairCap H b hb B e w.1 w.2 hw)
      (p4Q2PZ37ABV_originalDet_integrable H b hb B e).integrableOn
  calc
    b * Real.exp (-32 * b) / 32 =
        (Real.exp (-32 * b) * (2 * b)) * (1 / 64 : ℝ) := by ring
    _ ≤ (Real.exp (-32 * b) * (2 * b)) * Measure.real (Measure.prod μ μ) cap :=
      mul_le_mul_of_nonneg_left p4Q2PZ37ABV_pairCap_real_mass_lower (by positivity)
    _ ≤ _ := hset

/-- For positive coupling, the unchanged determinant's cap integral is positive. -/
theorem p4Q2PZ37ABV_originalDet_pairCap_integral_pos
    (b : ℝ) (hb : 0 < b) (B : Cfg) (e : Link) :
    0 < ∫ w in cap, det b hb.le B e w.1 w.2 ∂(Measure.prod μ μ) :=
  lt_of_lt_of_le (div_pos (mul_pos hb (Real.exp_pos _)) (by norm_num))
    (p4Q2PZ37ABV_originalDet_pairCap_integral_lower H b hb.le B e)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_temporalCrossLog_eq_energy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_temporalCrossLog_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_temporalCrossLog_deficit
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_temporalCrossLog_abs_deviation
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_pairCap_mem_nhds
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABV_temporalCrossLog_lower_on_pairCap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABV_originalDet_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABV_originalDet_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABV_originalDet_lower_on_pairCap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABV_originalDet_pairCap_integral_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABV_originalDet_pairCap_integral_pos
