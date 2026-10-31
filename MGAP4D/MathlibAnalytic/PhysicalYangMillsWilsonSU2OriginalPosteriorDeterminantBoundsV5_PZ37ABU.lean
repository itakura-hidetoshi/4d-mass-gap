import MGAP4D.MathlibAnalytic.RealPositiveCrossLogDeterminant
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGITwoPosteriorPairingV5_PZ37ABT
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalNormalizedPosteriorTemporalLogCrossingV5_FR
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABU — genuine posterior determinant with uniform amplitude bounds

ABT's two ORIGINAL interacting posterior densities are unchanged. Their
cross determinant is the actual positive cross product times exp(c)-1,
where c is exactly the temporal Wilson energy crossing, independent of H,
the selected physical link and the right environment. FK bounds the
positive cross product between exp(-32*b) and exp(32*b). Hence c>=0 gives
a signed lower bound exp(-32*b)*c; swapping gives its absolute version.
At the genuine identity/pi pair, c=4*b for every physical link and volume.

The physical response is not changed or presumed aligned with this sign.
The last theorem keeps its alignment as an explicit conditional premise.
No positive GI margin, full negative-tail or outer pair-Haar mass floor,
all-Hilbert coercivity or continuum mass gap follows from these results.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "rot" => specialUnitaryTwoRotation Real.pi
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local instance p4Q2PZ37ABU_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABU_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABU_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABU_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABU_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2

/-- Literal Wilson temporal crossing for identity and pi-rotated left values.
No lattice-volume, background or physical-source argument occurs here. -/
noncomputable def p4Q2PZ37ABU_temporalCrossLog (b : ℝ) (g h : G) : ℝ :=
  -b * ((E g - E h) - (E (rot⁻¹ * g) - E (rot⁻¹ * h)))
local notation "cross" => p4Q2PZ37ABU_temporalCrossLog

/-- Swapping the auxiliary values reverses the exact temporal crossing. -/
theorem p4Q2PZ37ABU_temporalCrossLog_swap (b : ℝ) (g h : G) :
    cross b h g = -cross b g h := by
  unfold p4Q2PZ37ABU_temporalCrossLog
  ring

/-- The actual identity/pi crossing is 4*b, with no volume-dependent factor. -/
theorem p4Q2PZ37ABU_temporalCrossLog_one_pi (b : ℝ) :
    cross b 1 rot = 4 * b := by
  have hzero : E (1 : G) = 0 := specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num)
  have hpi : E rot = 2 :=
    GroundStatePosteriorJoint.originalWilsonExplicitPiRotation_energy_eq_two
  have hinv : E rot⁻¹ = 2 := by
    rw [specialUnitaryWilsonPlaquetteEnergy_inv]
    exact hpi
  unfold p4Q2PZ37ABU_temporalCrossLog
  simp only [mul_one, inv_mul_cancel, hzero, hpi, hinv]
  ring

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local instance p4Q2PZ37ABU_links : Fintype Link := Fintype.ofFinite _
local notation "left0" => originalWilsonExplicitIdentityBoundary H
local notation "left1" => p4Q2FQ_originalSU2LeftPiRotationAtLink H
local notation "density" => p4Q2PZ37ABT_originalPosteriorDensity H
local notation "response" => p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num)

/-- FK's bounds applied to the actual ABT normalized posterior density. -/
theorem p4Q2PZ37ABU_originalDensity_twoSided
    (b : ℝ) (hb : 0 ≤ b) (A B : Cfg) (e : Link) (g : G) :
    Real.exp (-16 * b) ≤ density b hb A B e g ∧
      density b hb A B e g ≤ Real.exp (16 * b) :=
  p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided H 2 (by norm_num) b hb A B e g

private theorem p4Q2PZ37ABU_density_pos
    (b : ℝ) (hb : 0 ≤ b) (A B : Cfg) (e : Link) (g : G) :
    0 < density b hb A B e g :=
  lt_of_lt_of_le (Real.exp_pos _) (p4Q2PZ37ABU_originalDensity_twoSided H b hb A B e g).1

/-- The cross logarithm of the two actual normalized density rows is exactly
the volume-independent temporal Wilson crossing. All spatial/Perron terms
and the two original normalizers cancel only in this cross difference. -/
theorem p4Q2PZ37ABU_originalLogCross_eq_temporal
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    (Real.log (density b hb left0 B e g) - Real.log (density b hb left0 B e h)) -
      (Real.log (density b hb (left1 e) B e g) -
        Real.log (density b hb (left1 e) B e h)) = cross b g h := by
  have hAt0 : left0 e = (1 : G) := rfl
  have hAt1 : left1 e e = rot := p4Q2FQ_originalSU2LeftPiRotationAtLink_value H e
  have hx := p4Q2FR_originalWilsonNormalizedPosteriorLogCrossing_eq_temporalEnergy
    H 2 (by norm_num) b hb left0 (left1 e) B e g h
  rw [hAt0, hAt1] at hx
  simpa only [inv_one, one_mul, p4Q2PZ37ABU_temporalCrossLog] using hx

/-- The cross determinant of the unchanged two actual posterior rows. -/
noncomputable def p4Q2PZ37ABU_originalPosteriorDet
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) : ℝ :=
  density b hb left0 B e g * density b hb (left1 e) B e h -
    density b hb (left1 e) B e g * density b hb left0 B e h
local notation "det" => p4Q2PZ37ABU_originalPosteriorDet H

/-- The density determinant reverses sign when the auxiliary copies swap. -/
theorem p4Q2PZ37ABU_originalDet_swap
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    det b hb B e h g = -det b hb B e g h := by
  unfold p4Q2PZ37ABU_originalPosteriorDet
  ring

/-- Exact determinant: the actual positive cross product is NOT discarded. -/
theorem p4Q2PZ37ABU_originalDet_eq_crossRatio
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    det b hb B e g h =
      (density b hb (left1 e) B e g * density b hb left0 B e h) *
        (Real.exp (cross b g h) - 1) := by
  have hx := realPositiveCrossDet_eq_exp_crossLog
    (density b hb left0 B e g) (density b hb (left1 e) B e g)
    (density b hb left0 B e h) (density b hb (left1 e) B e h)
    (p4Q2PZ37ABU_density_pos H b hb left0 B e g)
    (p4Q2PZ37ABU_density_pos H b hb (left1 e) B e g)
    (p4Q2PZ37ABU_density_pos H b hb left0 B e h)
    (p4Q2PZ37ABU_density_pos H b hb (left1 e) B e h)
  rw [p4Q2PZ37ABU_originalLogCross_eq_temporal H b hb B e g h] at hx
  exact hx

/-- Uniform bounds on the actual positive cross product, not an abstract
partition surrogate or an absolute full-configuration mass assertion. -/
theorem p4Q2PZ37ABU_originalCrossProduct_twoSided
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    Real.exp (-32 * b) ≤ density b hb (left1 e) B e g * density b hb left0 B e h ∧
      density b hb (left1 e) B e g * density b hb left0 B e h ≤ Real.exp (32 * b) := by
  have h1 := p4Q2PZ37ABU_originalDensity_twoSided H b hb (left1 e) B e g
  have h0 := p4Q2PZ37ABU_originalDensity_twoSided H b hb left0 B e h
  have h1pos := (p4Q2PZ37ABU_density_pos H b hb (left1 e) B e g).le
  have h0pos := (p4Q2PZ37ABU_density_pos H b hb left0 B e h).le
  have hlo : Real.exp (-16 * b) * Real.exp (-16 * b) = Real.exp (-32 * b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hhi : Real.exp (16 * b) * Real.exp (16 * b) = Real.exp (32 * b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  constructor
  · rw [← hlo]
    exact mul_le_mul h1.1 h0.1 (Real.exp_nonneg _) h1pos
  · rw [← hhi]
    exact mul_le_mul h1.2 h0.2 h0pos (Real.exp_nonneg _)

/-- The determinant sign is precisely the original temporal crossing sign. -/
theorem p4Q2PZ37ABU_originalDet_nonneg_iff
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    0 ≤ det b hb B e g h ↔ 0 ≤ cross b g h := by
  have hp := mul_pos (p4Q2PZ37ABU_density_pos H b hb (left1 e) B e g)
    (p4Q2PZ37ABU_density_pos H b hb left0 B e h)
  rw [p4Q2PZ37ABU_originalDet_eq_crossRatio]
  constructor
  · intro hnonneg
    by_contra hc
    have hx : Real.exp (cross b g h) < 1 := by
      simpa only [Real.exp_zero] using (Real.exp_lt_exp.mpr (lt_of_not_ge hc))
    nlinarith
  · intro hc
    have hx : 1 ≤ Real.exp (cross b g h) := by
      simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hc)
    exact mul_nonneg hp.le (sub_nonneg.mpr hx)

/-- Quantitative positive-region determinant lower bound, uniform in H,
link and background. The crossing itself is the original Wilson energy. -/
theorem p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G)
    (hc : 0 ≤ cross b g h) :
    Real.exp (-32 * b) * cross b g h ≤ det b hb B e g h := by
  have hlin : cross b g h ≤ Real.exp (cross b g h) - 1 := by
    linarith [Real.add_one_le_exp (cross b g h)]
  have hexp : 0 ≤ Real.exp (cross b g h) - 1 := le_trans hc hlin
  rw [p4Q2PZ37ABU_originalDet_eq_crossRatio]
  calc
    _ ≤ Real.exp (-32 * b) * (Real.exp (cross b g h) - 1) :=
      mul_le_mul_of_nonneg_left hlin (Real.exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (p4Q2PZ37ABU_originalCrossProduct_twoSided H b hb B e g h).1 hexp

/-- Both orientations retain a uniform absolute determinant floor. This is
a density statement, not a signed physical-response expectation floor. -/
theorem p4Q2PZ37ABU_originalDet_abs_lower
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    Real.exp (-32 * b) * |cross b g h| ≤ |det b hb B e g h| := by
  by_cases hc : 0 ≤ cross b g h
  · have hd := (p4Q2PZ37ABU_originalDet_nonneg_iff H b hb B e g h).mpr hc
    simpa only [abs_of_nonneg hc, abs_of_nonneg hd] using
      (p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg H b hb B e g h hc)
  · have hc' : cross b g h ≤ 0 := (lt_of_not_ge hc).le
    have hswap : 0 ≤ cross b h g := by
      rw [p4Q2PZ37ABU_temporalCrossLog_swap]
      exact neg_nonneg.mpr hc'
    have hd := (p4Q2PZ37ABU_originalDet_nonneg_iff H b hb B e h g).mpr hswap
    rw [p4Q2PZ37ABU_originalDet_swap] at hd
    have hd' : det b hb B e g h ≤ 0 := neg_nonneg.mp hd
    have hlow := p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg H b hb B e h g hswap
    rw [p4Q2PZ37ABU_temporalCrossLog_swap, p4Q2PZ37ABU_originalDet_swap] at hlow
    simpa only [abs_of_nonpos hc', abs_of_nonpos hd'] using hlow

/-- Every original link has this explicit identity/pi determinant lower bound. -/
theorem p4Q2PZ37ABU_originalDet_one_pi_lower
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) :
    Real.exp (-32 * b) * (4 * b) ≤ det b hb B e 1 rot := by
  have hc : 0 ≤ cross b 1 rot := by
    rw [p4Q2PZ37ABU_temporalCrossLog_one_pi]
    positivity
  simpa only [p4Q2PZ37ABU_temporalCrossLog_one_pi] using
    (p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg H b hb B e 1 rot hc)

/-- Strict positivity at the explicit original pair for every b>0. -/
theorem p4Q2PZ37ABU_originalDet_one_pi_pos
    (b : ℝ) (hb : 0 < b) (B : Cfg) (e : Link) :
    0 < det b hb.le B e 1 rot :=
  lt_of_lt_of_le (mul_pos (Real.exp_pos _) (mul_pos (by norm_num) hb))
    (p4Q2PZ37ABU_originalDet_one_pi_lower H b hb.le B e)

/-- The unchanged physical signed pair inherits a lower bound ONLY where
its response difference and original temporal crossing are both nonnegative.
No such alignment is asserted globally or for an unproved physical source. -/
theorem p4Q2PZ37ABU_originalSignedPair_lower_of_alignment
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (g h : G)
    (hc : 0 ≤ cross b g h)
    (hF : 0 ≤ response b hb f e (z, g) - response b hb f e (z, h)) :
    Real.exp (-32 * b) *
      ((response b hb f e (z, g) - response b hb f e (z, h)) * cross b g h) ≤
        p4Q2PZ37ABT_originalSignedPair H b hb f e z (g, h) := by
  change _ ≤ (response b hb f e (z, g) - response b hb f e (z, h)) * det b hb z.2 e g h
  calc
    _ = (response b hb f e (z, g) - response b hb f e (z, h)) *
        (Real.exp (-32 * b) * cross b g h) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg H b hb z.2 e g h hc) hF

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABU_temporalCrossLog_swap
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ABU_temporalCrossLog_one_pi
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalDensity_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalLogCross_eq_temporal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalDet_swap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalDet_eq_crossRatio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalCrossProduct_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalDet_nonneg_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalDet_lower_of_cross_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalDet_abs_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalDet_one_pi_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalDet_one_pi_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABU_originalSignedPair_lower_of_alignment
