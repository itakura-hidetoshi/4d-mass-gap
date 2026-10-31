import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalDeterminantSlopeV5_PZ37ABY
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalActualReceiverAlignmentV5_PZ37ABX
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABY — actual full signed tail versus Wilson-energy misalignment

Retain both original interacting posterior laws and the SAME physical
FF source receiver. Put Psi_s=s*(F(g)-F(h))*c_b(g,h), with the ORIGINAL
crossing c_b=2*b*(E(h)-E(g)). This is an actual signed function, not a
new law or a replacement observable in GI. The exact original pairing
s*Phi is k*Psi_s, where exp(-32*b)<=k<=exp(32*b).

Both complete positive and negative contributions are therefore bounded
by the corresponding actual crossing moments. In particular the ENTIRE
negative tail is between exp(-32*b)*M_- and exp(32*b)*M_-, with
M_-=integral max(-Psi_s,0). No tail upper bound N is assumed. Combine
these proved bounds with ABX's actual rectangle to expose a concrete
signed-margin inequality. Smallness of the physical mismatch moment,
H-uniform rectangle mass/amplitude, and continuum gap remain OPEN.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "ν" => Measure.prod μ μ
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "cross" => p4Q2PZ37ABU_temporalCrossLog
local instance p4Q2PZ37ABY_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABY_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABY_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABY_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABY_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABY_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

private theorem p4Q2PZ37ABY_max_mul (k a : ℝ) (hk : 0 ≤ k) :
    max (k * a) 0 = k * max a 0 := by
  by_cases ha : 0 ≤ a
  · rw [max_eq_left ha, max_eq_left (mul_nonneg hk ha)]
  · have ha0 : a ≤ 0 := (lt_of_not_ge ha).le
    rw [max_eq_right ha0, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hk ha0), mul_zero]

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local instance p4Q2PZ37ABY_links : Fintype Link := Fintype.ofFinite _
local notation "diff" => p4Q2PZ37ABX_originalReceiverDifference H
local notation "pair" => p4Q2PZ37ABT_originalSignedPair H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H
local notation "slope" => p4Q2PZ37ABY_originalDetSlope H

/-- Actual physical response difference times ORIGINAL Wilson crossing.
The real scalar s records orientation; it never replaces the physical f. -/
def p4Q2PZ37ABY_originalCrossPair
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (w : G × G) : ℝ :=
  s * diff b hb f e z w.1 w.2 * cross b w.1 w.2
local notation "psi" => p4Q2PZ37ABY_originalCrossPair H

/-- This crossing is exactly the true Wilson-energy difference, not a
surrogate monotonicity or independently chosen test function. -/
theorem p4Q2PZ37ABY_originalCrossPair_eq_energy
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (w : G × G) :
    psi b hb f e z s w =
      (2 * b) * (s * diff b hb f e z w.1 w.2 * (E w.2 - E w.1)) := by
  unfold p4Q2PZ37ABY_originalCrossPair
  rw [p4Q2PZ37ABV_temporalCrossLog_eq_energy]
  ring

/-- Genuine continuity before any full-tail integration. -/
theorem p4Q2PZ37ABY_originalCrossPair_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    Continuous (psi b hb f e z s) := by
  have hF := (p4Q2PZ37ABX_originalDifference_joint_continuous H b hb f e s).comp
    (continuous_const.prodMk (continuous_id : Continuous (fun w : G × G => w)))
  exact hF.mul (p4Q2PZ37ABV_temporalCrossLog_continuous b)

/-- Full positive-part crossing moment exists for every actual source. -/
theorem p4Q2PZ37ABY_originalCrossPart_integrable
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    Integrable (fun w => max (psi b hb f e z s w) 0) ν :=
  ((p4Q2PZ37ABY_originalCrossPair_continuous H b hb f e z s).max
    continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Full actual positive crossing moment; negative orientation yields the
complete physical mismatch moment rather than a restricted local tail. -/
noncomputable def p4Q2PZ37ABY_originalCrossPartMass
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) : ℝ :=
  ∫ w : G × G, max (psi b hb f e z s w) 0 ∂ν
local notation "mass" => p4Q2PZ37ABY_originalCrossPartMass H

private theorem p4Q2PZ37ABY_orientedPart_integrable
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    Integrable (fun w => max (s * pair b hb f e z w) 0) ν :=
  ((continuous_const.mul (p4Q2PZ37ABT_originalSignedPair_continuous H b hb f e z)).max
    continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Exact signed factorization in the original physical model. -/
theorem p4Q2PZ37ABY_originalOrientedPair_eq_slope_mul_crossPair
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (w : G × G) :
    s * pair b hb f e z w = slope b hb z.2 e w.1 w.2 * psi b hb f e z s w := by
  rcases w with ⟨g, h⟩
  rw [p4Q2PZ37ABW_originalPair_eq_receiver_mul_det,
    p4Q2PZ37ABY_originalDet_eq_slope_mul_cross]
  unfold p4Q2PZ37ABY_originalCrossPair p4Q2PZ37ABX_originalReceiverDifference
  ring

/-- Exact negative region: no negative contribution is discarded or
replaced by a positivity assertion about either posterior density. -/
theorem p4Q2PZ37ABY_originalPair_neg_iff_crossPair_neg
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (w : G × G) :
    s * pair b hb f e z w < 0 ↔ psi b hb f e z s w < 0 := by
  have hk : 0 < slope b hb z.2 e w.1 w.2 := (Real.exp_pos _).trans_le
    (p4Q2PZ37ABY_originalDetSlope_twoSided H b hb z.2 e w.1 w.2).1
  rw [p4Q2PZ37ABY_originalOrientedPair_eq_slope_mul_crossPair]
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg hk.le (le_of_not_gt hn))) h
  · intro h
    exact mul_neg_of_pos_of_neg hk h

/-- Both orientations have the same uniform positive-part comparison. -/
theorem p4Q2PZ37ABY_originalPart_pointwise_twoSided
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (s : ℝ) (w : G × G) :
    Real.exp (-32 * b) * max (psi b hb f e z s w) 0 ≤ max (s * pair b hb f e z w) 0 ∧
      max (s * pair b hb f e z w) 0 ≤ Real.exp (32 * b) * max (psi b hb f e z s w) 0 := by
  have hk := p4Q2PZ37ABY_originalDetSlope_twoSided H b hb z.2 e w.1 w.2
  have hk0 := (Real.exp_nonneg _).trans hk.1
  rw [p4Q2PZ37ABY_originalOrientedPair_eq_slope_mul_crossPair,
    p4Q2PZ37ABY_max_mul _ _ hk0]
  exact ⟨mul_le_mul_of_nonneg_right hk.1 (le_max_right _ _),
    mul_le_mul_of_nonneg_right hk.2 (le_max_right _ _)⟩

/-- Whole two-copy Haar integral comparison, with integrability proved.
Taking s or -s controls all positive or all negative contributions. -/
theorem p4Q2PZ37ABY_originalPart_integral_twoSided
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    Real.exp (-32 * b) * mass b hb f e z s ≤
      (∫ w : G × G, max (s * pair b hb f e z w) 0 ∂ν) ∧
    (∫ w : G × G, max (s * pair b hb f e z w) 0 ∂ν) ≤
      Real.exp (32 * b) * mass b hb f e z s := by
  have hM := p4Q2PZ37ABY_originalCrossPart_integrable H b hb f e z s
  have hP := p4Q2PZ37ABY_orientedPart_integrable H b hb f e z s
  constructor
  · have hi := integral_mono (hM.const_mul (Real.exp (-32 * b))) hP
      (fun w => (p4Q2PZ37ABY_originalPart_pointwise_twoSided H b hb f e z s w).1)
    rw [integral_const_mul] at hi
    exact hi
  · have hi := integral_mono hP (hM.const_mul (Real.exp (32 * b)))
      (fun w => (p4Q2PZ37ABY_originalPart_pointwise_twoSided H b hb f e z s w).2)
    rw [integral_const_mul] at hi
    exact hi

/-- The actual crossing moment is 2*b times the true physical receiver /
Wilson-energy moment. The formula includes b=0 without division by b. -/
theorem p4Q2PZ37ABY_originalCrossPartMass_eq_energyMoment
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    mass b hb f e z s = (2 * b) *
      ∫ w : G × G, max (s * diff b hb f e z w.1 w.2 * (E w.2 - E w.1)) 0 ∂ν := by
  unfold p4Q2PZ37ABY_originalCrossPartMass
  simp_rw [p4Q2PZ37ABY_originalCrossPair_eq_energy,
    p4Q2PZ37ABY_max_mul (2 * b) _ (by positivity)]
  rw [integral_const_mul]

/-- The complete ORIGINAL negative tail, without a local truncation. -/
noncomputable def p4Q2PZ37ABY_originalNegativeTail
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) : ℝ :=
  ∫ w : G × G, max (-(s * pair b hb f e z w)) 0 ∂ν

/-- No tail-cap N is postulated: the full true negative tail is bounded
on both sides by the actual physical crossing-mismatch moment. -/
theorem p4Q2PZ37ABY_originalNegativeTail_twoSided
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    Real.exp (-32 * b) * mass b hb f e z (-s) ≤
        p4Q2PZ37ABY_originalNegativeTail H b hb f e z s ∧
      p4Q2PZ37ABY_originalNegativeTail H b hb f e z s ≤
        Real.exp (32 * b) * mass b hb f e z (-s) := by
  simpa only [p4Q2PZ37ABY_originalNegativeTail, neg_mul] using
    p4Q2PZ37ABY_originalPart_integral_twoSided H b hb f e z (-s)

/-- Full signed GI sandwich; all positive and negative moments are the
actual ones and there is NO additional alignment or tail-cap hypothesis. -/
theorem p4Q2PZ37ABY_originalGI_signed_twoSided
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) (s : ℝ) :
    (Real.exp (-32 * b) * mass b hb f e z s -
        Real.exp (32 * b) * mass b hb f e z (-s)) / 2 ≤ s * gap b hb f e z ∧
      s * gap b hb f e z ≤
        (Real.exp (32 * b) * mass b hb f e z s -
          Real.exp (-32 * b) * mass b hb f e z (-s)) / 2 := by
  have hp := p4Q2PZ37ABY_originalPart_integral_twoSided H b hb f e z s
  have hn := p4Q2PZ37ABY_originalPart_integral_twoSided H b hb f e z (-s)
  have heq := integral_compactContinuous_eq_pos_sub_neg ν
    (fun w : G × G => s * pair b hb f e z w)
    (continuous_const.mul (p4Q2PZ37ABT_originalSignedPair_continuous H b hb f e z))
  rw [integral_const_mul] at heq
  simp only [neg_mul] at hn
  rw [p4Q2PZ37ABT_originalGI_eq_half_pair_integral]
  constructor <;> linarith [hp.1, hp.2, hn.1, hn.2]

/-- ABX's derived region supplies a genuine lower bound for the whole
positive crossing moment, with its actual (not 1/64-assumed) Haar mass. -/
theorem p4Q2PZ37ABY_rectangle_crossPositive_mass_lower
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    R.eta * R.kappa * Measure.real ν R.innerEvent ≤ mass b hb f e z R.sign := by
  have hPoint (w : G × G) (hw : w ∈ R.innerEvent) :
      R.eta * R.kappa ≤ max (psi b hb f e z R.sign w) 0 := by
    have ha := R.aligned z hz w hw
    have hmul := mul_le_mul ha.1 ha.2 R.kappa_pos.le (R.eta_pos.le.trans ha.1)
    exact hmul.trans (le_max_left _ _)
  have hInt := p4Q2PZ37ABY_originalCrossPart_integrable H b hb f e z R.sign
  have hSet : R.eta * R.kappa * Measure.real ν R.innerEvent ≤
      ∫ w in R.innerEvent, max (psi b hb f e z R.sign w) 0 ∂ν :=
    setIntegral_ge_of_const_le_real R.inner_open.measurableSet
      (measure_ne_top _ _) hPoint hInt.integrableOn
  have hFull : (∫ w in R.innerEvent, max (psi b hb f e z R.sign w) 0 ∂ν) ≤
      ∫ w : G × G, max (psi b hb f e z R.sign w) 0 ∂ν :=
    setIntegral_le_integral hInt (Filter.Eventually.of_forall (fun _ => le_max_right _ _))
  exact hSet.trans hFull

/-- Quantitative actual-model signed bound using the derived rectangle
AND the proved full-negative-tail bound. The mismatch is still present;
its smallness and H-uniform control are not asserted. -/
theorem p4Q2PZ37ABY_rectangle_GI_lower_with_actualMismatch
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (R : p4Q2PZ37ABX_OriginalAlignmentRectangle H b hb f e)
    (z : Cfg × Cfg) (hz : z ∈ R.outerEvent) :
    (R.eta * R.kappa * Real.exp (-32 * b) * Measure.real ν R.innerEvent -
      Real.exp (32 * b) * mass b hb f e z (-R.sign)) / 2 ≤
        R.sign * gap b hb f e z := by
  have hm := p4Q2PZ37ABY_rectangle_crossPositive_mass_lower H b hb f e R z hz
  have hscaled := mul_le_mul_of_nonneg_left hm (Real.exp_nonneg (-32 * b))
  have hbound := (p4Q2PZ37ABY_originalGI_signed_twoSided H b hb f e z R.sign).1
  nlinarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalCrossPair_eq_energy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalCrossPair_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalCrossPart_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalOrientedPair_eq_slope_mul_crossPair
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalPair_neg_iff_crossPair_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalPart_pointwise_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalPart_integral_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalCrossPartMass_eq_energyMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalNegativeTail_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_originalGI_signed_twoSided
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_rectangle_crossPositive_mass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABY_rectangle_GI_lower_with_actualMismatch
