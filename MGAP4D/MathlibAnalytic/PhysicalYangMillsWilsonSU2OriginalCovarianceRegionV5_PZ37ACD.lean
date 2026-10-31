import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCovarianceGIBoundsV5_PZ37ACC
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSourceRemoteCorrectionV5_PZ37ABR

/-!
# P4-Q2-PZ37ACD — original covariance regions and quantitative GI margins

The receiver F, transfer section U, true Perron coefficient P, both interacting
posterior laws and outer configuration pair-Haar are unchanged. Joint continuity
of F gives continuity of its actual Haar covariance and variance. A NONZERO
COVARIANCE WITNESS, when supplied, constructs an open positive-Haar region with
an explicit strict improvement of the relative regression defect. The exact ACA
identities transfer that improvement to the original U without any new locality
or fixed-link centering assumption.

A separate quantitative inequality converts covariance and variance estimates
on an arbitrary measurable outer event into the ACC absolute GI margin and its
original outer pair-Haar second-moment lower bound. A positive actual ACC margin
at one point constructs such a positive-mass event by continuity.

Boundary: this file does NOT prove the existence of the nonzero covariance
witness for the centered physical source, nor that the defect improvement is
large enough for the ACC positivity threshold. It does not assert any useful
H-uniform event mass, prefactor or GI margin. In particular nonzero GI is not
silently identified with nonzero energy covariance.
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
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "Cov" => CompactEnergyMismatchMoment.covariance μ
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ACD_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACD_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACD_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACD_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACD_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACD_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "U" => p4Q2PZ37ABZ_originalTransferSection H
local notation "P" => p4Q2PZ37ABZ_originalTransferSectionPrefactor H
local notation "LAbs" => p4Q2PZ37ACC_originalAbsoluteCovarianceGIMargin H
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H
local instance p4Q2PZ37ACD_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACD_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
/-! Keep the expensive full-support measure instance scoped to its use.
Global local instances here can multiply reducibility/instance-search work
while elaborating the large physical receiver and joint configuration type. -/
private theorem p4Q2PZ37ACD_outerOpenPos :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  letI : (normalizedCompactHaar G).IsOpenPosMeasure := by
    unfold normalizedCompactHaar
    infer_instance
  letI : (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    infer_instance
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

private theorem p4Q2PZ37ACD_receiver_joint_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) :
    Continuous (fun t : (Cfg × Cfg) × G => F b hb f e t.1 t.2) := by
  -- Only unfold the one-step receiver abbreviation. Avoid whnf expansion of
  -- the continuous-map constructor, updated Perron density and physical source.
  change Continuous (fun t : (Cfg × Cfg) × G =>
    (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) b hb f e) t)
  exact (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) b hb f e).continuous

private theorem p4Q2PZ37ACD_receiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Continuous (F b hb f e z) :=
  -- Use the already kernel-checked ACC/ACA point-section proof directly.
  -- Composing the polymorphic joint continuity theorem here makes whnf
  -- normalize the enormous original receiver again and exceeds heartbeats.
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num) b hb f e).continuous.comp
    (continuous_const.prodMk continuous_id)

/-- Actual Haar covariance varies continuously with both original boundaries. -/
theorem p4Q2PZ37ACD_originalReceiver_covariance_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) :
    Continuous (fun z : Cfg × Cfg => Cov (F b hb f e z) E) := by
  have hF := p4Q2PZ37ACD_receiver_joint_continuous H b hb f e
  have hm : Continuous (fun z : Cfg × Cfg => ∫ g : G, F b hb f e z g ∂μ) :=
    continuous_compactParameter_integral μ _ hF
  have hp : Continuous (fun t : (Cfg × Cfg) × G => F b hb f e t.1 t.2 * E t.2) :=
    hF.mul ((continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp continuous_snd)
  have hi : Continuous (fun z : Cfg × Cfg => ∫ g : G, F b hb f e z g * E g ∂μ) :=
    continuous_compactParameter_integral μ _ hp
  exact hi.sub (hm.mul continuous_const)

/-- Actual variance continuity is proved by its full first and second moments. -/
theorem p4Q2PZ37ACD_originalReceiver_variance_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) :
    Continuous (fun z : Cfg × Cfg => Var (F b hb f e z)) := by
  have hF := p4Q2PZ37ACD_receiver_joint_continuous H b hb f e
  have hm : Continuous (fun z : Cfg × Cfg => ∫ g : G, F b hb f e z g ∂μ) :=
    continuous_compactParameter_integral μ _ hF
  have hi : Continuous (fun z : Cfg × Cfg =>
      ∫ g : G, F b hb f e z g * F b hb f e z g ∂μ) :=
    continuous_compactParameter_integral μ _ (hF.mul hF)
  exact hi.sub (hm.mul hm)

/-- Continuity of the actual orientation-free ACC lower margin. -/
theorem p4Q2PZ37ACD_originalAbsoluteMargin_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) :
    Continuous (LAbs b hb f e) := by
  exact (continuous_const.mul
    (p4Q2PZ37ACD_originalReceiver_covariance_continuous H b hb f e).abs).sub
      (continuous_const.mul (Real.continuous_sqrt.comp
        (p4Q2PZ37ACD_originalReceiver_variance_continuous H b hb f e)))

/-- An explicit outer region defined by actual receiver moments, not a new law. -/
def p4Q2PZ37ACD_originalCovarianceRegion
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (c V : ℝ) : Set (Cfg × Cfg) :=
  {z | c < |Cov (F b hb f e z) E| ∧ Var (F b hb f e z) < V}
local notation "A" => p4Q2PZ37ACD_originalCovarianceRegion H

/-- The selected moment region is genuinely open in the original configuration topology. -/
theorem p4Q2PZ37ACD_originalCovarianceRegion_isOpen
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (c V : ℝ) :
    IsOpen (A b hb f e c V) :=
  (isOpen_lt continuous_const
    (p4Q2PZ37ACD_originalReceiver_covariance_continuous H b hb f e).abs).inter
      (isOpen_lt (p4Q2PZ37ACD_originalReceiver_variance_continuous H b hb f e)
        continuous_const)

/-- A supplied actual moment witness gives positive ORIGINAL outer Haar mass. -/
theorem p4Q2PZ37ACD_originalCovarianceRegion_mass_pos
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (c V : ℝ)
    (z0 : Cfg × Cfg) (hz0 : z0 ∈ A b hb f e c V) :
    0 < Measure.real outer (A b hb f e c V) := by
  letI : (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := p4Q2PZ37ACD_outerOpenPos H
  exact ENNReal.toReal_pos
    ((p4Q2PZ37ACD_originalCovarianceRegion_isOpen H b hb f e c V).measure_pos
      outer ⟨z0, hz0⟩).ne' (measure_ne_top _ _)

/-- Quantitative improvement of the full receiver regression defect on the
actual moment region. No small-defect hypothesis is inserted. -/
theorem p4Q2PZ37ACD_receiver_relativeDefect_on_region
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (c V eta : ℝ) (hc : 0 < c) (heta : 0 ≤ eta)
    (hbudget : eta * V ≤ 2 * c ^ 2)
    (z : Cfg × Cfg) (hz : z ∈ A b hb f e c V) :
    0 ≤ Var (F b hb f e z) - 4 * (Cov (F b hb f e z) E) ^ 2 ∧
      Var (F b hb f e z) - 4 * (Cov (F b hb f e z) E) ^ 2 ≤
        (1 - eta) * Var (F b hb f e z) := by
  have h4 := CompactEnergyMismatchMoment.four_covariance_sq_le_variance μ
    (F b hb f e z) E (p4Q2PZ37ACD_receiver_continuous H b hb f e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
    p4Q2PZ37ABZ_originalEnergy_Haar_variance
  have hc2 : c ^ 2 ≤ (Cov (F b hb f e z) E) ^ 2 := by
    have h := pow_le_pow_left₀ hc.le hz.1.le 2
    simpa only [sq_abs] using h
  have hscale := (mul_le_mul_of_nonneg_left hz.2.le heta).trans hbudget
  constructor
  · exact sub_nonneg.mpr h4
  · nlinarith only [hscale, hc2, sq_nonneg (Cov (F b hb f e z) E)]

/-- The SAME relative improvement for U: the true positive P squared cancels
by the proved ACA equalities, not by replacing the Perron representative. -/
theorem p4Q2PZ37ACD_transfer_relativeDefect_on_region
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (c V eta : ℝ) (hc : 0 < c) (heta : 0 ≤ eta)
    (hbudget : eta * V ≤ 2 * c ^ 2)
    (z : Cfg × Cfg) (hz : z ∈ A b hb f e c V) :
    0 ≤ Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2 ∧
      Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2 ≤
        (1 - eta) * Var (U b hb f e z) := by
  have hF := p4Q2PZ37ACD_receiver_relativeDefect_on_region H b hb f e
    c V eta hc heta hbudget z hz
  have hF0 := hF.1
  have hF1 := hF.2
  rw [p4Q2PZ37ACA_originalRegressionDefect_eq_transfer] at hF0
  rw [p4Q2PZ37ACA_originalRegressionDefect_eq_transfer,
    p4Q2PZ37ACA_originalReceiver_variance_eq_transfer] at hF1
  have hp : 0 < (P b hb z) ^ 2 :=
    pow_pos (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b hb z) 2
  constructor
  · by_contra hn
    have hneg := mul_neg_of_pos_of_neg hp (lt_of_not_ge hn)
    exact (not_lt_of_ge hF0) hneg
  · by_contra hn
    have hscaled := mul_lt_mul_of_pos_left (lt_of_not_ge hn) hp
    nlinarith only [hF1, hscaled]

/-- Conditional only on a genuine covariance witness: construct an explicit
open positive-Haar region and a strict relative-defect improvement for U.
This theorem does not construct that witness for the physical centered source. -/
theorem p4Q2PZ37ACD_exists_relativeDefectRegion_of_nonzeroCovariance
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z0 : Cfg × Cfg) (hC : Cov (F b hb f e z0) E ≠ 0) :
    ∃ c V eta : ℝ, 0 < c ∧ 0 < V ∧ 0 < eta ∧ eta < 1 ∧
      z0 ∈ A b hb f e c V ∧ 0 < Measure.real outer (A b hb f e c V) ∧
      ∀ z ∈ A b hb f e c V,
        0 ≤ Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2 ∧
          Var (U b hb f e z) - 4 * (Cov (U b hb f e z) E) ^ 2 ≤
            (1 - eta) * Var (U b hb f e z) := by
  let c : ℝ := |Cov (F b hb f e z0) E| / 2
  let V : ℝ := Var (F b hb f e z0) + 1
  let eta : ℝ := min (1 / 2 : ℝ) (2 * c ^ 2 / V)
  have hc : 0 < c := half_pos (abs_pos.mpr hC)
  have hV : 0 < V := by
    have hv := CompactEnergyMismatchMoment.variance_nonneg μ
      (F b hb f e z0) (p4Q2PZ37ACD_receiver_continuous H b hb f e z0)
    dsimp [V]
    linarith
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min (by norm_num) (div_pos (by positivity) hV)
  have heta1 : eta < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hbudget : eta * V ≤ 2 * c ^ 2 :=
    (le_div_iff₀ hV).mp (min_le_right _ _)
  have hz0 : z0 ∈ A b hb f e c V := by
    change c < |Cov (F b hb f e z0) E| ∧ Var (F b hb f e z0) < V
    dsimp [c, V]
    constructor <;> linarith [abs_pos.mpr hC]
  refine ⟨c, V, eta, hc, hV, heta, heta1, hz0,
    p4Q2PZ37ACD_originalCovarianceRegion_mass_pos H b hb f e c V z0 hz0, ?_⟩
  intro z hz
  exact p4Q2PZ37ACD_transfer_relativeDefect_on_region H b hb f e
    c V eta hc heta.le hbudget z hz

/-- The explicit margin available from covariance floor c and variance cap V.
Its sign is NOT asserted by the definition or by nonzero covariance alone. -/
def p4Q2PZ37ACD_quantitativeCovarianceMargin (b c V : ℝ) : ℝ :=
  b * (Real.exp (32 * b) + Real.exp (-32 * b)) * c -
    (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) * Real.sqrt V

/-- Actual moment estimates imply the exact ACC absolute lower margin. -/
theorem p4Q2PZ37ACD_quantitativeMargin_le_absoluteMargin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (c V : ℝ)
    (z : Cfg × Cfg)
    (hC : c ≤ |Cov (F b hb f e z) E|) (hV : Var (F b hb f e z) ≤ V) :
    p4Q2PZ37ACD_quantitativeCovarianceMargin b c V ≤ LAbs b hb f e z := by
  have ha : 0 ≤ b * (Real.exp (32 * b) + Real.exp (-32 * b)) := by positivity
  have hw : 0 ≤ Real.exp (32 * b) - Real.exp (-32 * b) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith))
  have hd : 0 ≤ (b / 2) * (Real.exp (32 * b) - Real.exp (-32 * b)) :=
    mul_nonneg (div_nonneg hb (by norm_num)) hw
  have hc := mul_le_mul_of_nonneg_left hC ha
  have hv := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hV) hd
  unfold p4Q2PZ37ACD_quantitativeCovarianceMargin
    p4Q2PZ37ACC_originalAbsoluteCovarianceGIMargin
  linarith

/-- A quantitative ORIGINAL outer pair-Haar second-moment bound. No common
orientation is required. Nonnegativity of the computed margin is explicit. -/
theorem p4Q2PZ37ACD_originalOuterMoment_lower_of_momentRegion
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (S : Set (Cfg × Cfg)) (hS : MeasurableSet S) (c V : ℝ)
    (hdelta : 0 ≤ p4Q2PZ37ACD_quantitativeCovarianceMargin b c V)
    (hMoments : ∀ z ∈ S,
      c ≤ |Cov (F b hb f e z) E| ∧ Var (F b hb f e z) ≤ V) :
    Measure.real outer S * (p4Q2PZ37ACD_quantitativeCovarianceMargin b c V) ^ 2 ≤
      ∫ z : Cfg × Cfg, (gap b hb f e z) ^ 2 ∂outer := by
  apply p4Q2PZ37ACC_originalOuterMoment_lower_of_absoluteCovarianceMargin
    H b hb f e S hS _ hdelta
  intro z hz
  exact p4Q2PZ37ACD_quantitativeMargin_le_absoluteMargin H b hb f e c V z
    (hMoments z hz).1 (hMoments z hz).2

/-- A positive actual ACC margin at a point gives a positive-Haar open region,
a strictly positive GI amplitude floor and the original squared-moment bound.
The pointwise positivity witness remains an explicit, unproved model obligation. -/
theorem p4Q2PZ37ACD_exists_positiveHaar_marginRegion_of_point
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link)
    (z0 : Cfg × Cfg) (h0 : 0 < LAbs b hb f e z0) :
    ∃ (S : Set (Cfg × Cfg)) (delta : ℝ), IsOpen S ∧ z0 ∈ S ∧
      0 < Measure.real outer S ∧ 0 < delta ∧
      (∀ z ∈ S, delta ≤ LAbs b hb f e z ∧ delta ≤ |gap b hb f e z|) ∧
      Measure.real outer S * delta ^ 2 ≤
        ∫ z : Cfg × Cfg, (gap b hb f e z) ^ 2 ∂outer := by
  let delta : ℝ := LAbs b hb f e z0 / 2
  let S : Set (Cfg × Cfg) := {z | delta < LAbs b hb f e z}
  have hd : 0 < delta := half_pos h0
  have hopen : IsOpen S := isOpen_lt continuous_const
    (p4Q2PZ37ACD_originalAbsoluteMargin_continuous H b hb f e)
  have hz0 : z0 ∈ S := by change delta < LAbs b hb f e z0; dsimp [delta]; linarith
  have hmass : 0 < Measure.real outer S := by
    letI : (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := p4Q2PZ37ACD_outerOpenPos H
    exact ENNReal.toReal_pos
      (hopen.measure_pos outer ⟨z0, hz0⟩).ne' (measure_ne_top _ _)
  have hbound : ∀ z ∈ S, delta ≤ LAbs b hb f e z := fun _ hz => hz.le
  refine ⟨S, delta, hopen, hz0, hmass, hd, ?_, ?_⟩
  · intro z hz
    exact ⟨hbound z hz, (hbound z hz).trans
      (p4Q2PZ37ACC_originalGI_abs_lower H b hb f e z)⟩
  · exact p4Q2PZ37ACC_originalOuterMoment_lower_of_absoluteCovarianceMargin
      H b hb f e S hopen.measurableSet delta hd.le hbound

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_originalReceiver_covariance_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_originalReceiver_variance_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_originalAbsoluteMargin_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_originalCovarianceRegion_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_originalCovarianceRegion_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_receiver_relativeDefect_on_region
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_transfer_relativeDefect_on_region
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_exists_relativeDefectRegion_of_nonzeroCovariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_quantitativeMargin_le_absoluteMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_originalOuterMoment_lower_of_momentRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACD_exists_positiveHaar_marginRegion_of_point
