import MGAP4D.MathlibAnalytic.CompactSymmetricMomentRegions
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalEnergyCovarianceV5_PZ37ACI
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCovarianceRegionV5_PZ37ACD

/-!
# P4-Q2-PZ37ACJ — actual covariance moments and simultaneous physical regions

For the SAME centered Gauss-law source, write C(z)=Cov_Haar(F_z,E) and
S=integral_outer C(z)^2. ACI's nonzero covariance on EVERY chosen link,
together with ACD's already proved continuity and genuine Haar regions,
gives S>0 at every finite H and b>0. The actual center-gauge transformation
preserves the original outer pair-Haar law and reverses C. Hence the outer
mean of C is zero and its positive and negative tails have equal mass.

Let B be the unchanged ACA/FC source envelope. The proved inequalities
4*C(z)^2 <= Var(F_z) <= B^2 imply 0<S<=B^2/4. For
  c=sqrt(S/2), d=B^2-2*S, Aplus={z | c<C(z)}, Aminus={z | C(z)<-c},
both OPEN actual outer events have mass at least S/d>0. On these SAME
events the oriented covariance is at least c and the actual physical
energy-regression defect is between zero and d. No nonzero moment,
positive mass, covariance floor or source-residual bound is assumed.

The constants retain the actual covariance integral, original transfer
norm and physical source norm. This is a finite-volume quantitative
certificate in those actual quantities, not an evaluated H-uniform floor.
The inequality needed for a positive GI margin is not proved here.
No kernel, Perron representative, physical source, posterior or outer law
is replaced; no continuum mass-gap conclusion follows.
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
local instance p4Q2PZ37ACJ_momentGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACJ_momentCompact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACJ_momentCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACJ_momentMeasurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACJ_momentBorel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACJ_momentProbability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "Γ" => p4Q2PZ37ACC_originalCenterGaugePair H
local instance p4Q2PZ37ACJ_momentLinks : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACJ_momentOuterProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The original centered physical receiver's actual Haar energy covariance. -/
def p4Q2PZ37ACJ_originalCenteredEnergyCovariance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : ℝ :=
  Cov (F b hb f₀ e z) E
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H

/-- The complete second moment under the SAME original outer pair-Haar law. -/
def p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  CompactSymmetricMomentRegions.secondMoment outer (C b hb e)
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H

/-- The literal existing FC source envelope, retaining the actual transfer norm. -/
def p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope
    (b : ℝ) (hb : 0 ≤ b) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b hb‖⁻¹ * (Real.exp (8 * b) ^ 3 - 1) * ‖f₀‖
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H

/-- A covariance level obtained from its actual, proved-positive second moment. -/
def p4Q2PZ37ACJ_originalCovarianceMomentThreshold
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ := Real.sqrt (S b hb e / 2)
local notation "c" => p4Q2PZ37ACJ_originalCovarianceMomentThreshold H

/-- A simultaneous actual source-defect cap on the selected covariance regions. -/
def p4Q2PZ37ACJ_originalCovarianceMomentDefectCap
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ := (B b hb) ^ 2 - 2 * S b hb e
local notation "d" => p4Q2PZ37ACJ_originalCovarianceMomentDefectCap H

/-- Positive covariance region in the original outer configuration space. -/
def p4Q2PZ37ACJ_originalPositiveCovarianceMomentRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Set Pair :=
  {z | c b hb e < C b hb e z}
local notation "Apos" => p4Q2PZ37ACJ_originalPositiveCovarianceMomentRegion H

/-- Negative covariance region in the original outer configuration space. -/
def p4Q2PZ37ACJ_originalNegativeCovarianceMomentRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Set Pair :=
  {z | C b hb e z < -c b hb e}
local notation "Aneg" => p4Q2PZ37ACJ_originalNegativeCovarianceMomentRegion H

private theorem p4Q2PZ37ACJ_momentCovariance_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : Continuous (C b hb e) :=
  p4Q2PZ37ACD_originalReceiver_covariance_continuous H b hb f₀ e

private theorem p4Q2PZ37ACJ_momentReceiver_continuous
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) : Continuous (F b hb f₀ e z) :=
  (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) b hb f₀ e).continuous.comp
      (continuous_const.prodMk continuous_id)

private theorem p4Q2PZ37ACJ_momentCenterGauge_measurePreserving (e : Link) :
    MeasurePreserving (Γ e) outer outer :=
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_measurePreserving
    H 2 (p4Q2PZ37ACC_originalCenterGauge H e)

private theorem p4Q2PZ37ACJ_momentCovariance_centerGauge
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    C b hb e (Γ e z) = -C b hb e z :=
  p4Q2PZ37ACC_centeredReceiver_covariance_centerGauge H b hb e z

private theorem p4Q2PZ37ACJ_momentCovariance_four_sq_le_variance
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    4 * (C b hb e z) ^ 2 ≤ Var (F b hb f₀ e z) :=
  CompactEnergyMismatchMoment.four_covariance_sq_le_variance μ
    (F b hb f₀ e z) E (p4Q2PZ37ACJ_momentReceiver_continuous H b hb e z)
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
    p4Q2PZ37ABZ_originalEnergy_Haar_variance

private theorem p4Q2PZ37ACJ_momentCovariance_sq_le_FC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) :
    (C b hb e z) ^ 2 ≤ (B b hb) ^ 2 / 4 := by
  have h4 := p4Q2PZ37ACJ_momentCovariance_four_sq_le_variance H b hb e z
  have hV := p4Q2PZ37ACA_originalReceiver_variance_le_FC H b hb f₀ e z
  change Var (F b hb f₀ e z) ≤ (B b hb) ^ 2 at hV
  linarith

/-- ACI discharges the covariance witness: EVERY actual link has positive
complete original outer covariance-square mass at every positive coupling. -/
theorem p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
    (b : ℝ) (hb : 0 < b) (e : Link) : 0 < S b hb.le e := by
  obtain ⟨z0, hz0⟩ := p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
    H b hb e (originalWilsonExplicitIdentityBoundary H)
  obtain ⟨a, V, _, ha, _, _, _, _, hmass, _⟩ :=
    p4Q2PZ37ACD_exists_relativeDefectRegion_of_nonzeroCovariance
      H b hb.le f₀ e z0 hz0
  let A : Set Pair := p4Q2PZ37ACD_originalCovarianceRegion H b hb.le f₀ e a V
  have hopen : IsOpen A :=
    p4Q2PZ37ACD_originalCovarianceRegion_isOpen H b hb.le f₀ e a V
  have hInt : Integrable (fun z : Pair => (C b hb.le e z) ^ 2) outer :=
    ((p4Q2PZ37ACJ_momentCovariance_continuous H b hb.le e).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (z : Pair) (hz : z ∈ A) : a ^ 2 ≤ (C b hb.le e z) ^ 2 := by
    have hAbs : a ≤ |C b hb.le e z| := hz.1.le
    simpa only [sq_abs] using pow_le_pow_left₀ ha.le hAbs 2
  have hSet : a ^ 2 * Measure.real outer A ≤
      ∫ z in A, (C b hb.le e z) ^ 2 ∂outer :=
    setIntegral_ge_of_const_le_real hopen.measurableSet (measure_ne_top _ _)
      hPoint hInt.integrableOn
  have hFull : (∫ z in A, (C b hb.le e z) ^ 2 ∂outer) ≤ S b hb.le e :=
    setIntegral_le_integral hInt (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  exact (mul_pos (pow_pos ha 2) hmass).trans_le (hSet.trans hFull)

/-- The actual covariance moment retains the original physical FC envelope. -/
theorem p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_le_FC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : S b hb e ≤ (B b hb) ^ 2 / 4 :=
  CompactSymmetricMomentRegions.secondMoment_le outer (C b hb e)
    (p4Q2PZ37ACJ_momentCovariance_continuous H b hb e) ((B b hb) ^ 2 / 4)
    (p4Q2PZ37ACJ_momentCovariance_sq_le_FC H b hb e)

/-- Exact zero outer mean follows from genuine measure-preserving center gauge.
It does not say the covariance vanishes pointwise or in outer L2. -/
theorem p4Q2PZ37ACJ_originalCenteredEnergyCovariance_outerMean_zero
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : (∫ z : Pair, C b hb e z ∂outer) = 0 :=
  CompactSymmetricMomentRegions.mean_eq_zero outer (C b hb e) (Γ e)
    (p4Q2PZ37ACJ_momentCovariance_continuous H b hb e)
    (p4Q2PZ37ACJ_momentCenterGauge_measurePreserving H e)
    (p4Q2PZ37ACJ_momentCovariance_centerGauge H b hb e)

/-- Both covariance tails have exactly equal ORIGINAL outer mass at any level.
No assertion that either zero-level tail has mass one-half is made. -/
theorem p4Q2PZ37ACJ_originalCenteredCovariance_tailMass_eq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (t : ℝ) :
    Measure.real outer {z : Pair | t < C b hb e z} =
      Measure.real outer {z : Pair | C b hb e z < -t} :=
  CompactSymmetricMomentRegions.positive_negative_tail_mass_eq outer (C b hb e) (Γ e)
    (p4Q2PZ37ACJ_momentCovariance_continuous H b hb e)
    (p4Q2PZ37ACJ_momentCenterGauge_measurePreserving H e)
    (p4Q2PZ37ACJ_momentCovariance_centerGauge H b hb e) t

/-- Both selected covariance events are open in the original outer topology. -/
theorem p4Q2PZ37ACJ_originalCovarianceMomentRegions_isOpen
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    IsOpen (Apos b hb e) ∧ IsOpen (Aneg b hb e) := by
  exact ⟨isOpen_lt continuous_const (p4Q2PZ37ACJ_momentCovariance_continuous H b hb e),
    isOpen_lt (p4Q2PZ37ACJ_momentCovariance_continuous H b hb e) continuous_const⟩

/-- The actual positive moment provides positive threshold, positive defect
cap and explicit lower masses for BOTH original sign events, without premises. -/
theorem p4Q2PZ37ACJ_originalCovarianceMomentRegions_mass_lower
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < c b hb.le e ∧ 0 < d b hb.le e ∧
      S b hb.le e / d b hb.le e ≤ Measure.real outer (Apos b hb.le e) ∧
      S b hb.le e / d b hb.le e ≤ Measure.real outer (Aneg b hb.le e) := by
  have h := CompactSymmetricMomentRegions.half_moment_tail_bounds outer
    (C b hb.le e) (Γ e) (p4Q2PZ37ACJ_momentCovariance_continuous H b hb.le e)
    (p4Q2PZ37ACJ_momentCenterGauge_measurePreserving H e)
    (p4Q2PZ37ACJ_momentCovariance_centerGauge H b hb.le e) ((B b hb.le) ^ 2 / 4)
    (p4Q2PZ37ACJ_momentCovariance_sq_le_FC H b hb.le e)
    (p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e)
  have hFour : 4 * ((B b hb.le) ^ 2 / 4) = (B b hb.le) ^ 2 := by ring
  simp only [hFour] at h
  exact h

private theorem p4Q2PZ37ACJ_momentThreshold_sq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : (c b hb e) ^ 2 = S b hb e / 2 := by
  have hS : 0 ≤ S b hb e := integral_nonneg (fun _ => sq_nonneg _)
  exact Real.sq_sqrt (div_nonneg hS (by norm_num))

private theorem p4Q2PZ37ACJ_momentDefect_bounds_of_threshold_sq
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair)
    (hC : (c b hb e) ^ 2 ≤ (C b hb e z) ^ 2) :
    0 ≤ Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2 ∧
      Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2 ≤ d b hb e := by
  have h4 := p4Q2PZ37ACJ_momentCovariance_four_sq_le_variance H b hb e z
  have hV := p4Q2PZ37ACA_originalReceiver_variance_le_FC H b hb f₀ e z
  change Var (F b hb f₀ e z) ≤ (B b hb) ^ 2 at hV
  rw [p4Q2PZ37ACJ_momentThreshold_sq H b hb e] at hC
  change 0 ≤ Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2 ∧
    Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2 ≤ (B b hb) ^ 2 - 2 * S b hb e
  constructor <;> linarith

/-- On the positive covariance event the SAME physical regression defect
has the stated simultaneous cap; no source-residual bound is assumed. -/
theorem p4Q2PZ37ACJ_originalDefect_on_positiveCovarianceMomentRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (hz : z ∈ Apos b hb e) :
    c b hb e ≤ C b hb e z ∧
      0 ≤ Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2 ∧
      Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2 ≤ d b hb e := by
  have hc : 0 ≤ c b hb e := Real.sqrt_nonneg _
  have hC : (c b hb e) ^ 2 ≤ (C b hb e z) ^ 2 :=
    pow_le_pow_left₀ hc hz.le 2
  exact ⟨hz.le, p4Q2PZ37ACJ_momentDefect_bounds_of_threshold_sq H b hb e z hC⟩

/-- On the negative covariance event the favorable orientation is -C.
The original physical receiver and its actual residual are unchanged. -/
theorem p4Q2PZ37ACJ_originalDefect_on_negativeCovarianceMomentRegion
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Pair) (hz : z ∈ Aneg b hb e) :
    c b hb e ≤ -C b hb e z ∧
      0 ≤ Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2 ∧
      Var (F b hb f₀ e z) - 4 * (C b hb e z) ^ 2 ≤ d b hb e := by
  have hc : 0 ≤ c b hb e := Real.sqrt_nonneg _
  have hlevel : c b hb e ≤ -C b hb e z := by
    have hz' : C b hb e z < -c b hb e := hz
    linarith
  have hC : (c b hb e) ^ 2 ≤ (C b hb e z) ^ 2 := by
    simpa only [neg_sq] using pow_le_pow_left₀ hc hlevel 2
  exact ⟨hlevel, p4Q2PZ37ACJ_momentDefect_bounds_of_threshold_sq H b hb e z hC⟩

/-- An unconditional simultaneous certificate on BOTH actual outer sign
regions at every finite H,b>0 and EVERY selected link. Its positive mass floor
uses the actual second moment, and no GI-positivity comparison is asserted. -/
theorem p4Q2PZ37ACJ_originalCenteredCovarianceMomentRegion_certificate
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < S b hb.le e ∧ 0 < c b hb.le e ∧ 0 < d b hb.le e ∧
      IsOpen (Apos b hb.le e) ∧ IsOpen (Aneg b hb.le e) ∧
      Measure.real outer (Apos b hb.le e) = Measure.real outer (Aneg b hb.le e) ∧
      0 < S b hb.le e / d b hb.le e ∧
      S b hb.le e / d b hb.le e ≤ Measure.real outer (Apos b hb.le e) ∧
      S b hb.le e / d b hb.le e ≤ Measure.real outer (Aneg b hb.le e) ∧
      (∀ z ∈ Apos b hb.le e, c b hb.le e ≤ C b hb.le e z ∧
        0 ≤ Var (F b hb.le f₀ e z) - 4 * (C b hb.le e z) ^ 2 ∧
        Var (F b hb.le f₀ e z) - 4 * (C b hb.le e z) ^ 2 ≤ d b hb.le e) ∧
      (∀ z ∈ Aneg b hb.le e, c b hb.le e ≤ -C b hb.le e z ∧
        0 ≤ Var (F b hb.le f₀ e z) - 4 * (C b hb.le e z) ^ 2 ∧
        Var (F b hb.le f₀ e z) - 4 * (C b hb.le e z) ^ 2 ≤ d b hb.le e) := by
  have hS := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  obtain ⟨hc, hd, hpos, hneg⟩ :=
    p4Q2PZ37ACJ_originalCovarianceMomentRegions_mass_lower H b hb e
  obtain ⟨hopenPos, hopenNeg⟩ := p4Q2PZ37ACJ_originalCovarianceMomentRegions_isOpen H b hb.le e
  have heq : Measure.real outer (Apos b hb.le e) = Measure.real outer (Aneg b hb.le e) :=
    p4Q2PZ37ACJ_originalCenteredCovariance_tailMass_eq H b hb.le e (c b hb.le e)
  exact ⟨hS, hc, hd, hopenPos, hopenNeg, heq, div_pos hS hd, hpos, hneg,
    fun z hz => p4Q2PZ37ACJ_originalDefect_on_positiveCovarianceMomentRegion H b hb.le e z hz,
    fun z hz => p4Q2PZ37ACJ_originalDefect_on_negativeCovarianceMomentRegion H b hb.le e z hz⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalCenteredEnergyCovariance_outerMean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalCenteredCovariance_tailMass_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalCovarianceMomentRegions_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalCovarianceMomentRegions_mass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalDefect_on_positiveCovarianceMomentRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalDefect_on_negativeCovarianceMomentRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACJ_originalCenteredCovarianceMomentRegion_certificate
