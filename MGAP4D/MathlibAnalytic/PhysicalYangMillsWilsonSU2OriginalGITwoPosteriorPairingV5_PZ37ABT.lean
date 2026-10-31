import MGAP4D.MathlibAnalytic.CompactTwoDensitySignedPairing
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoWilsonPosteriorSourceExpectationGapV5_GI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ABT — genuine two-posterior signed pair formula

Keep the SAME original GI physical source, FF signed receiver, identity and
pi-rotated left boundaries, common right background, and normalized
interacting Wilson posterior laws. Rewrite their expectation difference as
one half the exact symmetric two-copy signed pairing. The two-copy Haar
reference is auxiliary; it is neither an independent-link approximation
nor a replacement of the outer original boundary pair-Haar law.

The density determinant factors through a strictly positive genuine
exponential weight and the difference of exponentials of the actual
log-odds. No sign of the physical receiver difference is assumed or
inferred. Both positive and negative contributions remain explicit.
A conditional mass-margin estimate is not a proved volume-uniform GI
floor, all-physical-Hilbert coercivity, or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local instance p4Q2PZ37ABT_group : IsTopologicalGroup G := specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ABT_compact : CompactSpace G := specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ABT_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ABT_measurable : MeasurableSpace G := specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ABT_borel : BorelSpace G := specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ABT_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local instance p4Q2PZ37ABT_links : Fintype Link := Fintype.ofFinite _
local notation "logW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
    H 2 (by norm_num)
local notation "left0" => originalWilsonExplicitIdentityBoundary H
local notation "left1" => p4Q2FQ_originalSU2LeftPiRotationAtLink H
local notation "response" => p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF H 2 (by norm_num)
local notation "gap" => p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H

/-- The actual normalized posterior density for an arbitrary original left boundary. -/
noncomputable def p4Q2PZ37ABT_originalPosteriorDensity
    (b : ℝ) (hb : 0 ≤ b) (A B : Cfg) (e : Link) : G → ℝ :=
  continuousNormalizedExp μ (logW b hb A B e)
local notation "density" => p4Q2PZ37ABT_originalPosteriorDensity H

/-- Continuity of the unchanged normalized interacting density. -/
theorem p4Q2PZ37ABT_originalPosteriorDensity_continuous
    (b : ℝ) (hb : 0 ≤ b) (A B : Cfg) (e : Link) : Continuous (density b hb A B e) :=
  continuous_continuousNormalizedExp μ _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) b hb A B e)

/-- Normalization by its own actual interacting partition function. -/
theorem p4Q2PZ37ABT_originalPosteriorDensity_mass_one
    (b : ℝ) (hb : 0 ≤ b) (A B : Cfg) (e : Link) :
    (∫ g : G, density b hb A B e g ∂μ) = 1 :=
  integral_compactNormalizedExp_eq_one μ _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) b hb A B e)

/-- Exact difference of the two genuine fiber log-weights, without a surrogate. -/
noncomputable def p4Q2PZ37ABT_originalPosteriorLogOdds
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g : G) : ℝ :=
  logW b hb left0 B e g - logW b hb (left1 e) B e g

/-- Pairing of the unchanged physical receiver and the two actual density rows. -/
noncomputable def p4Q2PZ37ABT_originalSignedPair
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) : G × G → ℝ :=
  twoDensitySignedPair
    (density b hb left0 z.2 e) (density b hb (left1 e) z.2 e)
    (fun g => response b hb f e (z, g))
local notation "pair" => p4Q2PZ37ABT_originalSignedPair H

/-- The signed two-point kernel is continuous in both auxiliary group variables. -/
theorem p4Q2PZ37ABT_originalSignedPair_continuous
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Continuous (pair b hb f e z) :=
  twoDensitySignedPair_continuous _ _ _
    (p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb left0 z.2 e)
    (p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb (left1 e) z.2 e)
    ((response b hb f e).continuous.comp (continuous_const.prodMk continuous_id))

/-- Genuine integrability of the two-copy signed kernel, before any estimate. -/
theorem p4Q2PZ37ABT_originalSignedPair_integrable
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    Integrable (pair b hb f e z) (Measure.prod μ μ) :=
  (p4Q2PZ37ABT_originalSignedPair_continuous H b hb f e z).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact symmetric two-copy formula for the ORIGINAL two-posterior GI gap. -/
theorem p4Q2PZ37ABT_originalGI_eq_half_pair_integral
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    gap b hb f e z = (1 / 2 : ℝ) * ∫ w : G × G, pair b hb f e z w ∂Measure.prod μ μ := by
  let P0 : G → ℝ := density b hb left0 z.2 e
  let P1 : G → ℝ := density b hb (left1 e) z.2 e
  let F : G → ℝ := fun g => response b hb f e (z, g)
  have h0 : Continuous P0 := p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb left0 z.2 e
  have h1 : Continuous P1 := p4Q2PZ37ABT_originalPosteriorDensity_continuous H b hb (left1 e) z.2 e
  have hF : Continuous F :=
    (response b hb f e).continuous.comp (continuous_const.prodMk continuous_id)
  have h0F : Integrable (fun g => P0 g * F g) μ :=
    (h0.mul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1F : Integrable (fun g => P1 g * F g) μ :=
    (h1.mul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpair : (∫ w : G × G, pair b hb f e z w ∂Measure.prod μ μ) =
      2 * ((∫ g : G, P0 g * F g ∂μ) - (∫ g : G, P1 g * F g ∂μ)) :=
    integral_twoDensitySignedPair_eq_two_mul_gap μ P0 P1 F h0 h1 hF
      (p4Q2PZ37ABT_originalPosteriorDensity_mass_one H b hb left0 z.2 e)
      (p4Q2PZ37ABT_originalPosteriorDensity_mass_one H b hb (left1 e) z.2 e)
  have hgap : gap b hb f e z =
      (∫ g : G, P0 g * F g ∂μ) - (∫ g : G, P1 g * F g ∂μ) := by
    rw [p4Q2GI_originalWilsonSignedTwoPosteriorExpectationGap_eq_HaarPairing]
    change (∫ g : G, F g * (P0 g - P1 g) ∂μ) = _
    calc
      _ = ∫ g : G, P0 g * F g - P1 g * F g ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        ring
      _ = _ := integral_sub h0F h1F
  rw [hgap, hpair]
  ring

/-- Exact positive and negative contributions; no negative region is discarded. -/
theorem p4Q2PZ37ABT_originalGI_eq_signed_pair_parts
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    gap b hb f e z = (1 / 2 : ℝ) *
      ((∫ w : G × G, max (pair b hb f e z w) 0 ∂Measure.prod μ μ) -
        (∫ w : G × G, max (-pair b hb f e z w) 0 ∂Measure.prod μ μ)) := by
  rw [p4Q2PZ37ABT_originalGI_eq_half_pair_integral,
    integral_compactContinuous_eq_pos_sub_neg (Measure.prod μ μ) _
      (p4Q2PZ37ABT_originalSignedPair_continuous H b hb f e z)]

/-- The exact strict positivity criterion is a positive-minus-negative margin,
not positivity of the posterior densities themselves. -/
theorem p4Q2PZ37ABT_originalGI_pos_iff_signed_pair_margin
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg) :
    0 < gap b hb f e z ↔
      (∫ w : G × G, max (-pair b hb f e z w) 0 ∂Measure.prod μ μ) <
        (∫ w : G × G, max (pair b hb f e z w) 0 ∂Measure.prod μ μ) := by
  rw [p4Q2PZ37ABT_originalGI_eq_signed_pair_parts]
  constructor <;> intro h <;> linarith

/-- Conditional quantitative bound: a positive contribution lower estimate
and a negative-tail upper estimate must BOTH be supplied. -/
theorem p4Q2PZ37ABT_originalGI_lower_of_pair_mass_bounds
    (b : ℝ) (hb : 0 ≤ b) (f : Phys) (e : Link) (z : Cfg × Cfg)
    (P N : ℝ)
    (hP : P ≤ ∫ w : G × G, max (pair b hb f e z w) 0 ∂Measure.prod μ μ)
    (hN : (∫ w : G × G, max (-pair b hb f e z w) 0 ∂Measure.prod μ μ) ≤ N) :
    (P - N) / 2 ≤ gap b hb f e z := by
  rw [p4Q2PZ37ABT_originalGI_eq_signed_pair_parts]
  linarith

/-- The determinant of the two original posterior density rows has exactly
the order of their actual log-odds. This makes no sign claim for the receiver. -/
theorem p4Q2PZ37ABT_originalPosteriorDet_nonneg_iff_logOdds
    (b : ℝ) (hb : 0 ≤ b) (B : Cfg) (e : Link) (g h : G) :
    0 ≤ density b hb left0 B e g * density b hb (left1 e) B e h -
      density b hb (left1 e) B e g * density b hb left0 B e h ↔
      p4Q2PZ37ABT_originalPosteriorLogOdds H b hb B e h ≤
        p4Q2PZ37ABT_originalPosteriorLogOdds H b hb B e g :=
  compactNormalizedExp_crossDet_nonneg_iff μ _ _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) b hb left0 B e)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
      H 2 (by norm_num) b hb (left1 e) B e) g h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABT_originalPosteriorDensity_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABT_originalPosteriorDensity_mass_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABT_originalSignedPair_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABT_originalSignedPair_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABT_originalGI_eq_half_pair_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABT_originalGI_eq_signed_pair_parts
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABT_originalGI_pos_iff_signed_pair_margin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABT_originalGI_lower_of_pair_mass_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ABT_originalPosteriorDet_nonneg_iff_logOdds
