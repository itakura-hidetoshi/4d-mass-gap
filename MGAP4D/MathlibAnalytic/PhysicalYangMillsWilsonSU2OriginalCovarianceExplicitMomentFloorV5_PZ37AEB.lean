import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPairHaarExplicitFloorV5_PZ37AEA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEB — explicit original physical covariance-square moment floor

AEA established the strict positive radius-only finite-H lower bound
  κ(R/(2*card(Link_H)+1))^(2*card(Link_H))
for the actual ORIGINAL interacting SU(2) boundary pair-Haar mass of
the actual full calibrated chordal D_H ball at EVERY center.

ADM proved genuine uniform continuity of the SAME ORIGINAL physical
centered-source Wilson FF covariance, producing a positive full-ball
radius around each actual nonzero covariance point. ADE already proved
the exact original physical covariance-square moment lower bound on
such a ball.

AEB composes these independently proved interfaces into a single
strictly positive, explicit formula-valued lower certificate:
  (|C_e(a)|/2)^2 * κ(R/(2*card(Link_H)+1))^(2*card(Link_H))
     <= S(H,b0,e)
for a genuine nonzero covariance witness a and an actual stability
radius R>0, for EVERY original physical spatial link e.

For a given verified on-ball amplitude A>0, an additional theorem
provides the same floor with A^2. All model objects remain exactly
the original interacting Wilson SU(2), genuine pair-Haar, centered
Gauss-law source, fixed FF receiver and two interacting posteriors.

The formula depends on H, a, R and the true covariance amplitude.
A closed numerical choice of R and covariance amplitude, H-uniform
coercivity, the GI threshold tests, and the 4D continuum physical
mass gap are NOT claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "Ball" => p4Q2PZ37ADL_originalFullBoundaryChordalBall H
local notation "κ" => p4Q2PZ37ADQ_sphereRadiusFraction
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H

local instance p4Q2PZ37AEB_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AEB_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Every actual nonzero centered physical covariance at a real
boundary-pair point supplies a strictly positive squared half-amplitude. -/
theorem p4Q2PZ37AEB_originalNonzeroCovariance_halfAmplitudeSq_pos
    (e : Link) (a : Pair)
    (ha : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0) :
    0 < (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 := by
  exact pow_pos (div_pos (abs_pos.mpr ha) (by norm_num)) _

/-- The actual nonzero physical half-amplitude and the AEA original
Haar radius-only floor combine into a STRICTLY positive real number. -/
theorem p4Q2PZ37AEB_originalNonzeroCovariance_explicitProduct_pos
    (e : Link) (a : Pair)
    (ha : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    0 <
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
        κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
          (2 * Fintype.card Link) := by
  exact mul_pos
    (p4Q2PZ37AEB_originalNonzeroCovariance_halfAmplitudeSq_pos H e a ha)
    (p4Q2PZ37AEA_explicitFloor_pos H R hR)

/-- A checkable radius/amplitude certificate: if the unchanged
physical covariance is at least A>0 in absolute value throughout
the TRUE D_H ball, then its real covariance-square moment is at
least A^2 times AEA's explicit original pair-Haar mass floor.
No unproved Lipschitz constant or substitute measure is assumed. -/
theorem p4Q2PZ37AEB_originalCertifiedBall_explicitMomentFloor
    (e : Link) (a : Pair) (R A : ℝ)
    (hR : 0 < R) (hA : 0 < A)
    (hStable : ∀ z ∈ Ball a R,
      A ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|) :
    A ^ 2 *
      κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) ≤
      S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  have hMoment :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e (Ball a R) A
      (p4Q2PZ37ADL_originalFullChordalBall_isOpen H a R)
      hA hStable
  have hHaar :=
    p4Q2PZ37AEA_originalFullBall_mass_ge_explicit H a R hR
  exact (mul_le_mul_of_nonneg_left hHaar (sq_nonneg A)).trans hMoment

/-- At ANY actual nonzero original centered-source covariance point
the ADM uniform modulus supplies R>0, whose original pair-Haar
quantitative floor gives an explicit strictly positive lower bound
for the SAME physical covariance-square moment. -/
theorem p4Q2PZ37AEB_originalNonzeroCovariance_explicitMomentWitness
    (e : Link) (a : Pair)
    (ha : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0) :
    ∃ R : ℝ, 0 < R ∧
      0 <
        κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
          (2 * Fintype.card Link) ∧
      0 <
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
          κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
            (2 * Fintype.card Link) ∧
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
        κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
          (2 * Fintype.card Link) ≤
        S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨R, hR, hStable⟩ :=
    p4Q2PZ37ADM_originalNonzeroCovariance_stableFullBall H e a ha
  have hA :
      0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2 :=
    div_pos (abs_pos.mpr ha) (by norm_num)
  have hLower :=
    p4Q2PZ37AEB_originalCertifiedBall_explicitMomentFloor
      H e a R
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2)
      hR hA hStable
  exact ⟨R, hR, p4Q2PZ37AEA_explicitFloor_pos H R hR,
    p4Q2PZ37AEB_originalNonzeroCovariance_explicitProduct_pos
      H e a ha R hR, hLower⟩

/-- For EVERY genuine original physical spatial link, ACI provides
an actual nonzero centered covariance point, so a finite-volume
explicit positive Wilson covariance-square moment certificate exists
without an external nonzero-point premise. -/
theorem p4Q2PZ37AEB_originalEveryLink_explicitMomentWitness
    (e : Link) :
    ∃ (a : Pair) (R : ℝ),
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0 ∧
      0 < R ∧
      0 <
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
          κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
            (2 * Fintype.card Link) ∧
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
        κ (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
          (2 * Fintype.card Link) ≤
        S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨a, ha⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
      (originalWilsonExplicitIdentityBoundary H)
  obtain ⟨R, hR, _hHaar, hPositive, hLower⟩ :=
    p4Q2PZ37AEB_originalNonzeroCovariance_explicitMomentWitness
      H e a ha
  exact ⟨a, R, ha, hR, hPositive, hLower⟩

/-- The original fixed-coupling finite-volume Wilson covariance-square
second moment is STRICTLY positive for EVERY genuine spatial link,
with an explicit (not numerically evaluated) supporting certificate.
This is a physical covariance-moment result, not a mass-gap theorem. -/
theorem p4Q2PZ37AEB_originalEveryLink_secondMoment_pos
    (e : Link) :
    0 < S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨_a, _R, _ha, _hR, hPositive, hLower⟩ :=
    p4Q2PZ37AEB_originalEveryLink_explicitMomentWitness H e
  exact hPositive.trans_le hLower

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEB_originalNonzeroCovariance_halfAmplitudeSq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEB_originalNonzeroCovariance_explicitProduct_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEB_originalCertifiedBall_explicitMomentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEB_originalNonzeroCovariance_explicitMomentWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEB_originalEveryLink_explicitMomentWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEB_originalEveryLink_secondMoment_pos
