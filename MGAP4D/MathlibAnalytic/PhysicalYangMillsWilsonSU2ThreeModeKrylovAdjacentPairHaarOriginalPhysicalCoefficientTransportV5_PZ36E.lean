import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEndpointMomentTransportV5_PZ36D
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalEndpointSixthCancellationAlgebraV5_PZ36B
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalScaledStrippedFifthAffineV5_PZ36
import Mathlib.Tactic

/-!
# P4-Q2-PZ36E — transport from genuine Haar moments to original jet signs

This module begins the ORIGINAL physical sixth Ward coefficient identification.
The fifth one-slab action-moment endpoint law is proved from the actual
right-stripped SU(2) spatial Haar integral, with the PZ36 affine correction.
The first through fifth action coefficients of PK, PP2, PX and PZ1 are
definitionally identified with the signed ORIGINAL PZ36D raw Haar moments.

These are source identities, not newly assumed moments. The remaining full
two-slab fifth endpoint transport and original mixed second/profile
coefficient identification are separate tasks. In particular this file
does NOT assert that Low6 or W6 is zero.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ36E_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ36E_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ36E_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ36E_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ36E_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ36E_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ36E_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section PhysicalCoefficientTransport
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : G))
local notation "R1" => p4Q2PZ36D_originalOneRaw H
local notation "R2" => p4Q2PZ36D_originalTwoRaw H

/-- The actual first signed PK coefficient is minus the first raw Haar moment. -/
theorem p4Q2PZ36E_originalFirstAction_eq_negRaw (B : Cfg) :
    p4Q2PK_originalOneSlabFirstActionMoment H B = -(R1 1 B) := by
  simp only [p4Q2PK_originalOneSlabFirstActionMoment,
    p4Q2PZ36D_originalOneRaw, pow_one]

/-- The original second PK coefficient is the genuine raw second moment. -/
theorem p4Q2PZ36E_originalSecondAction_eq_raw (B : Cfg) :
    p4Q2PK_originalOneSlabSecondActionMoment H B = R1 2 B := rfl

/-- The third PP2 moment has the negative exponential-Taylor sign. -/
theorem p4Q2PZ36E_originalOneThird_eq_negRaw (B : Cfg) :
    p4Q2PP2_originalOneSlabThirdActionMoment H B = -(R1 3 B) := rfl

theorem p4Q2PZ36E_originalTwoThird_eq_negRaw (B : Cfg) :
    p4Q2PP2_originalTwoSlabThirdActionMoment H B = -(R2 3 B) := rfl

theorem p4Q2PZ36E_originalOneFourth_eq_raw (B : Cfg) :
    p4Q2PX_originalOneSlabFourthActionMoment H B = R1 4 B := rfl

theorem p4Q2PZ36E_originalTwoFourth_eq_raw (B : Cfg) :
    p4Q2PX_originalTwoSlabFourthActionMoment H B = R2 4 B := rfl

theorem p4Q2PZ36E_originalOneFifth_eq_raw (B : Cfg) :
    p4Q2PZ1_originalOneSlabFifthActionMoment H B = R1 5 B := rfl

theorem p4Q2PZ36E_originalTwoFifth_eq_raw (B : Cfg) :
    p4Q2PZ1_originalTwoSlabFifthActionMoment H B = R2 5 B := rfl

/-- TRUE original one-slab stripped fifth moment at any right endpoint.
The identity-endpoint raw coefficient is the SAME original Wilson action,
not a surrogate right-stripped observable. -/
theorem p4Q2PZ36E_originalOneStripFifth_affine (B : Cfg) :
    (∫ X : Cfg, (w X + Cross X B)^5 ∂haar) =
      R1 5 I + (15 / 32 : ℝ) * w B := by
  have hI : R1 5 I =
      (∫ X : Cfg, (w X + Cross X I)^5 ∂haar) := by
    unfold p4Q2PZ36D_originalOneRaw
    apply integral_congr_ae
    filter_upwards with X
    rw [p4Q2PZ36C_originalOneSlab_eq_rightStripped H X I,
      p4Q2PZ35_originalHalfSpatialAction_identity_zero H]
    ring
  have hF := p4Q2PZ36_originalScaledStrippedFifth_affine H 1 B
  simp only [p4Q2PZ36_originalScaledStrippedFifth, one_mul, mul_one] at hF
  rw [← hI] at hF
  exact hF

/-- Genuine one-slab fifth raw moment with the previously omitted
four-link Haar correction. The six binomial sectors and original action
are kept exactly. Valid for every finite even period including H=0. -/
theorem p4Q2PZ36E_originalOneRaw_fifth_endpoint (B : Cfg) :
    R1 5 B =
      (w B)^5 + 5*(R1 1 I)*(w B)^4 +
        10*(R1 2 I)*(w B)^3 +
        10*(R1 3 I)*(w B)^2 +
        5*(R1 4 I)*(w B) + R1 5 I +
        (15 / 32 : ℝ)*w B := by
  have hc : Continuous (fun X : Cfg => w X + Cross X B) :=
    (p4Q2PZ36C_half_continuous H).add
      (p4Q2PZ36C_cross_continuous H B)
  have hExp : R1 5 B =
      ∑ k ∈ Finset.range 6, ((5 : ℕ).choose k : ℝ) *
        ((∫ X : Cfg, (w X+Cross X B)^k ∂haar)*(w B)^(5-k)) := by
    calc
      R1 5 B = (∫ X : Cfg, ((w X+Cross X B)+w B)^5 ∂haar) := by
        unfold p4Q2PZ36D_originalOneRaw
        apply integral_congr_ae
        filter_upwards with X
        rw [p4Q2PZ36C_originalOneSlab_eq_rightStripped H X B]
      _ = ∑ k ∈ Finset.range 6, ((5 : ℕ).choose k : ℝ) *
          (∫ X : Cfg, (w X+Cross X B)^k*(w B)^(5-k) ∂haar) := by
        simpa only [] using
          (p4Q2PZ36A_originalHaar_integral_binomial H
            (fun X : Cfg => w X+Cross X B)
            (fun _ : Cfg => w B) hc continuous_const 5)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [integral_mul_const]
  have h1 := p4Q2PZ36D_originalOneStrip_eq_identityRaw H 1 (by omega) B
  have h2 := p4Q2PZ36D_originalOneStrip_eq_identityRaw H 2 (by omega) B
  have h3 := p4Q2PZ36D_originalOneStrip_eq_identityRaw H 3 (by omega) B
  have h4 := p4Q2PZ36D_originalOneStrip_eq_identityRaw H 4 (by omega) B
  have h5 := p4Q2PZ36E_originalOneStripFifth_affine H B
  simp only [pow_one] at h1
  rw [hExp]
  simp [Finset.sum_range_succ, h1, h2, h3, h4, h5, Nat.choose]
  ring


/-- Original first raw moment is the true spatial half-Wilson action plus
the fixed compact-SU(2) Haar constant, with no surrogate boundary. -/
theorem p4Q2PZ36E_originalRawFirst_spatialAffine (B : Cfg) :
    R1 1 B = w B + p4Q2PY6_originalSecondActionLinearScalar H := by
  simpa only [p4Q2PZ36D_originalOneRaw,
    p4Q2PZ16_originalLeftSlabMoment, pow_one] using
    (p4Q2PZ18_originalCompleteFirst_eq_halfPlusAlpha H B)

/-- Actual one/two-slab first raw moments at the identity endpoint.
The complete intermediate slice and both original Haar integrations
are retained; this is the exact first-moment coefficient transport. -/
theorem p4Q2PZ36E_originalTwoFirst_identity_split :
    R2 1 I = R1 1 I + (∫ X : Cfg, R1 1 X ∂haar) := by
  have hR : Continuous (fun X : Cfg => R1 1 X) := by
    have heq : (fun X : Cfg => R1 1 X) =
        (fun X : Cfg => w X +
          p4Q2PY6_originalSecondActionLinearScalar H) := by
      funext X
      exact p4Q2PZ36E_originalRawFirst_spatialAffine H X
    rw [heq]
    exact (p4Q2PZ36C_half_continuous H).add continuous_const
  have hS (D : Cfg) : Continuous (fun X : Cfg => S X D) := by
    have heq : (fun X : Cfg => S X D) =
        (fun X : Cfg => (w X + Cross X D) + w D) := by
      funext X
      exact p4Q2PZ36C_originalOneSlab_eq_rightStripped H X D
    rw [heq]
    exact ((p4Q2PZ36C_half_continuous H).add
      (p4Q2PZ36C_cross_continuous H D)).add continuous_const
  have hInner (X : Cfg) :
      (∫ Y : Cfg, (p4Q2PK_originalTwoSlabAction H Y X I)^1 ∂haar) =
        R1 1 X + S X I := by
    have hSI : Integrable (fun Y : Cfg => S Y X) haar :=
      (hS X).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      (∫ Y : Cfg, (p4Q2PK_originalTwoSlabAction H Y X I)^1 ∂haar) =
          (∫ Y : Cfg, S Y X + S X I ∂haar) := by
            apply integral_congr_ae
            filter_upwards with Y
            change (S Y X + S X I)^1 = S Y X + S X I
            simp
      _ = (∫ Y : Cfg, S Y X ∂haar) + S X I := by
        rw [integral_add hSI (integrable_const (S X I))]
        simp
      _ = R1 1 X + S X I := by
        simp only [p4Q2PZ36D_originalOneRaw, pow_one]
  calc
    R2 1 I = (∫ X : Cfg, R1 1 X + S X I ∂haar) := by
      unfold p4Q2PZ36D_originalTwoRaw
      apply integral_congr_ae
      filter_upwards with X
      exact hInner X
    _ = (∫ X : Cfg, R1 1 X ∂haar) +
        (∫ X : Cfg, S X I ∂haar) := by
          simpa only [Pi.add_apply] using
            (integral_add
              (hR.integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _))
              ((hS I).integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)))
    _ = R1 1 I + (∫ X : Cfg, R1 1 X ∂haar) := by
      simp only [p4Q2PZ36D_originalOneRaw, pow_one]
      ring

/-- The highest-order true low-Ward quartic profile coefficient β₄
is exactly five times the difference of original two/one slab FIRST
identity Haar moments, not an assumed abstract shift coefficient. -/
theorem p4Q2PZ36E_originalLowCoeffHaar4_eq_trueMomentDifference :
    p4Q2PZ23_originalLowCoeffHaar4 H =
      5 * (R2 1 I - R1 1 I) := by
  have hβ :
      p4Q2PZ23_originalLowCoeffHaar4 H =
        5 * (∫ X : Cfg, R1 1 X ∂haar) := by
    change (∫ X : Cfg, p4Q2PZ23_originalLowCoeff4 H X ∂haar) = _
    calc
      (∫ X : Cfg, p4Q2PZ23_originalLowCoeff4 H X ∂haar) =
          (∫ X : Cfg, 5 * R1 1 X ∂haar) := by
            apply integral_congr_ae
            filter_upwards with X
            change 5 * (w X +
              p4Q2PY6_originalSecondActionLinearScalar H) = 5 * R1 1 X
            rw [p4Q2PZ36E_originalRawFirst_spatialAffine H X]
      _ = 5 * (∫ X : Cfg, R1 1 X ∂haar) := by
        rw [integral_const_mul]
  rw [hβ, p4Q2PZ36E_originalTwoFirst_identity_split H]
  ring

end PhysicalCoefficientTransport
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalFirstAction_eq_negRaw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalSecondAction_eq_raw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalOneThird_eq_negRaw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalTwoThird_eq_negRaw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalOneFourth_eq_raw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalTwoFourth_eq_raw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalOneFifth_eq_raw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalTwoFifth_eq_raw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalOneStripFifth_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalOneRaw_fifth_endpoint

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalRawFirst_spatialAffine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalTwoFirst_identity_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36E_originalLowCoeffHaar4_eq_trueMomentDifference
