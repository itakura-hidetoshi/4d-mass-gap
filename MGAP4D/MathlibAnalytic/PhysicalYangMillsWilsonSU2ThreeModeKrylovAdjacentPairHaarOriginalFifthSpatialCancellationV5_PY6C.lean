import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSecondActionQuadraticV5_PY6B
import Mathlib.Tactic

/-!
# P4-Q2-PY6C — exact cancellation of the quadratic fifth-Ward counterterm

PY5 gives C2=6∫b-12∫w*h-12∫h*Cross(identity).
PY proves s_H=3∫b−6 J(identity), where the ORIGINAL genuine
centered J(identity)=∫S(A,I)h(A) has expansion
  ∫w*h +∫h*Cross(identity), since ∫h=0 by PS.
Therefore C2=2*s_H EXACTLY under original finite spatial SU(2) Haar.

Together with the proved genuine second-moment quadratic b(B),
the ENTIRE physical fifth Ward residual has no quadratic spatial
counterterm and is
  R5(B)=D0+D1*w(B)−6*V2(B)
for exact original Haar scalars D0,D1, and true weighted two-crossing V2.
No conclusion about V2 or nonvanishing is postulated; no axiom/sorry.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY6C_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY6C_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY6C_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY6C_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY6C_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PY6C_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
  instFintypeProd (PeriodicHypercubicEvenSpatialSliceVertex H)
    PeriodicHypercubicEvenSpatialDirectionPair

namespace GroundStatePosteriorJoint
section ExactOriginalFifthQuadraticCancellation
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "s" => p4Q2PY_originalQuarticWardSlope H
local notation "C0" => p4Q2PY5_originalFifthSpatialConstant H
local notation "C1" => p4Q2PY5_originalFifthSpatialLinear H
local notation "C2" => p4Q2PY5_originalFifthSpatialQuadratic H
local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H
local notation "R5" => p4Q2PY_originalFifthWardResidual H
local notation "V2" => p4Q2PY5_originalWeightedTwoCrossingHaar H

/-- Original true centered Wilson J is exactly the sum of two
genuine weighted Haar terms, since ∫h=0 by the proven spatial Ward. -/
theorem p4Q2PY6_originalCenteredMixedHaar_atIdentity_split :
    p4Q2PS_originalCenteredMixedHaar H (fun _ => 1) =
      (∫ A : Cfg, w A * h A ∂haar) +
        (∫ A : Cfg, h A * Cross A (fun _ => 1) ∂haar) := by
  let I : Cfg := fun _ => 1
  have hw : Continuous (fun A : Cfg => w A) :=
    continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have hh : Continuous (fun A : Cfg => h A) := by
    have hEq : (fun A : Cfg => h A) =
        (fun A : Cfg =>
          (1 / 2 : ℝ) * p4Q2PW2_originalAllPlaquetteRealTrace H A) := by
      funext A
      exact p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A
    rw [hEq]
    exact continuous_const.mul
      (p4Q2PW2_originalAllPlaquetteRealTrace_continuous H)
  have hc : Continuous (fun A : Cfg => Cross A I) :=
    p4Q2PY6B_cross_continuous H I
  have hiW : Integrable (fun A : Cfg => w A * h A) haar :=
    (hw.mul hh).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiC : Integrable (fun A : Cfg => Cross A I * h A) haar :=
    (hc.mul hh).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiH : Integrable (fun A : Cfg => h A) haar :=
    hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAdd :
      (∫ A : Cfg, w A * h A + Cross A I * h A ∂haar) =
      (∫ A : Cfg, w A * h A ∂haar) +
        (∫ A : Cfg, Cross A I * h A ∂haar) := by
    simpa only [Pi.add_apply] using (integral_add hiW hiC)
  have hAddConst :
      (∫ A : Cfg,
        (w A * h A + Cross A I * h A) + w I * h A ∂haar) =
      (∫ A : Cfg, w A * h A + Cross A I * h A ∂haar) +
        w I * (∫ A : Cfg, h A ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul] using
      (integral_add (hiW.add hiC) (hiH.const_mul (w I)))
  calc
    p4Q2PS_originalCenteredMixedHaar H (fun _ => 1) =
        ∫ A : Cfg,
          (w A * h A + Cross A I * h A) + w I * h A ∂haar := by
      unfold p4Q2PS_originalCenteredMixedHaar
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PS_originalOneSlabAction_rightSplit H A I]
      unfold p4Q2PS_originalRightStrippedAction
      ring
    _ = (∫ A : Cfg, w A * h A ∂haar) +
          (∫ A : Cfg, Cross A I * h A ∂haar) +
          w I * (∫ A : Cfg, h A ∂haar) := by
      rw [hAddConst, hAdd]
    _ = (∫ A : Cfg, w A * h A ∂haar) +
          (∫ A : Cfg, h A * Cross A I ∂haar) := by
      rw [p4Q2PS_originalCenteredFirst_HaarMean_zero H]
      have hComm :
          (∫ A : Cfg, Cross A I * h A ∂haar) =
            (∫ A : Cfg, h A * Cross A I ∂haar) := by
        apply integral_congr_ae
        filter_upwards with A
        ring
      rw [hComm]
      ring

/-- The coefficient of w(B)^2 in the true fifth-Ward polynomial
equals exactly twice the PROVED physical fourth-Ward slope s_H.
No false nonzero constraint or arbitrary counterterm is inserted. -/
theorem p4Q2PY6_originalFifthSpatialQuadratic_eq_twiceWardSlope :
    C2 = 2 * s := by
  have hw : Continuous (fun A : Cfg => w A) :=
    continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have hh : Continuous (fun A : Cfg => h A) := by
    have hEq : (fun A : Cfg => h A) =
        (fun A : Cfg =>
          (1 / 2 : ℝ) * p4Q2PW2_originalAllPlaquetteRealTrace H A) := by
      funext A
      exact p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H A
    rw [hEq]
    exact continuous_const.mul
      (p4Q2PW2_originalAllPlaquetteRealTrace_continuous H)
  have hb : Continuous (fun A : Cfg => b A) :=
    p4Q2PT_originalSecondMoment_continuous H
  have hiB : Integrable (fun A : Cfg => b A) haar :=
    hb.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiWH : Integrable (fun A : Cfg => w A * h A) haar :=
    (hw.mul hh).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPhi :
      (∫ A : Cfg,
        p4Q2PY5_originalPureSpatialQuadraticWeight H A ∂haar) =
      6 * (∫ A : Cfg, b A ∂haar) -
        12 * (∫ A : Cfg, w A * h A ∂haar) := by
    change
      (∫ A : Cfg, 6 * b A - 12 * w A * h A ∂haar) = _
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub (hiB.const_mul 6) (hiWH.const_mul 12))
  have hJ := p4Q2PY6_originalCenteredMixedHaar_atIdentity_split H
  unfold p4Q2PY5_originalFifthSpatialQuadratic
    p4Q2PY_originalQuarticWardSlope
  rw [hPhi, hJ]
  ring

noncomputable def p4Q2PY6_originalReducedFifthConstant : ℝ :=
  C0 - 2 * s * θ

noncomputable def p4Q2PY6_originalReducedFifthLinear : ℝ :=
  C1 - 4 * s * α

local notation "D0" => p4Q2PY6_originalReducedFifthConstant H
local notation "D1" => p4Q2PY6_originalReducedFifthLinear H

/-- The true fifth Ward residual has NO remaining quadratic spatial
Wilson term. Only a spatial-affine scalar and the genuine weighted
two-crossing Haar profile survive. -/
theorem p4Q2PY6_originalFifthWardResidual_affinePlusTwoCrossing (B : Cfg) :
    R5 B = D0 + D1 * w B - 6 * V2 B := by
  have hC2 := p4Q2PY6_originalFifthSpatialQuadratic_eq_twiceWardSlope H
  have hB := p4Q2PY6_originalSecondActionMoment_quadratic H B
  rw [p4Q2PY5_originalFifthWardResidual_quadraticPlusTwoCrossing H B,
    hC2, hB]
  unfold p4Q2PY6_originalReducedFifthConstant
    p4Q2PY6_originalReducedFifthLinear
  ring

end ExactOriginalFifthQuadraticCancellation
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalCenteredMixedHaar_atIdentity_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalFifthSpatialQuadratic_eq_twiceWardSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY6_originalFifthWardResidual_affinePlusTwoCrossing
