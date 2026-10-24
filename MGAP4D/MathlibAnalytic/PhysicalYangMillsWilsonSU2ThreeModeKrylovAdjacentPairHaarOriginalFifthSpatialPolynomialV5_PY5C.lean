import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthTwoCrossingCoreV5_PY5B
import Mathlib.Tactic

/-!
# P4-Q2-PY5C — exact quadratic spatial polynomial of the true fifth Ward residual

PY5B reduces the genuine original SU(2) fifth Ward residual to
the original zero-crossing Haar polynomial and a single true
two-crossing profile V2(B)=∫k(A)Cross(A,B)^2 dHaar(A).

Since h(A)=a(A)-mean(a) is EXACTLY Haar-centered by PS,
the zero-crossing spatial polynomial in w(B)=W(B)/2 has NO
cubic term after original Haar integration. Hence the full
fifth residual is precisely
  R5(B)=C0+C1*w(B)+C2*w(B)^2-6*V2(B)-2*s_H*b(B)
with TRUE spatial SU(2) Haar constants C0,C1,C2.

No claim that V2 is affine, quadratic, zero, or nonzero is
introduced, and the full original Wilson middle spatial
plaquette action remains present throughout.
No new axiom, sorry/admit, independent posterior, Dobrushin or
invented spectrum.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY5C_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY5C_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY5C_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY5C_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY5C_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalFifthSpatialQuadratic
variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "u" => p4Q2PX_originalOneSlabFourthActionMoment H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "k" => p4Q2PT_originalSingleCrossingWardWeight H
local notation "f5" => p4Q2PY5_originalHigherSingleCrossingWardWeight H
local notation "s" => p4Q2PY_originalQuarticWardSlope H
local notation "R5" => p4Q2PY_originalFifthWardResidual H
local notation "V2" => p4Q2PY5_originalWeightedTwoCrossingHaar H

noncomputable def p4Q2PY5_originalPureSpatialConstantWeight (A : Cfg) : ℝ :=
  -4 * w A * c A + 6 * (w A)^2 * b A - 4 * (w A)^3 * h A

noncomputable def p4Q2PY5_originalPureSpatialLinearWeight (A : Cfg) : ℝ :=
  -4 * c A + 12 * w A * b A - 12 * (w A)^2 * h A

noncomputable def p4Q2PY5_originalPureSpatialQuadraticWeight (A : Cfg) : ℝ :=
  6 * b A - 12 * w A * h A

local notation "φ0" => p4Q2PY5_originalPureSpatialConstantWeight H
local notation "φ1" => p4Q2PY5_originalPureSpatialLinearWeight H
local notation "φ2" => p4Q2PY5_originalPureSpatialQuadraticWeight H

/-- The pure-spatial Haar sector is an exact DEGREE-TWO
polynomial in the true right Wilson half-action w(B), because
the original first action moment has zero centered Haar mean. -/
theorem p4Q2PY5_originalPureSpatialFifthProfile_quadratic
    (B : Cfg) :
    p4Q2PY5_originalPureSpatialFifthProfile H B =
      (∫ A : Cfg, φ0 A ∂haar) +
        w B * (∫ A : Cfg, φ1 A ∂haar) +
          (w B)^2 * (∫ A : Cfg, φ2 A ∂haar) := by
  have hw : Continuous (fun A : Cfg => w A) :=
    continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have ha : Continuous (fun A : Cfg => a A) := by
    have heq : (fun A : Cfg => a A) =
        fun A : Cfg => -(1 / 2 : ℝ) * W A -
          p4Q2JE_originalWilsonHaarZeroDerivativeConstant H := by
      funext A
      exact p4Q2PM_originalFirstMoment_spatialWilson H A
    rw [heq]
    exact (continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous
        H 2)).sub continuous_const
  have hh : Continuous (fun A : Cfg => h A) := by
    change Continuous (fun A : Cfg =>
      a A - p4Q2PQ_originalFirstActionMean H)
    exact ha.sub continuous_const
  have hb := p4Q2PT_originalSecondMoment_continuous H
  have hc := p4Q2PY5_originalThirdMoment_continuous H
  have hφ0 : Continuous (fun A : Cfg => φ0 A) := by
    change Continuous (fun A : Cfg =>
      -4 * w A * c A + 6 * (w A)^2 * b A - 4 * (w A)^3 * h A)
    exact
      (((continuous_const.mul hw).mul hc).add
        ((continuous_const.mul (hw.pow 2)).mul hb)).sub
        ((continuous_const.mul (hw.pow 3)).mul hh)
  have hφ1 : Continuous (fun A : Cfg => φ1 A) := by
    change Continuous (fun A : Cfg =>
      -4 * c A + 12 * w A * b A - 12 * (w A)^2 * h A)
    exact
      ((continuous_const.mul hc).add
        ((continuous_const.mul hw).mul hb)).sub
        ((continuous_const.mul (hw.pow 2)).mul hh)
  have hφ2 : Continuous (fun A : Cfg => φ2 A) := by
    change Continuous (fun A : Cfg =>
      6 * b A - 12 * w A * h A)
    exact (continuous_const.mul hb).sub
      ((continuous_const.mul hw).mul hh)
  have hi0 : Integrable (fun A : Cfg => φ0 A) haar :=
    hφ0.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi1 : Integrable (fun A : Cfg => φ1 A) haar :=
    hφ1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun A : Cfg => φ2 A) haar :=
    hφ2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hih : Integrable (fun A : Cfg => h A) haar :=
    hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi01 : Integrable (fun A : Cfg =>
      φ0 A + w B * φ1 A) haar :=
    hi0.add (hi1.const_mul (w B))
  have hi012 : Integrable (fun A : Cfg =>
      (φ0 A + w B * φ1 A) + (w B)^2 * φ2 A) haar :=
    hi01.add (hi2.const_mul ((w B)^2))
  have hAdd01 :
      (∫ A : Cfg, φ0 A + w B * φ1 A ∂haar) =
      (∫ A : Cfg, φ0 A ∂haar) +
        w B * (∫ A : Cfg, φ1 A ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul] using
      (integral_add hi0 (hi1.const_mul (w B)))
  have hAdd012 :
      (∫ A : Cfg, (φ0 A + w B * φ1 A) +
        (w B)^2 * φ2 A ∂haar) =
      (∫ A : Cfg, φ0 A + w B * φ1 A ∂haar) +
        (w B)^2 * (∫ A : Cfg, φ2 A ∂haar) := by
    simpa only [Pi.add_apply, integral_const_mul] using
      (integral_add hi01 (hi2.const_mul ((w B)^2)))
  have hSub :
      (∫ A : Cfg, (φ0 A + w B * φ1 A) +
        (w B)^2 * φ2 A - (4 * (w B)^3) * h A ∂haar) =
      (∫ A : Cfg, (φ0 A + w B * φ1 A) +
        (w B)^2 * φ2 A ∂haar) -
        (4 * (w B)^3) * (∫ A : Cfg, h A ∂haar) := by
    simpa only [Pi.sub_apply, integral_const_mul] using
      (integral_sub hi012 (hih.const_mul (4 * (w B)^3)))
  have hPoint (A : Cfg) :
      -4 * (w A + w B) * c A +
        6 * (w A + w B)^2 * b A -
          4 * (w A + w B)^3 * h A =
      (φ0 A + w B * φ1 A) + (w B)^2 * φ2 A -
        (4 * (w B)^3) * h A := by
    unfold p4Q2PY5_originalPureSpatialConstantWeight
      p4Q2PY5_originalPureSpatialLinearWeight
      p4Q2PY5_originalPureSpatialQuadraticWeight
    ring
  calc
    p4Q2PY5_originalPureSpatialFifthProfile H B =
        ∫ A : Cfg,
          (φ0 A + w B * φ1 A) + (w B)^2 * φ2 A -
            (4 * (w B)^3) * h A ∂haar := by
      unfold p4Q2PY5_originalPureSpatialFifthProfile
      apply integral_congr_ae
      filter_upwards with A
      exact hPoint A
    _ = ((∫ A : Cfg, φ0 A ∂haar) +
          w B * (∫ A : Cfg, φ1 A ∂haar)) +
          (w B)^2 * (∫ A : Cfg, φ2 A ∂haar) -
            (4 * (w B)^3) * (∫ A : Cfg, h A ∂haar) := by
      rw [hSub, hAdd012, hAdd01]
      ring
    _ = _ := by
      rw [p4Q2PS_originalCenteredFirst_HaarMean_zero H]
      ring

/-- Exact original spatial SU(2) Haar scalar coefficients. -/
noncomputable def p4Q2PY5_originalFifthSpatialConstant : ℝ :=
  (∫ A : Cfg, u A ∂haar) +
    (∫ A : Cfg, φ0 A ∂haar) -
      4 * (∫ A : Cfg, f5 A * Cross A (fun _ => 1) ∂haar)

noncomputable def p4Q2PY5_originalFifthSpatialLinear : ℝ :=
  (∫ A : Cfg, φ1 A ∂haar) -
    12 * (∫ A : Cfg, k A * Cross A (fun _ => 1) ∂haar)

noncomputable def p4Q2PY5_originalFifthSpatialQuadratic : ℝ :=
  (∫ A : Cfg, φ2 A ∂haar) -
    12 * (∫ A : Cfg, h A * Cross A (fun _ => 1) ∂haar)

local notation "C0" => p4Q2PY5_originalFifthSpatialConstant H
local notation "C1" => p4Q2PY5_originalFifthSpatialLinear H
local notation "C2" => p4Q2PY5_originalFifthSpatialQuadratic H

/-- Every remaining full SU(2) fifth Ward term is either a degree-two
polynomial in the original right Wilson spatial energy, the actual
one-slab second moment b(B), or the sole weighted two-crossing Haar V2. -/
theorem p4Q2PY5_originalFifthWardResidual_quadraticPlusTwoCrossing
    (B : Cfg) :
    R5 B =
      C0 + C1 * w B + C2 * (w B)^2 -
        6 * V2 B - 2 * s * b B := by
  rw [p4Q2PY5_originalFifthWardResidual_twoCrossingReduced H B,
    p4Q2PY5_originalPureSpatialFifthProfile_quadratic H B]
  unfold p4Q2PY5_originalFifthSpatialConstant
    p4Q2PY5_originalFifthSpatialLinear
    p4Q2PY5_originalFifthSpatialQuadratic
  ring

end OriginalFifthSpatialQuadratic
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalPureSpatialFifthProfile_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalFifthWardResidual_quadraticPlusTwoCrossing
