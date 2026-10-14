import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointPosteriorHalfDensityDescentV5_GQ
import Mathlib.Tactic

/-!
# P4-Q2-GR: exact original physical signed receiver / posterior square-root bridge

GN proved the original Wilson physical signed FF right-link response,
including its full right-update drift, as
 R_f((A,B),g)=L[t_f(B) - s(A,B)/s(A,B_g) * t_f(B_g)].

GQ proves the *actual* continuous physical joint density rho and the
*actual* interacting Wilson posterior density p have proportional
right-link fibers. The physical positive half-density s = sqrt rho
therefore obeys
  s(A,B)/s(A,B_g) = sqrt(p_A(B(e)))/sqrt(p_A(g)).

The original signed response thus becomes
 R_f((A,B),g)=L[t_f(B) -
   sqrt(p_A(B(e)))/sqrt(p_A(g)) * t_f(B_g)].
No Wilson factor, actual physical transfer output, or joint-density
normalization is dropped.

In the two genuine left boundary rows A0=identity, A1=SU2 pi rotation,
the common t_f(B) cancels POINTWISE. The remaining difference has
exactly the same original physical source transfer t_f(B_g) multiplied
by a square-root posterior-row ratio contrast.

This provides an exact direct connection of GQ to the original
GN/FF signed receiver, but is NOT yet the integrated GI two-Wilson
posterior expectation-gap positivity, signed-source injectivity,
volume-uniform source frame, C1/C2/C3 or a continuum Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1700000
set_option synthInstance.maxHeartbeats 720000

local instance p4Q2GR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Frozen

variable (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "s" => continuousJointSqrtDensity H 2 (by norm_num) beta hbeta
local notation "rho" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumJointNormalizedWeight
    H 2 (by norm_num) beta hbeta
local notation "posterior" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
    H 2 (by norm_num) beta hbeta
local notation "L" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta‖⁻¹

/-- The canonical continuous joint square-root used in the ACTUAL
normalized physical GN receiver equals the pointwise square root of
the true positive continuous ground-state Wilson joint density of GQ. -/
theorem p4Q2GR_actualContinuousJointSqrt_eq_sqrt_originalJoint
    (z : Cfg × Cfg) :
    s z = Real.sqrt (rho z) := by
  rfl

/-- The exact original signed physical half-density update factor is
the square-root ratio of the ORIGINAL interacting Wilson conditional
posterior density, with its left physical boundary retained. -/
theorem p4Q2GR_originalPhysicalJointSqrtRatio_eq_posteriorSqrtRatio
    (left right : Cfg) (e : Link) (g : Gauge) :
    s (left, right) / s (left, Function.update right e g) =
      Real.sqrt (posterior left right e (right e)) /
        Real.sqrt (posterior left right e g) := by
  have hsUpdate :
      s (left, Function.update right e g) ≠ 0 :=
    (continuousJointSqrtDensity_pos H 2 (by norm_num) beta hbeta
      (left, Function.update right e g)).ne'
  have hpUpdate :
      Real.sqrt (posterior left right e g) ≠ 0 :=
    (Real.sqrt_pos.mpr
      (p4Q2GQ_originalPosteriorDensity_pos H beta hbeta left right e g)).ne'
  have hCross :=
    p4Q2GQ_originalJointPosteriorFiber_sqrt_cross
      H beta hbeta left right e (right e) g
  have hPhysical :
      s (left, right) * Real.sqrt (posterior left right e g) =
        s (left, Function.update right e g) *
          Real.sqrt (posterior left right e (right e)) := by
    simpa only [p4Q2GR_actualContinuousJointSqrt_eq_sqrt_originalJoint,
      Function.update_same] using hCross
  apply (div_eq_div_iff hsUpdate hpUpdate).2
  simpa only [mul_comm] using hPhysical

/-- ORIGINAL signed FF/GN physical source response expressed using
its true frozen Wilson posterior square-root ratio at a fixed left
boundary. The actual source-smoothing t_f is not replaced by a free
function and the full update drift is preserved. -/
theorem p4Q2GR_originalSignedPhysicalResponse_eq_posteriorSqrtRatio
    (f : Phys) (e : Link) (z : Cfg × Cfg) (g : Gauge) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e (z,g) =
      L * (decomposableOneSliceTransferIntegral H 2 beta f z.2 -
        (Real.sqrt (posterior z.1 z.2 e (z.2 e)) /
          Real.sqrt (posterior z.1 z.2 e g)) *
          decomposableOneSliceTransferIntegral H 2 beta f
            (Function.update z.2 e g)) := by
  rw [p4Q2GN_originalSignedResponse_eq_transferDifference]
  rw [p4Q2GR_originalPhysicalJointSqrtRatio_eq_posteriorSqrtRatio]

/-- For the SAME genuine signed physical source f and the SAME right
insertion g, compare the two ACTUAL left boundary rows. Their common
original transfer output t_f(B) cancels exactly. Only the true Wilson
conditional posterior square-root row ratios distinguish the responses. -/
theorem p4Q2GR_originalTwoBoundarySignedPhysicalResponse_difference
    (f : Phys) (e : Link) (right : Cfg) (g : Gauge) :
    p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e
        ((originalWilsonExplicitIdentityBoundary H, right),g) -
      p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) beta hbeta f e
        ((p4Q2FQ_originalSU2LeftPiRotationAtLink H e, right),g) =
      L * decomposableOneSliceTransferIntegral H 2 beta f
        (Function.update right e g) *
      ((Real.sqrt
          (posterior (p4Q2FQ_originalSU2LeftPiRotationAtLink H e)
            right e (right e)) /
          Real.sqrt
            (posterior (p4Q2FQ_originalSU2LeftPiRotationAtLink H e)
              right e g)) -
        (Real.sqrt
          (posterior (originalWilsonExplicitIdentityBoundary H)
            right e (right e)) /
          Real.sqrt
            (posterior (originalWilsonExplicitIdentityBoundary H)
              right e g))) := by
  rw [p4Q2GR_originalSignedPhysicalResponse_eq_posteriorSqrtRatio,
    p4Q2GR_originalSignedPhysicalResponse_eq_posteriorSqrtRatio]
  ring

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GR_actualContinuousJointSqrt_eq_sqrt_originalJoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GR_originalPhysicalJointSqrtRatio_eq_posteriorSqrtRatio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GR_originalSignedPhysicalResponse_eq_posteriorSqrtRatio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GR_originalTwoBoundarySignedPhysicalResponse_difference
