import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDiagonalCubicBoundaryWardV5_PZ12
import Mathlib.Tactic

/-!
# P4-Q2-PZ13 — remove the true invariant cubic Haar sector of fifth Wilson moments

The genuine full one-slab Wilson action is
  S(X,B) = w(X) + Cross(X,B) + w(B).
Let h(X) = ∫w dHaar - w(X), the original centered SU(2) spatial
Wilson first moment. Binomial expansion of S^5 isolates exactly
  10 * h(X)^2 * Cross(X,B)^3
as a genuine action-moment term. PZ12 proves its Haar mean is
right-boundary invariant for all finite even periods (including H=0).

The rest is given by an explicit fifth-degree polynomial of the
UNCHANGED original Wilson spatial and temporal action components.
Hence the exact boundary differences of the genuine fifth one-slab
action moment depend ONLY on that residual, not the invariant term.

The two-slab fifth action moment is NOT independently factorized.
Its original middle spatial plaquette action must be retained.
No nonzero sixth coefficient, rank-three or mass-gap claim, new axiom,
sorry/admit, posterior substitution or spectral surrogate.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ13_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ13_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ13_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ13_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ13_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section OriginalFifthCubicWardResidual
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H
local notation "Phi" => p4Q2PW2_originalAllPlaquetteRealTrace H
local notation "m5" => p4Q2PZ1_originalOneSlabFifthActionMoment H

private theorem p4Q2PZ13_half_continuous :
    Continuous (fun X : Cfg => w X) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PZ13_centered_continuous :
    Continuous (fun X : Cfg => h X) := by
  have heq :
      (fun X : Cfg => h X) =
        (fun X : Cfg => (1 / 2 : ℝ) * Phi X) := by
    funext X
    exact p4Q2PW2_originalCenteredFirstMoment_eq_half_traceSum H X
  rw [heq]
  exact continuous_const.mul
    (p4Q2PW2_originalAllPlaquetteRealTrace_continuous H)

private theorem p4Q2PZ13_cross_continuous (B : Cfg) :
    Continuous (fun X : Cfg => Cross X B) := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have hCont := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
  simpa only [Function.comp_def] using hCont

private theorem p4Q2PZ13_slab_continuous (B : Cfg) :
    Continuous (fun X : Cfg => S X B) := by
  have hPair : Continuous (fun X : Cfg => (X, B)) :=
    continuous_id.prodMk continuous_const
  have hCont := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using hCont

/-- The ACTUAL centered squared Wilson / complete cubic crossing
Haar moment, already proved boundary-invariant in PZ12. -/
noncomputable def p4Q2PZ13_originalCenteredCubicHaar (B : Cfg) : ℝ :=
  ∫ X : Cfg, (h X)^2 * (Cross X B)^3 ∂haar

local notation "G3" => p4Q2PZ13_originalCenteredCubicHaar H

theorem p4Q2PZ13_originalCenteredCubicHaar_invariant (B : Cfg) :
    G3 B = G3 (fun _ => 1) :=
  p4Q2PZ12_originalCenteredSquare_fullCrossingCubeHaar_invariant H B

/-- Explicit original S^5 residual after the genuine cubic-centered
Haar term is extracted: r=w(X)+w(B), z=mean(w)+w(B), and
h(X)=mean(w)-w(X). All full Wilson terms remain literal. -/
noncomputable def p4Q2PZ13_originalOneSlabFifthResidualIntegrand
    (X B : Cfg) : ℝ :=
  let r : ℝ := w X + w B
  let z : ℝ := (∫ Y : Cfg, w Y ∂haar) + w B
  let c : ℝ := Cross X B
  r^5 + 5 * r^4 * c + 10 * r^3 * c^2 +
    10 * (z^2 - 2 * z * h X) * c^3 +
      5 * r * c^4 + c^5

local notation "R1" =>
  p4Q2PZ13_originalOneSlabFifthResidualIntegrand H

/-- ORIGINAL one-slab fifth-power identity, not a jet/surrogate:
the full action's degree-five cubic-centered sector has EXACT
factorial/binomial coefficient 10. -/
theorem p4Q2PZ13_originalOneSlabFifth_split (X B : Cfg) :
    (S X B)^5 = 10 * ((h X)^2 * (Cross X B)^3) + R1 X B := by
  rw [p4Q2PS_originalOneSlabAction_rightSplit H X B]
  change (w X + Cross X B + w B)^5 =
    10 * ((h X)^2 * (Cross X B)^3) + R1 X B
  unfold p4Q2PZ13_originalOneSlabFifthResidualIntegrand
  dsimp only
  rw [p4Q2PY6_originalCenteredFirst_eq_meanHalf_sub_half H X]
  ring

private theorem p4Q2PZ13_oneSlabResidual_continuous (B : Cfg) :
    Continuous (fun X : Cfg => R1 X B) := by
  have heq :
      (fun X : Cfg => R1 X B) =
        (fun X : Cfg =>
          (S X B)^5 - 10 * ((h X)^2 * (Cross X B)^3)) := by
    funext X
    have hp := p4Q2PZ13_originalOneSlabFifth_split H X B
    linear_combination -hp
  rw [heq]
  exact (p4Q2PZ13_slab_continuous H B).pow 5 |>.sub
    (continuous_const.mul
      (((p4Q2PZ13_centered_continuous H).pow 2).mul
        ((p4Q2PZ13_cross_continuous H B).pow 3)))

/-- The ORIGINAL one-slab fifth Haar action moment minus its
right-boundary-INVARIANT cubic Ward sector has this EXPLICIT
true-Wilson residual integral (no independent posterior). -/
noncomputable def p4Q2PZ13_originalOneSlabFifthResidual (B : Cfg) : ℝ :=
  ∫ X : Cfg, R1 X B ∂haar

local notation "r1" => p4Q2PZ13_originalOneSlabFifthResidual H

theorem p4Q2PZ13_originalOneSlabFifth_eq_WardPlusResidual (B : Cfg) :
    m5 B = 10 * G3 B + r1 B := by
  have hh : Continuous (fun X : Cfg => h X) :=
    p4Q2PZ13_centered_continuous H
  have hc : Continuous (fun X : Cfg => Cross X B) :=
    p4Q2PZ13_cross_continuous H B
  have hiWard :
      Integrable
        (fun X : Cfg => (10 : ℝ) * ((h X)^2 * (Cross X B)^3)) haar :=
    (continuous_const.mul ((hh.pow 2).mul (hc.pow 3))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiResidual : Integrable (fun X : Cfg => R1 X B) haar :=
    (p4Q2PZ13_oneSlabResidual_continuous H B).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    m5 B =
        ∫ X : Cfg,
          (10 : ℝ) * ((h X)^2 * (Cross X B)^3) + R1 X B ∂haar := by
      unfold p4Q2PZ1_originalOneSlabFifthActionMoment
      apply integral_congr_ae
      filter_upwards with X
      exact p4Q2PZ13_originalOneSlabFifth_split H X B
    _ = (10 : ℝ) * (∫ X : Cfg, (h X)^2 * (Cross X B)^3 ∂haar) +
        (∫ X : Cfg, R1 X B ∂haar) := by
      simpa only [Pi.add_apply, integral_const_mul] using
        (integral_add hiWard hiResidual)
    _ = 10 * G3 B + r1 B := rfl

/-- The PZ12 genuine cubic Ward sector vanishes from ALL boundary
differences of the ACTUAL fifth one-slab Wilson moment. -/
theorem p4Q2PZ13_originalOneSlabFifth_difference_residual
    (A B : Cfg) :
    m5 B - m5 A = r1 B - r1 A := by
  rw [p4Q2PZ13_originalOneSlabFifth_eq_WardPlusResidual H B,
    p4Q2PZ13_originalOneSlabFifth_eq_WardPlusResidual H A,
    p4Q2PZ13_originalCenteredCubicHaar_invariant H B,
    p4Q2PZ13_originalCenteredCubicHaar_invariant H A]
  ring


/-- Exact physical sixth Wilson coefficient with the PZ12-invariant
ONE-slab cubic Ward term removed. The true two-slab fifth moment
is UNCHANGED: its additional invariant sector remains to be
separated in the next stage. -/
theorem p4Q2PZ13_originalSixthCoefficient_oneSlabResidual
    (A B C : Cfg) :
    p4Q2PZ1_originalSixthFifthJetCoefficient H A B C =
      p4Q2PX_originalSixthFourthJetCoefficient H A B C -
        ((p4Q2PK_originalOneSlabFirstActionMoment H B -
            p4Q2PK_originalOneSlabFirstActionMoment H A) *
          ((p4Q2PZ1_originalTwoSlabFifthActionMoment H C -
              p4Q2PZ1_originalTwoSlabFifthActionMoment H A) -
            (r1 C - r1 A)) -
         (p4Q2PK_originalOneSlabFirstActionMoment H C -
            p4Q2PK_originalOneSlabFirstActionMoment H A) *
          ((p4Q2PZ1_originalTwoSlabFifthActionMoment H B -
              p4Q2PZ1_originalTwoSlabFifthActionMoment H A) -
            (r1 B - r1 A))) / 120 := by
  unfold p4Q2PZ1_originalSixthFifthJetCoefficient
  rw [p4Q2PZ13_originalOneSlabFifth_difference_residual H A C,
      p4Q2PZ13_originalOneSlabFifth_difference_residual H A B]

/-- Transport the exact one-slab cubic-Haar Ward cancellation into
the GENUINE sixth obstruction W6=720D6. No universal W6 vanishing
or nonvanishing follows without further two-slab Haar analysis. -/
theorem p4Q2PZ13_originalSixthWard_oneSlabResidual
    (A B C : Cfg) :
    p4Q2PZ8_originalSixthWardObstruction H A B C =
      720 * (p4Q2PX_originalSixthFourthJetCoefficient H A B C -
        ((p4Q2PK_originalOneSlabFirstActionMoment H B -
            p4Q2PK_originalOneSlabFirstActionMoment H A) *
          ((p4Q2PZ1_originalTwoSlabFifthActionMoment H C -
              p4Q2PZ1_originalTwoSlabFifthActionMoment H A) -
            (r1 C - r1 A)) -
         (p4Q2PK_originalOneSlabFirstActionMoment H C -
            p4Q2PK_originalOneSlabFirstActionMoment H A) *
          ((p4Q2PZ1_originalTwoSlabFifthActionMoment H B -
              p4Q2PZ1_originalTwoSlabFifthActionMoment H A) -
            (r1 B - r1 A))) / 120) := by
  rw [p4Q2PZ8_sixthWard_eq_correctedCoefficient H A B C,
    p4Q2PZ13_originalSixthCoefficient_oneSlabResidual H A B C]

end OriginalFifthCubicWardResidual
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ13_originalCenteredCubicHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ13_originalOneSlabFifth_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ13_originalOneSlabFifth_eq_WardPlusResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ13_originalOneSlabFifth_difference_residual

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ13_originalSixthCoefficient_oneSlabResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ13_originalSixthWard_oneSlabResidual
