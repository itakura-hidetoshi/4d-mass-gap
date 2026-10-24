import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalStrippedQuarticHaarWardV5_PZ20
import Mathlib.Tactic

/-!
# P4-Q2-PZ21 — exact cancellation of the ORIGINAL fifth Haar boundary responses

The PZ20 fully selected ORIGINAL Wilson left Haar fourth-polarization
kernel is separated without any modification of either Wilson action:

 (t-u) K20(A;t,u) =
   (t^5-u^5) + R(A,t)-R(A,u)

 R(A,t) = 5 M4(A)t + 10 M3(A)t² + 10 M2(A)t³ + 5 M1(A)t⁴,

where all four M1..M4 are the original single-slab Haar moments,
already proved in PZ17–PZ20 to be spatial Wilson polynomials with
authentic SU(2) Haar constants.

The term t^5-u^5, after the original OUTER Haar integration over
the interacting intermediate spatial configuration A, is EXACTLY
the original one-slab fifth boundary response J1(B,C). Therefore
the subtraction T20(B,C)-J1(B,C) eliminates all fifth-power
right-boundary terms, leaving the genuine physical mixed-potential
boundary difference

 V(B)-V(C),  V(B)= integral_A R(A,S(A,B)) dHaar(A).

This is NOT an independent-posterior factorization. The genuine
spatial Wilson action at the intermediate slice A remains in every
M_k(A) and S(A,B), and the original Haar and Gauss-law model are
unchanged. The six-Ward obstruction W6 is reduced to the original
fourth jet C6 plus the mixed physical two-boundary determinant.
No W6 zero/nonzero witness, mass gap, new axiom, sorry/admit,
Dobrushin shortcut, or replacement spectrum is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ21_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ21_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ21_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ21_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ21_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ21_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalFifthHaarCancellation

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "M" => p4Q2PZ16_originalLeftSlabMoment H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "α" => p4Q2PY6_originalSecondActionLinearScalar H
local notation "θ" => p4Q2PY6_originalSecondActionConstant H
local notation "η3" => p4Q2PZ19_originalStrippedCubicHaarConstant H
local notation "η4" => p4Q2PZ20_originalStrippedFourthHaarConstant H
local notation "K20" => p4Q2PZ20_originalFullySelectedFourthKernel H
local notation "T20" => p4Q2PZ20_originalTwoSlabFullySelectedHaarResponse H
local notation "J1" => p4Q2PZ15_originalOneSlabFifthBoundaryResponse H
local notation "J2" => p4Q2PZ15_originalTwoSlabFifthBoundaryResponse H
local notation "G" => p4Q2PZ15_originalWardResidualResponseGap H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "C6" => p4Q2PX_originalSixthFourthJetCoefficient H
local notation "W6" => p4Q2PZ8_originalSixthWardObstruction H

/-- ORIGINAL mixed fifth-boundary polynomial with the genuine left
Haar moments M1..M4. It is NOT a physical posterior replacement. -/
noncomputable def p4Q2PZ21_originalMixedMomentPolynomial
    (A : Cfg) (t : ℝ) : ℝ :=
  5 * M 4 A * t +
    10 * M 3 A * t^2 +
      10 * M 2 A * t^3 +
        5 * M 1 A * t^4

local notation "R" => p4Q2PZ21_originalMixedMomentPolynomial H

/-- Algebraic fifth-response cancellation at EACH genuine middle
slice, after the exact PZ20 physical left-Haar selection. -/
theorem p4Q2PZ21_originalSelectedFifthBoundary_factor
    (A : Cfg) (t u : ℝ) :
    (t-u) * K20 A t u =
      (t^5-u^5) + (R A t-R A u) := by
  rw [← p4Q2PZ20_originalConditionalTower_fullyHaarSelected H A t u]
  unfold p4Q2PZ16_originalConditionalFourthTower
    p4Q2PZ21_originalMixedMomentPolynomial
    p4Q2PZ15_originalFourthPolarization
  ring

/-- The genuine mixed-kernel polynomial now has NO unselected
conditional Haar coefficient. Each coefficient is an exact original
spatial Wilson polynomial proved in PZ17–PZ20. -/
theorem p4Q2PZ21_originalMixedPolynomial_spatialWilson
    (A : Cfg) (t : ℝ) :
    R A t =
      5*(w A^4 + 4*α*w A^3 + 6*θ*w A^2 +
          4*η3*w A + η4)*t +
      10*(w A^3 + 3*α*w A^2 + 3*θ*w A + η3)*t^2 +
      10*(w A^2 + 2*α*w A + θ)*t^3 +
      5*(w A + α)*t^4 := by
  unfold p4Q2PZ21_originalMixedMomentPolynomial
  rw [p4Q2PZ20_originalCompleteFourth_quarticSpatial H A,
    p4Q2PZ19_originalCompleteThird_cubicSpatial H A,
    p4Q2PZ17_originalSecondMoment_quadratic H A,
    p4Q2PZ18_originalCompleteFirst_eq_halfPlusAlpha H A]
  ring

/-- Original SU(2) Haar conditional moment M_k is continuous in
its actual right spatial configuration; no independence assumption. -/
private theorem p4Q2PZ21_leftMoment_continuous (k : ℕ) :
    Continuous (fun A : Cfg => M k A) := by
  let f : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2)^k),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow k⟩
  let v : C(Cfg, C(Cfg, ℝ)) := f.curry
  have hv : Integrable (fun X : Cfg => v X) haar :=
    v.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun :
      (fun A : Cfg => ∫ X : Cfg, f (X,A) ∂haar) =
        (fun A : Cfg => (∫ X : Cfg, v X ∂haar) A) := by
    funext A
    rw [ContinuousMap.integral_apply hv A]
    rfl
  unfold p4Q2PZ16_originalLeftSlabMoment
  change Continuous (fun A : Cfg => ∫ X : Cfg, f (X,A) ∂haar)
  rw [hfun]
  exact (∫ X : Cfg, v X ∂haar).continuous

private theorem p4Q2PZ21_slab_row_continuous (B : Cfg) :
    Continuous (fun A : Cfg => S A B) := by
  have hp : Continuous (fun A : Cfg => (A,B)) :=
    continuous_id.prodMk continuous_const
  have hc := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hp
  simpa only [Function.comp_def] using hc

/-- The physical mixed moment polynomial stays continuous in the
actual interacting intermediate slice, including its Wilson plaquettes. -/
private theorem p4Q2PZ21_mixed_row_continuous (B : Cfg) :
    Continuous (fun A : Cfg => R A (S A B)) := by
  have hs := p4Q2PZ21_slab_row_continuous H B
  have h1 := p4Q2PZ21_leftMoment_continuous H 1
  have h2 := p4Q2PZ21_leftMoment_continuous H 2
  have h3 := p4Q2PZ21_leftMoment_continuous H 3
  have h4 := p4Q2PZ21_leftMoment_continuous H 4
  have hc4 : Continuous (fun A : Cfg => 5*M 4 A*S A B) :=
    (continuous_const.mul h4).mul hs
  have hc3 : Continuous (fun A : Cfg => 10*M 3 A*(S A B)^2) :=
    (continuous_const.mul h3).mul (hs.pow 2)
  have hc2 : Continuous (fun A : Cfg => 10*M 2 A*(S A B)^3) :=
    (continuous_const.mul h2).mul (hs.pow 3)
  have hc1 : Continuous (fun A : Cfg => 5*M 1 A*(S A B)^4) :=
    (continuous_const.mul h1).mul (hs.pow 4)
  unfold p4Q2PZ21_originalMixedMomentPolynomial
  exact ((hc4.add hc3).add hc2).add hc1

/-- Only the original OUTER Haar integration survives in the mixed
boundary potential, evaluated on the complete actual action S(A,B). -/
noncomputable def p4Q2PZ21_originalMixedFifthBoundaryPotential
    (B : Cfg) : ℝ :=
  ∫ A : Cfg, R A (S A B) ∂haar

local notation "V" => p4Q2PZ21_originalMixedFifthBoundaryPotential H

/-- The original PZ20 two-slab fifth response is precisely the
UNCHANGED original one-slab fifth response PLUS a genuine mixed
boundary-potential difference. The fifth raw right-boundary powers
cancel algebraically, not by altering the posterior or action. -/
theorem p4Q2PZ21_originalTwoSlabResponse_oneSlabPlusMixed
    (B C : Cfg) :
    T20 B C = J1 B C + (V B - V C) := by
  have hiS (D : Cfg) :
      Integrable (fun A : Cfg => (S A D)^5) haar :=
    ((p4Q2PZ21_slab_row_continuous H D).pow 5).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiR (D : Cfg) :
      Integrable (fun A : Cfg => R A (S A D)) haar :=
    (p4Q2PZ21_mixed_row_continuous H D).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hOne :
      (∫ A : Cfg, (S A B)^5-(S A C)^5 ∂haar) = J1 B C := by
    rw [integral_sub (hiS B) (hiS C)]
    exact p4Q2PZ15_originalOneSlabFifth_difference_response H B C
  calc
    T20 B C =
      ∫ A : Cfg, ((S A B)^5-(S A C)^5) +
        (R A (S A B)-R A (S A C)) ∂haar := by
      unfold p4Q2PZ20_originalTwoSlabFullySelectedHaarResponse
      apply integral_congr_ae
      filter_upwards with A
      exact p4Q2PZ21_originalSelectedFifthBoundary_factor H A (S A B) (S A C)
    _ = (∫ A : Cfg, (S A B)^5-(S A C)^5 ∂haar) +
        (∫ A : Cfg, R A (S A B)-R A (S A C) ∂haar) := by
      simpa only [Pi.add_apply] using
        (integral_add ((hiS B).sub (hiS C)) ((hiR B).sub (hiR C)))
    _ = J1 B C + (V B - V C) := by
      rw [hOne, integral_sub (hiR B) (hiR C)]
      rfl

/-- The entire physical fifth response GAP is just the difference
of the original SU(2) mixed potential; the original J1 cancels. -/
theorem p4Q2PZ21_originalResponseGap_eq_mixedPotential
    (B C : Cfg) :
    G B C = V B - V C := by
  unfold p4Q2PZ15_originalWardResidualResponseGap
  rw [p4Q2PZ16_originalTwoSlabResponse_eq_tower H B C,
      p4Q2PZ20_originalTwoSlabResponse_fullyHaarSelected H B C,
      p4Q2PZ21_originalTwoSlabResponse_oneSlabPlusMixed H B C]
  ring

/-- True PZ13/PZ14 fifth Ward residual gap eliminates both original
one/two-slab fifth raw boundary responses, leaving V(B)-V(C). -/
theorem p4Q2PZ21_originalFifthResidualGap_mixedPotential
    (B C : Cfg) :
    (p4Q2PZ14_originalTwoSlabFifthResidual H B -
        p4Q2PZ13_originalOneSlabFifthResidual H B) -
      (p4Q2PZ14_originalTwoSlabFifthResidual H C -
        p4Q2PZ13_originalOneSlabFifthResidual H C) =
      V B - V C := by
  rw [p4Q2PZ15_originalResidualGap_boundaryResponse H B C,
    p4Q2PZ21_originalResponseGap_eq_mixedPotential H B C]

/-- Original SU(2) sixth Wilson Ward obstruction in the genuine
mixed Haar fifth potential V, with the 720*C6 fourth jet unchanged. -/
theorem p4Q2PZ21_originalSixthWard_mixedPotential
    (A B C : Cfg) :
    W6 A B C =
      720*C6 A B C -
      6*((a B-a A)*(V C-V A) -
         (a C-a A)*(V B-V A)) := by
  rw [p4Q2PZ20_originalSixthWard_fullyHaarSelected H A B C,
    p4Q2PZ21_originalTwoSlabResponse_oneSlabPlusMixed H C A,
    p4Q2PZ21_originalTwoSlabResponse_oneSlabPlusMixed H B A]
  ring

/-- A concrete necessary and sufficient physical mixed-Haar balance
for cancellation of W6. No vanishing or nonvanishing is assumed. -/
theorem p4Q2PZ21_originalSixthWard_zero_iff_mixedBalance
    (A B C : Cfg) :
    W6 A B C = 0 ↔
      120*C6 A B C =
        (a B-a A)*(V C-V A) -
          (a C-a A)*(V B-V A) := by
  rw [p4Q2PZ21_originalSixthWard_mixedPotential H A B C]
  constructor <;> intro hh <;> nlinarith

/-- A strict inequality of ACTUAL finite-volume Haar expressions
suffices for a positive W6, without declaring a nonzero witness. -/
theorem p4Q2PZ21_originalSixthWard_positive_of_strictMixed
    (A B C : Cfg)
    (hStrict :
      (a B-a A)*(V C-V A) -
        (a C-a A)*(V B-V A) < 120*C6 A B C) :
    0 < W6 A B C := by
  rw [p4Q2PZ21_originalSixthWard_mixedPotential H A B C]
  nlinarith

/-- A genuine strict mixed-Haar witness, if constructed, transfers
to a NONZERO original interacting Wilson minor for all sufficiently
small positive physical coupling via PZ8 (not a mass-gap claim). -/
theorem p4Q2PZ21_originalLiteralMinor_of_strictMixed
    (A B C : Cfg)
    (hStrict :
      (a B-a A)*(V C-V A) -
        (a C-a A)*(V B-V A) < 120*C6 A B C) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ beta : ℝ, 0 < beta → beta < delta →
        p4Q2PJ_originalWilsonLiteralThreeSpatialMinor H beta A B C ≠ 0 := by
  have hW : W6 A B C ≠ 0 :=
    ne_of_gt (p4Q2PZ21_originalSixthWard_positive_of_strictMixed
      H A B C hStrict)
  exact p4Q2PZ8_originalLiteralMinor_smallPositive_nonzero_of_Ward
    H A B C hW

end OriginalFifthHaarCancellation
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ21_originalSelectedFifthBoundary_factor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ21_originalMixedPolynomial_spatialWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ21_originalTwoSlabResponse_oneSlabPlusMixed
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ21_originalResponseGap_eq_mixedPotential
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ21_originalFifthResidualGap_mixedPotential
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ21_originalSixthWard_mixedPotential
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ21_originalSixthWard_zero_iff_mixedBalance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ21_originalSixthWard_positive_of_strictMixed
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ21_originalLiteralMinor_of_strictMixed
