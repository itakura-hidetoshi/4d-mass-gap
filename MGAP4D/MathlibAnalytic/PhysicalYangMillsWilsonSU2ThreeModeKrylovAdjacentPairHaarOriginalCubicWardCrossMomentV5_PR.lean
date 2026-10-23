import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourthWitnessSmallFineV5_PQ2
import Mathlib.Tactic

/-!
# P4-Q2-PR — exact cubic Haar reduction of the ORIGINAL Wilson Ward residual

The original complete two-slab action is Q(X,A,B) = S(X,A) + S(A,B).
Expand Q^3 *before* either genuine spatial Haar integration. The
inner Haar integral is a cubic polynomial in the unchanged one-slab
action moments a(A), b(A), c(A). The outer Haar integration gives

  g(B) - c(B) =
      mean_H(c) - 3 * integral_H [S(A,B) * b(A)]
                + 3 * integral_H [S(A,B)^2 * a(A)].

Thus PQ's exact fourth-order Ward obstruction is the sum of a constant,
a centered second-cross-slab action moment and a second-moment-weighted
first-cross-slab action moment:

  R_H(B) =
      mean_H(c)
      + 3 * integral_H [S(A,B)^2 * (a(A) - mean_H(a))]
      - 3 * integral_H [S(A,B) * b(A)].

Every integral is the original finite-volume SU(2) spatial Haar; the
intermediate spatial Wilson plaquette action is fully present in S.
These are identities, NOT a non-affinity or nonzero-C4 assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalWilsonCubicHaar
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Q" => p4Q2PK_originalTwoSlabAction H
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "g" => p4Q2PP2_originalTwoSlabThirdActionMoment H

private theorem p4Q2PR_oneSlabAction_row_continuous (A : Cfg) :
    Continuous (fun X : Cfg => S X A) := by
  have hPair : Continuous (fun X : Cfg => (X, A)) :=
    continuous_id.prodMk continuous_const
  have h := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
  simpa only [Function.comp_def] using h

private theorem p4Q2PR_shiftedCube_integral
    (f : Cfg → ℝ) (hf : Continuous f) (u : ℝ) :
    (∫ X : Cfg, (f X + u) ^ 3 ∂haar) =
      (∫ X : Cfg, (f X) ^ 3 ∂haar) +
      3 * u * (∫ X : Cfg, (f X) ^ 2 ∂haar) +
      3 * u ^ 2 * (∫ X : Cfg, f X ∂haar) + u ^ 3 := by
  have h1 : Integrable f haar :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun X : Cfg => (f X) ^ 2) haar :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h3 : Integrable (fun X : Cfg => (f X) ^ 3) haar :=
    (hf.pow 3).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLeft : Integrable
      (fun X : Cfg => (f X) ^ 3 + (3 * u) * (f X) ^ 2) haar :=
    h3.add (h2.const_mul _)
  have hRight : Integrable
      (fun X : Cfg => (3 * u ^ 2) * f X + u ^ 3) haar :=
    (h1.const_mul _).add (integrable_const _)
  calc
    (∫ X : Cfg, (f X + u) ^ 3 ∂haar) =
        ∫ X : Cfg,
          ((f X) ^ 3 + (3 * u) * (f X) ^ 2) +
          ((3 * u ^ 2) * f X + u ^ 3) ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      ring
    _ = ((∫ X : Cfg, (f X) ^ 3 ∂haar) +
        3 * u * (∫ X : Cfg, (f X) ^ 2 ∂haar)) +
        (3 * u ^ 2 * (∫ X : Cfg, f X ∂haar) + u ^ 3) := by
      rw [integral_add hLeft hRight]
      rw [integral_add h3 (h2.const_mul _)]
      rw [integral_add (h1.const_mul _) (integrable_const _)]
      simp only [integral_const_mul]
      simp
    _ = _ := by ring

/-- Inner original Haar cube: all powers of the full intermediate
spatial Wilson energy survive in the unchanged second Haar step. -/
theorem p4Q2PR_originalTwoSlabInnerCubic_expansion (A B : Cfg) :
    (∫ X : Cfg, (Q X A B) ^ 3 ∂haar) =
      -c A + 3 * S A B * b A -
      3 * (S A B) ^ 2 * a A + (S A B) ^ 3 := by
  have h :=
    p4Q2PR_shiftedCube_integral H
      (fun X : Cfg => S X A)
      (p4Q2PR_oneSlabAction_row_continuous H A) (S A B)
  change (∫ X : Cfg, (S X A + S A B) ^ 3 ∂haar) = _
  rw [h]
  unfold p4Q2PP2_originalOneSlabThirdActionMoment
    p4Q2PK_originalOneSlabFirstActionMoment
    p4Q2PK_originalOneSlabSecondActionMoment
  ring

/-- Bochner evaluation supplies continuity in the right boundary for
genuine full-action Haar moments on compact spatial SU(2) slices. -/
private theorem p4Q2PR_integral_first_continuous
    (f : C(Cfg × Cfg, ℝ)) :
    Continuous (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) := by
  let v : C(Cfg, C(Cfg, ℝ)) := f.curry
  have hv : Integrable (fun X : Cfg => v X) haar :=
    v.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun :
      (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) =
        (fun A : Cfg => (∫ X : Cfg, v X ∂haar) A) := by
    funext A
    rw [ContinuousMap.integral_apply hv A]
    rfl
  rw [hfun]
  exact (∫ X : Cfg, v X ∂haar).continuous

private theorem p4Q2PR_firstMoment_continuous :
    Continuous (fun A : Cfg => a A) := by
  have hW :
      Continuous (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hEq : (fun A : Cfg => a A) =
      (fun A : Cfg => -(1 / 2 : ℝ) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2 A -
        p4Q2JE_originalWilsonHaarZeroDerivativeConstant H) := by
    funext A
    exact p4Q2PM_originalFirstMoment_spatialWilson H A
  rw [hEq]
  exact (continuous_const.mul hW).sub continuous_const

private theorem p4Q2PR_secondMoment_continuous :
    Continuous (fun A : Cfg => b A) := by
  let f : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2) ^ 2),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow 2⟩
  have h := p4Q2PR_integral_first_continuous H f
  change Continuous (fun A : Cfg => b A) at h
  exact h

private theorem p4Q2PR_thirdMoment_continuous :
    Continuous (fun A : Cfg => c A) := by
  let f : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2) ^ 3),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow 3⟩
  have h := (p4Q2PR_integral_first_continuous H f).neg
  change Continuous (fun A : Cfg => c A) at h
  exact h

/-- FULL original double Haar cubic action moment, reduced to exactly
three original single-Haar weighted action moments. This does not
factor either interacting Wilson posterior into independent terms. -/
theorem p4Q2PR_originalTwoSlabThirdHaar_split (B : Cfg) :
    g B =
      (∫ A : Cfg, c A ∂haar) -
      3 * (∫ A : Cfg, S A B * b A ∂haar) +
      3 * (∫ A : Cfg, (S A B) ^ 2 * a A ∂haar) +
      c B := by
  have hRow := p4Q2PR_oneSlabAction_row_continuous H B
  have hA := p4Q2PR_firstMoment_continuous H
  have hB := p4Q2PR_secondMoment_continuous H
  have hC := p4Q2PR_thirdMoment_continuous H
  have hc : Integrable (fun A : Cfg => c A) haar :=
    hC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFirst : Integrable (fun A : Cfg => S A B * b A) haar :=
    (hRow.mul hB).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSecond : Integrable (fun A : Cfg => (S A B) ^ 2 * a A) haar :=
    ((hRow.pow 2).mul hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCube : Integrable (fun A : Cfg => (S A B) ^ 3) haar :=
    (hRow.pow 3).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hLeft : Integrable (fun A : Cfg =>
      c A - 3 * (S A B * b A)) haar :=
    hc.sub (hFirst.const_mul 3)
  have hRight : Integrable (fun A : Cfg =>
      3 * ((S A B) ^ 2 * a A)) haar :=
    hSecond.const_mul 3
  calc
    g B = (∫ A : Cfg, -(∫ X : Cfg, (Q X A B) ^ 3 ∂haar) ∂haar) := by
      unfold p4Q2PP2_originalTwoSlabThirdActionMoment
      rw [integral_neg]
    _ = ∫ A : Cfg,
          (c A - 3 * (S A B * b A) + 3 * ((S A B) ^ 2 * a A)) -
            (S A B) ^ 3 ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PR_originalTwoSlabInnerCubic_expansion H A B]
      ring
    _ = (∫ A : Cfg, c A ∂haar) -
          3 * (∫ A : Cfg, S A B * b A ∂haar) +
          3 * (∫ A : Cfg, (S A B) ^ 2 * a A ∂haar) +
          c B := by
      rw [integral_sub (hLeft.add hRight) hCube]
      rw [integral_add hLeft hRight]
      rw [integral_sub hc (hFirst.const_mul 3)]
      simp only [integral_const_mul]
      unfold p4Q2PP2_originalOneSlabThirdActionMoment
      ring

/-- The complete genuine quartic Ward residual becomes a centered
second cross-slab action moment minus a genuinely weighted first
cross-slab moment. No non-affinity premise is introduced. -/
theorem p4Q2PR_originalQuarticWardResidual_centeredCrossMoments
    (B : Cfg) :
    p4Q2PQ_originalQuarticWardResidual H B =
      (∫ A : Cfg, c A ∂haar) +
      3 * (∫ A : Cfg,
        (S A B) ^ 2 *
          (a A - p4Q2PQ_originalFirstActionMean H) ∂haar) -
      3 * (∫ A : Cfg, S A B * b A ∂haar) := by
  have hRow := p4Q2PR_oneSlabAction_row_continuous H B
  have hA := p4Q2PR_firstMoment_continuous H
  have hS2 : Integrable (fun A : Cfg => (S A B) ^ 2) haar :=
    (hRow.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSA : Integrable (fun A : Cfg => (S A B) ^ 2 * a A) haar :=
    ((hRow.pow 2).mul hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCentered :
      (∫ A : Cfg, (S A B) ^ 2 *
          (a A - p4Q2PQ_originalFirstActionMean H) ∂haar) =
        (∫ A : Cfg, (S A B) ^ 2 * a A ∂haar) -
          p4Q2PQ_originalFirstActionMean H * b B := by
    calc
      (∫ A : Cfg, (S A B) ^ 2 *
          (a A - p4Q2PQ_originalFirstActionMean H) ∂haar) =
          ∫ A : Cfg, (S A B) ^ 2 * a A -
            p4Q2PQ_originalFirstActionMean H * (S A B) ^ 2 ∂haar := by
        apply integral_congr_ae
        filter_upwards with A
        ring
      _ = (∫ A : Cfg, (S A B) ^ 2 * a A ∂haar) -
            p4Q2PQ_originalFirstActionMean H *
              (∫ A : Cfg, (S A B) ^ 2 ∂haar) := by
        rw [integral_sub hSA (hS2.const_mul _), integral_const_mul]
      _ = _ := rfl
  unfold p4Q2PQ_originalQuarticWardResidual
  rw [p4Q2PR_originalTwoSlabThirdHaar_split H B]
  calc
    (∫ A : Cfg, c A ∂haar) -
      3 * (∫ A : Cfg, S A B * b A ∂haar) +
      3 * (∫ A : Cfg, (S A B) ^ 2 * a A ∂haar) +
      c B - c B - 3 * p4Q2PQ_originalFirstActionMean H * b B =
      (∫ A : Cfg, c A ∂haar) +
      3 * ((∫ A : Cfg, (S A B) ^ 2 * a A ∂haar) -
        p4Q2PQ_originalFirstActionMean H * b B) -
      3 * (∫ A : Cfg, S A B * b A ∂haar) := by ring
    _ = _ := by rw [← hCentered]

end OriginalWilsonCubicHaar
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PR_originalTwoSlabInnerCubic_expansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PR_originalTwoSlabThirdHaar_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PR_originalQuarticWardResidual_centeredCrossMoments
