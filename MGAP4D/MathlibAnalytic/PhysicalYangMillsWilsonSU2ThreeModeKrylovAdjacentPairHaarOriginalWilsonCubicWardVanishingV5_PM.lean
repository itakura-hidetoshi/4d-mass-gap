import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonWeightedCrossingHaarWardV5_PL
import Mathlib.Tactic

/-!
# P4-Q2-PM — true Wilson two-slab mixed action moment is affine in first variation

PK produced the exact ORIGINAL Wilson two-slab action and formal Taylor
moments. PL proved the ORIGINAL spatial-Wilson-weighted temporal-crossing
Haar Ward identity, without replacing the true interacting posterior.

Using the original first moment a(X) = -W(X)/2 - c_H and PL and IX,
the genuine spatial Haar mean of C(X,B)*a(X) is independent of B.
The complete original one-slab action S(X,B) then yields

  d(B) - d(A) = (∫ X, a(X) dμ) * (a(B) - a(A))

for PK's TRUE mixed double-Wilson action moment
  d(B) = -∫ X, S(X,B)*a(X) dμ(X).

This gives the unconditional vanishing of PK's cubic obstruction
for EVERY three actual SU(2) spatial boundary configurations.
The order-two FORMAL Taylor jets consequently have a quartic-only
algebraic determinant. This does NOT establish a quartic coefficient
of the fully integrated original kernel without controlling its genuine
third derivatives/remainders, nor a nonzero quartic witness or D3>0.

No spectral surrogate, interacting-posterior replacement, new rank
axiom, sorry, admit, Dobrushin or continuum mass-gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section OriginalTwoSlabMixedMomentWard
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "d" => p4Q2PK_originalMixedTwoSlabActionMoment H
local notation "cH" => p4Q2JE_originalWilsonHaarZeroDerivativeConstant H

/-- The first genuine original-Wilson Haar action moment has precisely
the spatial-plaquette profile already constructed in JE and JF. -/
theorem p4Q2PM_originalFirstMoment_spatialWilson (B : Cfg) :
    a B = -(1 / 2 : ℝ) * W B - cH := by
  rw [p4Q2PK_originalFirstMoment_eq_trueWilsonDerivative H B]
  rfl

/-- A linear consequence of the actual PL Ward identity: the ORIGINAL
crossing energy weighted by the physical first variation is independent
of the right boundary. Its proof retains the full spatial Wilson action
inside the true reference Haar integration. -/
theorem p4Q2PM_originalCrossing_weightedFirstMoment_Haar_invariant
    (B : Cfg) :
    (∫ X : Cfg, Cross X B * a X ∂haar) =
      (∫ X : Cfg, Cross X (fun _ => 1) * a X ∂haar) := by
  have hW : Continuous W :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hCross (D : Cfg) :
      Continuous (fun X : Cfg => Cross X D) := by
    have hPair : Continuous (fun X : Cfg => (X, D)) :=
      continuous_id.prodMk continuous_const
    have h := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using h
  have hWC (D : Cfg) :
      Integrable (fun X : Cfg => W X * Cross X D) haar :=
    (hW.mul (hCross D)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC (D : Cfg) :
      Integrable (fun X : Cfg => Cross X D) haar :=
    (hCross D).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFormula (D : Cfg) :
      (∫ X : Cfg, Cross X D * a X ∂haar) =
        -(1 / 2 : ℝ) * (∫ X : Cfg, W X * Cross X D ∂haar) -
          cH * (∫ X : Cfg, Cross X D ∂haar) := by
    calc
      (∫ X : Cfg, Cross X D * a X ∂haar) =
          ∫ X : Cfg,
            (-(1 / 2 : ℝ)) * (W X * Cross X D) -
              cH * Cross X D ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        rw [p4Q2PM_originalFirstMoment_spatialWilson H X]
        ring
      _ = -(1 / 2 : ℝ) *
            (∫ X : Cfg, W X * Cross X D ∂haar) -
          cH * (∫ X : Cfg, Cross X D ∂haar) := by
        rw [integral_sub ((hWC D).const_mul _) ((hC D).const_mul _),
          integral_const_mul, integral_const_mul]
  calc
    (∫ X : Cfg, Cross X B * a X ∂haar) =
        -(1 / 2 : ℝ) * (∫ X : Cfg, W X * Cross X B ∂haar) -
          cH * (∫ X : Cfg, Cross X B ∂haar) := hFormula B
    _ = -(1 / 2 : ℝ) *
          (∫ X : Cfg, W X * Cross X (fun _ => 1) ∂haar) -
          cH * (∫ X : Cfg, Cross X (fun _ => 1) ∂haar) := by
      rw [p4Q2PL_originalSpatialWilson_weightedCrossingHaar_invariant H B,
        p4Q2IX_originalCrossingAction_HaarMean_eq_identity H B]
    _ = (∫ X : Cfg, Cross X (fun _ => 1) * a X ∂haar) :=
      (hFormula (fun _ => 1)).symm

/-- The ACTUAL original mixed two-slab Wilson action moment is the
sum of its left spatial term, its crossing term and its right
half-spatial boundary term. All integrability obligations are discharged
using true compact finite spatial SU(2) configuration continuity. -/
theorem p4Q2PM_originalMixedMoment_integral_split (B : Cfg) :
    d B =
      -((∫ X : Cfg, (1 / 2 : ℝ) * W X * a X ∂haar) +
        (∫ X : Cfg, Cross X B * a X ∂haar) +
        (1 / 2 : ℝ) * W B * (∫ X : Cfg, a X ∂haar)) := by
  have hW : Continuous W :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hFirst : Continuous (fun X : Cfg => a X) := by
    have hEq : (fun X : Cfg => a X) =
        fun X : Cfg => p4Q2JE_originalWilsonHaarZeroDerivativeProfile H X := by
      funext X
      exact p4Q2PK_originalFirstMoment_eq_trueWilsonDerivative H X
    rw [hEq]
    exact (p4Q2JE_originalWilsonHaarZeroDerivativeProfile H).continuous
  have hC : Continuous (fun X : Cfg => Cross X B) := by
    have hPair : Continuous (fun X : Cfg => (X, B)) :=
      continuous_id.prodMk continuous_const
    have h := (p4Q2IW_originalWilsonCrossingAction_continuous H).comp hPair
    simpa only [Function.comp_def] using h
  have hA :
      Integrable (fun X : Cfg => (1 / 2 : ℝ) * W X * a X) haar :=
    ((continuous_const.mul hW).mul hFirst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB :
      Integrable (fun X : Cfg => Cross X B * a X) haar :=
    (hC.mul hFirst).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hC' :
      Integrable (fun X : Cfg => (1 / 2 : ℝ) * W B * a X) haar :=
    (hFirst.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  have hPoint (X : Cfg) :
      S X B * a X =
        ((1 / 2 : ℝ) * W X * a X + Cross X B * a X) +
          (1 / 2 : ℝ) * W B * a X := by
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    ring
  have hEq :
      (∫ X : Cfg, S X B * a X ∂haar) =
        ∫ X : Cfg,
          ((1 / 2 : ℝ) * W X * a X + Cross X B * a X) +
            (1 / 2 : ℝ) * W B * a X ∂haar := by
    apply integral_congr_ae
    filter_upwards with X
    exact hPoint X
  change -(∫ X : Cfg, S X B * a X ∂haar) = _
  rw [hEq, integral_add (hA.add hB) hC',
    integral_add hA hB, integral_const_mul]
  ring

/-- A genuine two-slab Wilson moment identity: PL removes ALL
right-boundary dependence of the first-order crossing contribution.
Consequently the mixed two-slab second-order action moment changes
along the SAME physical spatial-Wilson direction as the first moment.
The proportionality scalar is the actual first moment's Haar mean. -/
theorem p4Q2PM_originalMixedMoment_difference_proportional
    (A B : Cfg) :
    d B - d A =
      (∫ X : Cfg, a X ∂haar) * (a B - a A) := by
  rw [p4Q2PM_originalMixedMoment_integral_split H B,
    p4Q2PM_originalMixedMoment_integral_split H A,
    p4Q2PM_originalCrossing_weightedFirstMoment_Haar_invariant H B,
    p4Q2PM_originalCrossing_weightedFirstMoment_Haar_invariant H A,
    p4Q2PM_originalFirstMoment_spatialWilson H B,
    p4Q2PM_originalFirstMoment_spatialWilson H A]
  ring

/-- The original two-slab mixed moment is GENUINELY affine in the
original one-slab Haar derivative. Unlike PK's abstract affine test,
here its existence is derived from the unchanged finite-volume SU(2)
Wilson action and PL's true spatial Wilson Haar Ward symmetry. -/
theorem p4Q2PM_originalMixedMoment_affine_firstMoment :
    ∃ s c : ℝ, ∀ B : Cfg, d B = s * a B + c := by
  let s : ℝ := ∫ X : Cfg, a X ∂haar
  let A₀ : Cfg := fun _ => 1
  let c : ℝ := d A₀ - s * a A₀
  refine ⟨s, c, ?_⟩
  intro B
  have hDiff : d B - d A₀ = s * (a B - a A₀) := by
    exact p4Q2PM_originalMixedMoment_difference_proportional H A₀ B
  calc
    d B = (d B - d A₀) + d A₀ := by ring
    _ = s * (a B - a A₀) + d A₀ := by rw [hDiff]
    _ = s * a B + c := by dsimp only [c]; ring

/-- UNCONDITIONAL vanishing of the cubic obstruction of the true
SU(2) Wilson action-moment formal three-boundary minor, for EVERY
triple of physical spatial SU(2) boundary configurations. -/
theorem p4Q2PM_originalLiteralCubicObstruction_zero (A B C : Cfg) :
    p4Q2PK_originalLiteralCubicObstruction H A B C = 0 := by
  obtain ⟨s, c, hAffine⟩ :=
    p4Q2PM_originalMixedMoment_affine_firstMoment H
  exact p4Q2PK_originalLiteralCubicObstruction_vanishes_of_affine
    H A B C s c hAffine

/-- PK's degree-two *FORMAL* one-slab/two-slab Wilson Taylor jets have
no quadratic or cubic three-boundary determinant coefficients. The
remaining algebraic quartic factor is expressed in unchanged Wilson
Haar moments. It is not yet the coefficient of the ACTUAL integrated
physical Wilson minor (third-order jet terms also contribute there). -/
theorem p4Q2PM_originalWilsonFormalTaylorMinor_quarticOnly
    (beta : ℝ) (A B C : Cfg) :
    (p4Q2PK_originalOneSlabFormalTaylor2 H beta B -
        p4Q2PK_originalOneSlabFormalTaylor2 H beta A) *
      (p4Q2PK_originalTwoSlabFormalTaylor2 H beta C -
        p4Q2PK_originalTwoSlabFormalTaylor2 H beta A) -
    (p4Q2PK_originalOneSlabFormalTaylor2 H beta C -
        p4Q2PK_originalOneSlabFormalTaylor2 H beta A) *
      (p4Q2PK_originalTwoSlabFormalTaylor2 H beta B -
        p4Q2PK_originalTwoSlabFormalTaylor2 H beta A) =
      beta ^ 4 / 2 *
        ((p4Q2PK_originalOneSlabSecondActionMoment H B -
            p4Q2PK_originalOneSlabSecondActionMoment H A) *
          (p4Q2PK_originalMixedTwoSlabActionMoment H C -
            p4Q2PK_originalMixedTwoSlabActionMoment H A) -
        (p4Q2PK_originalOneSlabSecondActionMoment H C -
            p4Q2PK_originalOneSlabSecondActionMoment H A) *
          (p4Q2PK_originalMixedTwoSlabActionMoment H B -
            p4Q2PK_originalMixedTwoSlabActionMoment H A)) := by
  rw [p4Q2PK_originalWilsonFormalTaylorMinor_factor H beta A B C,
      p4Q2PM_originalLiteralCubicObstruction_zero H A B C]
  ring

end OriginalTwoSlabMixedMomentWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PM_originalFirstMoment_spatialWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PM_originalCrossing_weightedFirstMoment_Haar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PM_originalMixedMoment_integral_split
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PM_originalMixedMoment_difference_proportional
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PM_originalMixedMoment_affine_firstMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PM_originalLiteralCubicObstruction_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PM_originalWilsonFormalTaylorMinor_quarticOnly
