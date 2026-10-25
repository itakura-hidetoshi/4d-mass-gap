import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFourLinkSchurTheoremV5_PZ35D9D
import Mathlib.Tactic

/-!
# P4-Q2-PZ36 — exact affine fifth stripped Haar moment, not a sixth Ward witness

PZ35 evaluates the original four-link integral. The next issue is not
whether an isolated low-sector term is nonzero, but whether the actual
one/two-slab Taylor coefficients cancel. Keep the original spatial
Wilson half-action w, temporal crossing C, full spatial product Haar,
and both physical posteriors.

For any REAL scalar r, define an auxiliary observable, not a new model,
  R5(r,B) = integral (r*w(X)+C(X,B))^5 dHaar(X).
Every fifth-degree binomial sector is boundary invariant except w*C^4.
The original PZ35 theorem gives its variation +3*w(B)/32. Therefore
  R5(r,B) = R5(r,I) + (15*r/32)*w(B).
In particular r=1 is the TRUE right-stripped fifth Wilson moment;
r=2 is the doubled spatial weight needed for the subsequent two-slab
moment calculation. This theorem is NOT a two-slab factorization.

The affine term is collinear with the first Taylor boundary response:
its Vandermonde determinant vanishes identically. Sixth Ward zero or
nonzero, rank three and a continuum gap are NOT asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ36_topologicalGroup : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ36_compactSpace : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ36_secondCountable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ36_measurableSpace : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ36_borelSpace : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ36_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
local instance p4Q2PZ36_probability (H : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section OriginalScaledStrippedFifth
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "I" => (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => (1 : G))
local notation "F32" => p4Q2PZ22_originalSpatialCubeCrossingSquareHaar H
local notation "F23" => p4Q2PZ22_originalSpatialSquareCrossingCubeHaar H
local notation "F14" => p4Q2PZ22_originalSpatialCrossingFourthHaar H

private theorem p4Q2PZ36_half_continuous : Continuous (fun X : Cfg => w X) :=
  continuous_const.mul
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)

private theorem p4Q2PZ36_cross_continuous (B : Cfg) :
    Continuous (fun X : Cfg => Cross X B) := by
  have hp : Continuous (fun X : Cfg => (X,B)) :=
    continuous_id.prodMk continuous_const
  simpa only [Function.comp_def] using
    ((p4Q2IW_originalWilsonCrossingAction_continuous H).comp hp)

/-- Arbitrary original spatial Wilson powers are valid gauge-invariant
weights for the genuine one-crossing Haar Ward theorem. -/
theorem p4Q2PZ36_originalSpatialPower_crossingHaar_invariant
    (n : ℕ) (B : Cfg) :
    (∫ X : Cfg, (w X)^n * Cross X B ∂haar) =
      (∫ X : Cfg, (w X)^n * Cross X I ∂haar) := by
  have hc : Continuous (fun X : Cfg => (w X)^n) :=
    (p4Q2PZ36_half_continuous H).pow n
  have hInv : ∀ (γ : Gauge) (X : Cfg),
      (w (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
        H 2 γ X))^n = (w X)^n := by
    intro γ X
    unfold p4Q2PS_originalHalfSpatialAction
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 γ X]
  exact p4Q2PT_originalGaugeWeight_crossingHaar_invariant
    H (fun X : Cfg => (w X)^n) hc hInv B

/-- Sign-critical: the ORIGINAL uncentered w*Cross^4 moment increases
by +3*w(B)/32, although the centered D14 is -3*w(B)/32. -/
theorem p4Q2PZ36_originalF14_affine (B : Cfg) :
    F14 B = F14 I + (3 / 32 : ℝ) * w B := by
  rw [p4Q2PZ24_originalF14_eq_const_sub_defect H B,
    p4Q2PZ35D9D_originalD14_unconditional H B]
  ring

/-- An auxiliary scalar family of observables on the SAME physical
configuration and Haar measure. It does not define another model. -/
noncomputable def p4Q2PZ36_originalScaledStrippedFifth
    (r : ℝ) (B : Cfg) : ℝ :=
  ∫ X : Cfg, (r * w X + Cross X B)^5 ∂haar

local notation "R5" => p4Q2PZ36_originalScaledStrippedFifth H

/-- Binomial expansion with actual Haar integrability of all six terms.
No independence of spatial and crossing observables is assumed. -/
theorem p4Q2PZ36_originalScaledStrippedFifth_expansion
    (r : ℝ) (B : Cfg) :
    R5 r B =
      r^5 * (∫ X : Cfg, (w X)^5 ∂haar) +
      5*r^4 * (∫ X : Cfg, (w X)^4 * Cross X B ∂haar) +
      10*r^3 * F32 B + 10*r^2 * F23 B + 5*r * F14 B +
      (∫ X : Cfg, (Cross X B)^5 ∂haar) := by
  let f : Fin 6 → Cfg → ℝ :=
    ![fun X => r^5 * (w X)^5,
      fun X => (5*r^4) * ((w X)^4 * Cross X B),
      fun X => (10*r^3) * ((w X)^3 * (Cross X B)^2),
      fun X => (10*r^2) * ((w X)^2 * (Cross X B)^3),
      fun X => (5*r) * (w X * (Cross X B)^4),
      fun X => (Cross X B)^5]
  have hw := p4Q2PZ36_half_continuous H
  have hc := p4Q2PZ36_cross_continuous H B
  have hf (i : Fin 6) : Continuous (f i) := by
    fin_cases i <;> dsimp [f] <;> fun_prop (disch := assumption)
  have hi (i : Fin 6) : Integrable (f i) haar :=
    (hf i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPoint (X : Cfg) : (r*w X+Cross X B)^5 = ∑ i : Fin 6, f i X := by
    simp [f, Fin.sum_univ_succ] <;> ring
  have hSum := integral_finset_sum (μ := haar) (Finset.univ : Finset (Fin 6))
    (f := f) (fun i _hi => hi i)
  calc
    R5 r B = ∫ X : Cfg, (∑ i : Fin 6, f i X) ∂haar := by
      unfold p4Q2PZ36_originalScaledStrippedFifth
      apply integral_congr_ae
      filter_upwards with X
      exact hPoint X
    _ = _ := by
      simpa [f, Fin.sum_univ_succ, integral_const_mul,
        p4Q2PZ22_originalSpatialCubeCrossingSquareHaar,
        p4Q2PZ22_originalSpatialSquareCrossingCubeHaar,
        p4Q2PZ22_originalSpatialCrossingFourthHaar, add_assoc] using hSum

/-- Exact affine boundary law for EVERY real spatial coefficient and
EVERY original finite period, including H=0. -/
theorem p4Q2PZ36_originalScaledStrippedFifth_affine
    (r : ℝ) (B : Cfg) :
    R5 r B = R5 r I + (15 / 32 : ℝ) * r * w B := by
  rw [p4Q2PZ36_originalScaledStrippedFifth_expansion H r B,
    p4Q2PZ36_originalScaledStrippedFifth_expansion H r I,
    p4Q2PZ36_originalSpatialPower_crossingHaar_invariant H 4 B,
    p4Q2PZ32_originalF32_Haar_boundaryInvariant H B,
    p4Q2PZ23_originalF23_Haar_boundaryInvariant H B,
    p4Q2PZ36_originalF14_affine H B,
    p4Q2PZ19_originalFullCrossingPowerHaar_invariant H 5 B]
  ring

/-- Pairwise boundary law without identity-boundary normalization. -/
theorem p4Q2PZ36_originalScaledStrippedFifth_difference
    (r : ℝ) (A B : Cfg) :
    R5 r B - R5 r A = (15 / 32 : ℝ) * r * (w B - w A) := by
  rw [p4Q2PZ36_originalScaledStrippedFifth_affine H r A,
    p4Q2PZ36_originalScaledStrippedFifth_affine H r B]
  ring

/-- The TRUE right-stripped original Wilson action (r=1), not a
hypothetical fifth moment, now has its exact boundary dependence. -/
theorem p4Q2PZ36_originalStrippedFifth_affine (B : Cfg) :
    p4Q2PZ18_originalStrippedHaarMoment H 5 B =
      p4Q2PZ18_originalStrippedHaarMoment H 5 I + (15 / 32 : ℝ) * w B := by
  simpa only [p4Q2PZ36_originalScaledStrippedFifth,
    p4Q2PZ18_originalStrippedHaarMoment,
    p4Q2PS_originalRightStrippedAction, one_mul, mul_one] using
      (p4Q2PZ36_originalScaledStrippedFifth_affine H 1 B)

/-- Doubled spatial observable relevant to the two-slab expansion.
This does NOT identify a complete two-slab moment with this alone. -/
theorem p4Q2PZ36_originalDoubledSpatialFifth_affine (B : Cfg) :
    R5 2 B = R5 2 I + (15 / 16 : ℝ) * w B := by
  rw [p4Q2PZ36_originalScaledStrippedFifth_affine H 2 B]
  ring

/-- A nonconstant fifth Haar moment still gives ZERO when paired
with the first spatial-action response in a three-boundary minor.
This forbids using its nonzero slope as a sixth-Ward witness. -/
theorem p4Q2PZ36_originalScaledFifth_spatialDeterminant_zero
    (r : ℝ) (A B C : Cfg) :
    (w B-w A)*(R5 r C-R5 r A) -
      (w C-w A)*(R5 r B-R5 r A) = 0 := by
  rw [p4Q2PZ36_originalScaledStrippedFifth_difference H r A C,
    p4Q2PZ36_originalScaledStrippedFifth_difference H r A B]
  ring

end OriginalScaledStrippedFifth
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36_originalSpatialPower_crossingHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36_originalF14_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36_originalScaledStrippedFifth_expansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36_originalScaledStrippedFifth_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36_originalScaledStrippedFifth_difference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36_originalStrippedFifth_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36_originalDoubledSpatialFifth_affine
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36_originalScaledFifth_spatialDeterminant_zero
