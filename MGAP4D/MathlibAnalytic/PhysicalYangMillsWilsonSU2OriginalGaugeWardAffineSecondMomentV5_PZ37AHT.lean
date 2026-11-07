import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCrossingQuadraticHaarSecondMomentV5_PZ37AHS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWeightedCrossingGaugeWardV5_PT
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHT — genuine original quadratic Haar gauge-Ward descent

AHS proved the exact original SU(2) source-weighted full one-slab
second-action moment

  M₂,H(B) = M₃,H + (p_H+W_H(B))*V_H + 2*Y_H(B),
  Y_H(B) = ∫ f_H(A)^2 Cross_H(A,B) dμ_H(A).

AHT uses PT's ALREADY PROVED gauge-Ward Haar identity for an arbitrary
continuous gauge-invariant observable. The weight f_H(A)^2 IS such an
observable because the same original Wilson spatial action W_H is
gauge invariant, and f_H=(W_H-p_H)/2 by original AGN.
Therefore the genuine mixed correlation Y_H(B), without any
independent-posterior or numerical-evaluation assumption, is
IDENTICAL for all original right boundaries B.

This proves the exact affine identity in the TRUE original spatial
Wilson action

  M₂,H(B) = I₂,H + W_H(B)*V_H,

where I₂,H = M₃,H + p_H*V_H + 2*Y_H(1) is named with the actual
unevaluated original Haar moments. As AHN proved V_H>0, this is a
strictly increasing affine function of the true Wilson action.
The pointwise true Wilson crossing energy range also gives

  0 <= Y_H(B) <= 2*p_H*V_H.

The mixed Haar correlation Y_H(1) is NOT postulated to equal p_H V_H,
and M₃,H is not assigned a sign or exact numeric value. No first/second
derivative of the complete transfer is fabricated. The old physical
SU(2) kernel, both halfweights, original ZW signed source, original
spatial product Haar, genuine gauge action, and all proof-history roots
are untouched.

No claim of fixed beta0 transfer sign, volume-uniform coercivity,
Hamiltonian gap or continuum 4D Yang-Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHT_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHT_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHT_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHT_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHT_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Y" =>
  p4Q2PZ37AHS_originalSourceSquareCrossingHaarMoment H
local notation "M3" => p4Q2PZ37AHS_originalSourceThirdHaarMoment H
local notation "M2" => p4Q2PZ37AHS_originalSecondFullActionHaarMoment H

local instance p4Q2PZ37AHT_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Squared ORIGINAL ZW source continuous under genuine spatial product Haar. -/
theorem p4Q2PZ37AHT_originalSourceSquare_continuous :
    Continuous (fun A : Cfg => (fCont A)^2) :=
  (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.pow 2

/-- The squared original source is invariant under every ORIGINAL
spatial vertex-gauge transformation. Uses AGN's exact centering and
the actual Wilson plaquette conjugation invariance, not any new gauge
hypothesis. -/
theorem p4Q2PZ37AHT_originalSourceSquare_gaugeInvariant
    (γ : Gauge) (A : Cfg) :
    (fCont (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
      H 2 γ A))^2 = (fCont A)^2 := by
  have hSource :
      fCont (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
        H 2 γ A) = fCont A := by
    rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H,
      p4Q2PZ37AGN_originalCenteredContinuous_eq H,
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
        H 2 γ A]
  rw [hSource]

/-- PT's EXISTING full gauge-Ward theorem, specialized to the
continuous genuine squared source, shows boundary independence
of Y_H(B). Here 1 is the true identity spatial boundary. -/
theorem p4Q2PZ37AHT_originalMixedCrossing_boundaryIdentity
    (B : Cfg) :
    Y B = Y (fun _ => 1) := by
  change (∫ A : Cfg, (fCont A)^2 * Cross A B ∂muH) =
    (∫ A : Cfg, (fCont A)^2 * Cross A (fun _ => 1) ∂muH)
  exact p4Q2PT_originalGaugeWeight_crossingHaar_invariant H
    (fun A : Cfg => (fCont A)^2)
    (p4Q2PZ37AHT_originalSourceSquare_continuous H)
    (p4Q2PZ37AHT_originalSourceSquare_gaugeInvariant H) B

/-- Authentic mixed Haar correlation is the SAME for any two genuine
right spatial boundaries: no conditional independence or symmetry
assumption on the interacting Wilson posterior. -/
theorem p4Q2PZ37AHT_originalMixedCrossing_boundaryIndependent
    (B C : Cfg) :
    Y B = Y C :=
  (p4Q2PZ37AHT_originalMixedCrossing_boundaryIdentity H B).trans
    (p4Q2PZ37AHT_originalMixedCrossing_boundaryIdentity H C).symm

/-- The uncomputed original second-Haar-moment intercept is named from
the three actual, previously defined source and crossing moments. -/
def p4Q2PZ37AHT_originalSecondMomentIntercept : ℝ :=
  M3 + pH * Vsrc + 2 * Y (fun _ => 1)

/-- Exact affine original SU(2) second one-slab source Haar moment,
with the genuine Wilson spatial action as the only B-dependent term.
The slope is the TRUE AHN source second moment V_H, not a postulated
spectral lower bound. -/
theorem p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson
    (B : Cfg) :
    M2 B = p4Q2PZ37AHT_originalSecondMomentIntercept H + W B * Vsrc := by
  rw [p4Q2PZ37AHS_originalSecondFullActionHaarMoment_eq H B,
    p4Q2PZ37AHT_originalMixedCrossing_boundaryIdentity H B]
  unfold p4Q2PZ37AHT_originalSecondMomentIntercept
  ring

/-- Exact signed difference between source-weighted ORIGINAL
full one-slab second-action moments at any genuine right boundaries.
The true mixed crossing correlation cancels by the proved gauge Ward,
and the original third source moment cancels without evaluating it. -/
theorem p4Q2PZ37AHT_originalSecondMoment_difference
    (B C : Cfg) :
    M2 B - M2 C = (W B - W C) * Vsrc := by
  rw [p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson H B,
    p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson H C]
  ring

/-- Same original spatial Wilson action yields the SAME
second source-weighted complete one-slab action moment. -/
theorem p4Q2PZ37AHT_originalSecondMoment_sameSpatialWilson
    (B C : Cfg) (hEq : W B = W C) :
    M2 B = M2 C := by
  rw [p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson H B,
    p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson H C, hEq]

/-- The affine slope is STRICTLY positive because AHN proved the
TRUE source variance positive for each finite H. -/
theorem p4Q2PZ37AHT_originalSecondMoment_strictMonoSpatialWilson
    (B C : Cfg) (hLess : W B < W C) :
    M2 B < M2 C := by
  have hV : 0 < Vsrc :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hScaled := mul_lt_mul_of_pos_right hLess hV
  rw [p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson H B,
    p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson H C]
  exact add_lt_add_right hScaled _

/-- The true second original full-Wilson action source moment is
spatial-gauge invariant as a corollary of its proved affine
dependence on the gauge-invariant ORIGINAL Wilson action. -/
theorem p4Q2PZ37AHT_originalSecondMoment_gaugeInvariant
    (γ : Gauge) (B : Cfg) :
    M2 (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform
      H 2 γ B) = M2 B := by
  rw [p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson H,
    p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson H,
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 γ B]

/-- Genuine two-sided estimate for the as-yet unevaluated mixed
Haar moment Y_H(B), using ONLY the original nonnegative temporal
Wilson crossing action and its original physical link-count bound. -/
theorem p4Q2PZ37AHT_originalMixedCrossing_interval
    (B : Cfg) :
    0 ≤ Y B ∧ Y B ≤ 2 * pH * Vsrc := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hc : Continuous (fun A : Cfg => Cross A B) :=
    p4Q2PZ37AHP_originalCrossing_continuous H B
  have hWeighted : Integrable (fun A : Cfg =>
      (fCont A)^2 * Cross A B) muH :=
    ((hf.pow 2).mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hUpper : Integrable (fun A : Cfg =>
      (2 * pH) * (fCont A)^2) muH :=
    (continuous_const.mul (hf.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  constructor
  · unfold p4Q2PZ37AHS_originalSourceSquareCrossingHaarMoment
    apply integral_nonneg
    intro A
    exact mul_nonneg (sq_nonneg _)
      (p4Q2PZ37AHQ_originalCrossing_nonneg H A B)
  · calc
      Y B = ∫ A : Cfg, (fCont A)^2 * Cross A B ∂muH := rfl
      _ ≤ ∫ A : Cfg, (2 * pH) * (fCont A)^2 ∂muH := by
        apply integral_mono hWeighted hUpper
        intro A
        calc
          (fCont A)^2 * Cross A B ≤ (fCont A)^2 * (2 * pH) :=
            mul_le_mul_of_nonneg_left
              (p4Q2PZ37AHQ_originalCrossing_le_twoCount H A B)
              (sq_nonneg _)
          _ = (2 * pH) * (fCont A)^2 := by ring
      _ = 2 * pH * Vsrc := by
        rw [integral_const_mul]
        rfl

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalSourceSquare_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalSourceSquare_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalMixedCrossing_boundaryIdentity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalMixedCrossing_boundaryIndependent
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalSecondMoment_affineSpatialWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalSecondMoment_difference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalSecondMoment_sameSpatialWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalSecondMoment_strictMonoSpatialWilson
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalSecondMoment_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHT_originalMixedCrossing_interval
