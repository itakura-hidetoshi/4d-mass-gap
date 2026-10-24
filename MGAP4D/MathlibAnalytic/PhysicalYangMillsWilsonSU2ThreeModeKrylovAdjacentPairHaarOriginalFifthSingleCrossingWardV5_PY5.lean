import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFifthWardTwoCrossingCoreV5_PY4C
import Mathlib.Tactic

/-!
# P4-Q2-PY5 — single-crossing sectors of the genuine fifth Wilson Ward residual

PY4 reduces the original full SU(2) Wilson fifth Ward residual to genuine
zero-, one- and two-temporal-crossing sectors. For the single-crossing
sector, the ORIGINAL third action moment c(A) has to be shown spatial
gauge invariant; this is proved here by simultaneously transforming
both ends of the true one-slab action under original spatial Haar.

The exact weight f(A) = c(A) - 3w(A)b(A) + 3w(A)^2 h(A)
is continuous and gauge invariant. PT's already-proved real Haar
single-link Ward symmetry thus makes its original crossing integral
independent of the right spatial boundary, without factoring posterior
measures. The centered h(A) has the same property.

No new axiom, sorry/admit, rank or nonvanishing hypothesis, Dobrushin,
surrogate spectral measure or continuum mass-gap assertion.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PY5_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PY5_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PY5_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PY5_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PY5_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PY5_spatialFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint
section OriginalFifthSingleCrossingGaugeWard
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
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
local notation "c" => p4Q2PP2_originalOneSlabThirdActionMoment H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H

/-- Third original one-slab action moment under EXACT simultaneous
spatial vertex gauge transform of both physical boundaries. -/
theorem p4Q2PY5_originalThirdMoment_gaugeInvariant
    (γ : Gauge) (B : Cfg) :
    c (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ B) =
      c B := by
  let T : Cfg → Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  have hPres : MeasurePreserving T haar haar :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H 2 γ
  have hPair : Continuous (fun X : Cfg => (X, T B)) :=
    continuous_id.prodMk continuous_const
  have hS : Continuous (fun X : Cfg => S X (T B)) := by
    have hc := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hc
  let f : Cfg → ℝ := fun X => (S X (T B)) ^ 3
  have hf : AEStronglyMeasurable f haar :=
    (hS.pow 3).measurable.aestronglyMeasurable
  have hmap : Measure.map T haar = haar := hPres.map_eq
  have hfm : AEStronglyMeasurable f (Measure.map T haar) := by
    rw [hmap]
    exact hf
  have hIntegral :
      (∫ X : Cfg, (S X (T B)) ^ 3 ∂haar) =
      (∫ X : Cfg, (S X B) ^ 3 ∂haar) := by
    calc
      (∫ X : Cfg, (S X (T B)) ^ 3 ∂haar) =
          ∫ X : Cfg, f X ∂haar := rfl
      _ = ∫ X : Cfg, f X ∂Measure.map T haar := by rw [hmap]
      _ = ∫ X : Cfg, f (T X) ∂haar :=
        MeasureTheory.integral_map hPres.measurable.aemeasurable hfm
      _ = ∫ X : Cfg, (S X B) ^ 3 ∂haar := by
        apply integral_congr_ae
        filter_upwards with X
        change (S (T X) (T B)) ^ 3 = (S X B) ^ 3
        rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_gaugeInvariant
          H 2 γ X B]
  change -(∫ X : Cfg, (S X (T B)) ^ 3 ∂haar) =
    -(∫ X : Cfg, (S X B) ^ 3 ∂haar)
  rw [hIntegral]

/-- Continuity of original negative third power Haar moment. -/
theorem p4Q2PY5_originalThirdMoment_continuous :
    Continuous (fun A : Cfg => c A) := by
  let f : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2) ^ 3),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow 3⟩
  let q : C(Cfg, C(Cfg, ℝ)) := f.curry
  have hq : Integrable (fun X : Cfg => q X) haar :=
    q.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun :
      (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) =
      (fun A : Cfg => (∫ X : Cfg, q X ∂haar) A) := by
    funext A
    rw [ContinuousMap.integral_apply hq A]
    rfl
  have hc : Continuous (fun A : Cfg => ∫ X : Cfg, f (X, A) ∂haar) := by
    rw [hfun]
    exact (∫ X : Cfg, q X ∂haar).continuous
  have hc' := hc.neg
  change Continuous (fun A : Cfg => c A) at hc'
  exact hc'

/-- Gauge invariance of the true centered first moment follows
from the original spatial Wilson plaquette action, not an axiom. -/
theorem p4Q2PY5_originalCenteredFirst_gaugeInvariant
    (γ : Gauge) (A : Cfg) :
    h (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) =
      h A := by
  let T : Cfg → Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  change a (T A) - p4Q2PQ_originalFirstActionMean H =
    a A - p4Q2PQ_originalFirstActionMean H
  rw [p4Q2PM_originalFirstMoment_spatialWilson H (T A),
    p4Q2PM_originalFirstMoment_spatialWilson H A,
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 γ A]

/-- Third-moment weighted single-crossing source at fifth order;
the full left spatial plaquette weight remains present. -/
noncomputable def p4Q2PY5_originalHigherSingleCrossingWardWeight
    (A : Cfg) : ℝ :=
  c A - 3 * w A * b A + 3 * (w A) ^ 2 * h A

local notation "f₅" => p4Q2PY5_originalHigherSingleCrossingWardWeight H

theorem p4Q2PY5_originalHigherSingleCrossingWardWeight_continuous :
    Continuous (fun A : Cfg => f₅ A) := by
  have hw : Continuous (fun A : Cfg => w A) :=
    continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have hh : Continuous (fun A : Cfg => h A) := by
    change Continuous (fun A : Cfg =>
      a A - p4Q2PQ_originalFirstActionMean H)
    have ha : Continuous (fun A : Cfg => a A) := by
      have heq : (fun A : Cfg => a A) =
          (fun A : Cfg =>
            -(1 / 2 : ℝ) * W A -
              p4Q2JE_originalWilsonHaarZeroDerivativeConstant H) := by
        funext A
        exact p4Q2PM_originalFirstMoment_spatialWilson H A
      rw [heq]
      exact (continuous_const.mul
        (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous
          H 2)).sub continuous_const
    exact ha.sub continuous_const
  have hc := p4Q2PY5_originalThirdMoment_continuous H
  have hb := p4Q2PT_originalSecondMoment_continuous H
  change Continuous (fun A : Cfg =>
    c A - 3 * w A * b A + 3 * (w A) ^ 2 * h A)
  exact (hc.sub ((continuous_const.mul hw).mul hb)).add
    ((continuous_const.mul (hw.pow 2)).mul hh)

theorem p4Q2PY5_originalHigherSingleCrossingWardWeight_gaugeInvariant
    (γ : Gauge) (A : Cfg) :
    f₅ (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) =
      f₅ A := by
  let T : Cfg → Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  have hc := p4Q2PY5_originalThirdMoment_gaugeInvariant H γ A
  have hb := p4Q2PT_originalSecondMoment_gaugeInvariant H γ A
  have hh := p4Q2PY5_originalCenteredFirst_gaugeInvariant H γ A
  have hw : w (T A) = w A := by
    change (1 / 2 : ℝ) * W (T A) = (1 / 2 : ℝ) * W A
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 γ A]
  unfold p4Q2PY5_originalHigherSingleCrossingWardWeight
  rw [hc, hb, hh, hw]

/-- The entire genuine one-crossing fifth-order weight f5 has
reference-Haar integral INDEPENDENT of the right boundary B. -/
theorem p4Q2PY5_originalHigherSingleCrossingWardHaar_invariant (B : Cfg) :
    (∫ A : Cfg, f₅ A * Cross A B ∂haar) =
      (∫ A : Cfg, f₅ A * Cross A (fun _ => 1) ∂haar) := by
  exact p4Q2PT_originalGaugeWeight_crossingHaar_invariant H f₅
    (p4Q2PY5_originalHigherSingleCrossingWardWeight_continuous H)
    (p4Q2PY5_originalHigherSingleCrossingWardWeight_gaugeInvariant H) B

/-- The SU(2) centered first moment is gauge invariant, so its
original single-crossing Haar pairing is a true boundary constant. -/
theorem p4Q2PY5_originalCenteredFirst_singleCrossingHaar_invariant (B : Cfg) :
    (∫ A : Cfg, h A * Cross A B ∂haar) =
      (∫ A : Cfg, h A * Cross A (fun _ => 1) ∂haar) := by
  have ha : Continuous (fun A : Cfg => a A) := by
    have heq : (fun A : Cfg => a A) =
        (fun A : Cfg =>
          -(1 / 2 : ℝ) * W A -
            p4Q2JE_originalWilsonHaarZeroDerivativeConstant H) := by
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
  exact p4Q2PT_originalGaugeWeight_crossingHaar_invariant H h hh
    (p4Q2PY5_originalCenteredFirst_gaugeInvariant H) B

end OriginalFifthSingleCrossingGaugeWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalThirdMoment_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalThirdMoment_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalCenteredFirst_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalHigherSingleCrossingWardWeight_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalHigherSingleCrossingWardWeight_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalHigherSingleCrossingWardHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PY5_originalCenteredFirst_singleCrossingHaar_invariant
