import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWardRightSpatialStripV5_PS
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeAction
import Mathlib.Tactic

/-!
# P4-Q2-PT — the ORIGINAL Wilson gauge-weighted single-crossing Ward identity

An arbitrary *genuinely spatial-gauge-invariant continuous weight* has a
right-boundary-independent Haar integral against a single temporal
crossing Wilson action. Unlike an artificial independent-posterior
factorization, this is a change of variables in the original spatial
link product Haar measure by a genuine vertex gauge transformation.

Show the actual original one-slab second action Haar moment b(A) is
spatial-gauge invariant. Consequently the PS weight
  k(A) = 2*(W(A)/2)*(a(A)-mean_H(a))-b(A)
is continuous and gauge invariant, and its weighted single-crossing
Haar integral is independent of the right SU(2) configuration B.

The original interacting physical transfer, its two posteriors, all
spatial plaquette Wilson terms, and the unmodified Gauss-law source
remain unchanged. The double-crossing term is NOT assumed to vanish.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PT_spatialLinksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section GenuineGaugeWeightedSingleCrossing
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Gauge" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "a" => p4Q2PK_originalOneSlabFirstActionMoment H
local notation "b" => p4Q2PK_originalOneSlabSecondActionMoment H
local notation "w" => p4Q2PS_originalHalfSpatialAction H
local notation "h" => p4Q2PS_originalCenteredFirstMoment H

/-- Original Haar Ward symmetry with an *arbitrary* continuous
gauge-invariant weight; no independent link posterior is used. -/
theorem p4Q2PT_originalGaugeWeight_singleLinkHaar_invariant
    (φ : Cfg → ℝ) (hφ : Continuous φ)
    (hGauge : ∀ (γ : Gauge) (A : Cfg),
      φ (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) =
        φ A)
    (e : Link) (B : Cfg) :
    (∫ A : Cfg, φ A * E ((A e)⁻¹ * B e) ∂haar) =
      (∫ A : Cfg, φ A * E ((A e)⁻¹) ∂haar) := by
  let γ : Gauge := fun v => if v = e.1 then B e else 1
  have hsrc : γ e.1 = B e := by simp [γ]
  have htar : γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) = 1 := by
    simp [γ, p4Q2PL_originalSpatialLink_target_ne_source H e]
  let T : Cfg → Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  have hPres : MeasurePreserving T haar haar :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H 2 γ
  have hRel (A : Cfg) :
      ((T A e)⁻¹ * B e) = (A e)⁻¹ := by
    change
      ((γ e.1 * A e *
          (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹)⁻¹ *
          B e) = (A e)⁻¹
    rw [hsrc, htar]
    group
  let f : Cfg → ℝ := fun A => φ A * E ((A e)⁻¹ * B e)
  let g : Cfg → ℝ := fun A => φ A * E ((A e)⁻¹)
  have hE : Continuous (fun A : Cfg => E ((A e)⁻¹ * B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hf : AEStronglyMeasurable f haar :=
    (hφ.mul hE).measurable.aestronglyMeasurable
  have hpoint (A : Cfg) : f (T A) = g A := by
    change φ (T A) * E ((T A e)⁻¹ * B e) = φ A * E ((A e)⁻¹)
    rw [hGauge γ A, hRel A]
  have hmap : Measure.map T haar = haar := hPres.map_eq
  have hfm : AEStronglyMeasurable f (Measure.map T haar) := by
    rw [hmap]
    exact hf
  calc
    (∫ A : Cfg, φ A * E ((A e)⁻¹ * B e) ∂haar) =
        ∫ A : Cfg, f A ∂haar := rfl
    _ = ∫ A : Cfg, f A ∂Measure.map T haar := by rw [hmap]
    _ = ∫ A : Cfg, f (T A) ∂haar :=
      MeasureTheory.integral_map hPres.measurable.aemeasurable hfm
    _ = ∫ A : Cfg, g A ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact hpoint A
    _ = (∫ A : Cfg, φ A * E ((A e)⁻¹) ∂haar) := rfl

/-- Ward symmetry persists for every finite sum of the ORIGINAL
temporal crossing plaquettes; correlations are not factored. -/
theorem p4Q2PT_originalGaugeWeight_finiteLinkHaar_invariant
    (φ : Cfg → ℝ) (hφ : Continuous φ)
    (hGauge : ∀ (γ : Gauge) (A : Cfg),
      φ (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) =
        φ A)
    (es : List Link) (B : Cfg) :
    (∫ A : Cfg,
      φ A * ((es.map fun e => E ((A e)⁻¹ * B e)).sum) ∂haar) =
    (∫ A : Cfg,
      φ A * ((es.map fun e => E ((A e)⁻¹)).sum) ∂haar) := by
  have hEc (e : Link) (B : Cfg) :
      Continuous (fun A : Cfg => E ((A e)⁻¹ * B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hSum (xs : List Link) (B : Cfg) :
      Continuous (fun A : Cfg =>
        ((xs.map fun e => E ((A e)⁻¹ * B e)).sum)) := by
    induction xs with
    | nil =>
        simpa using (continuous_const :
          Continuous (fun _ : Cfg => (0 : ℝ)))
    | cons e xs ih =>
        simpa only [List.map_cons, List.sum_cons] using (hEc e B).add ih
  have hInt (xs : List Link) (B : Cfg) :
      Integrable (fun A : Cfg =>
        φ A * ((xs.map fun e => E ((A e)⁻¹ * B e)).sum)) haar :=
    (hφ.mul (hSum xs B)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntZero (xs : List Link) :
      Integrable (fun A : Cfg =>
        φ A * ((xs.map fun e => E ((A e)⁻¹)).sum)) haar := by
    simpa only [Pi.one_apply, mul_one] using (hInt xs (fun _ => (1 : G)))
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, mul_add]
      have hSingleB :
          Integrable (fun A : Cfg => φ A * E ((A e)⁻¹ * B e)) haar :=
        (hφ.mul (hEc e B)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hSingleZero :
          Integrable (fun A : Cfg => φ A * E ((A e)⁻¹)) haar := by
        simpa only [Pi.one_apply, mul_one] using
          ((hφ.mul (hEc e (fun _ => (1 : G)))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
      have hSplitB :
          (∫ A : Cfg, φ A * E ((A e)⁻¹ * B e) +
            φ A * ((es.map fun e => E ((A e)⁻¹ * B e)).sum) ∂haar) =
          (∫ A : Cfg, φ A * E ((A e)⁻¹ * B e) ∂haar) +
          (∫ A : Cfg, φ A * ((es.map fun e => E ((A e)⁻¹ * B e)).sum) ∂haar) := by
        simpa only [Pi.add_apply] using (integral_add hSingleB (hInt es B))
      have hSplitZero :
          (∫ A : Cfg, φ A * E ((A e)⁻¹) +
            φ A * ((es.map fun e => E ((A e)⁻¹)).sum) ∂haar) =
          (∫ A : Cfg, φ A * E ((A e)⁻¹) ∂haar) +
          (∫ A : Cfg, φ A * ((es.map fun e => E ((A e)⁻¹)).sum) ∂haar) := by
        simpa only [Pi.add_apply] using (integral_add hSingleZero (hIntZero es))
      rw [hSplitB, hSplitZero,
        p4Q2PT_originalGaugeWeight_singleLinkHaar_invariant
          H φ hφ hGauge e B, ih]

/-- Gauge-invariant weights give a boundary-independent genuine
temporal crossing action Haar integral on the ORIGINAL slice. -/
theorem p4Q2PT_originalGaugeWeight_crossingHaar_invariant
    (φ : Cfg → ℝ) (hφ : Continuous φ)
    (hGauge : ∀ (γ : Gauge) (A : Cfg),
      φ (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) =
        φ A)
    (B : Cfg) :
    (∫ A : Cfg, φ A * Cross A B ∂haar) =
      (∫ A : Cfg, φ A * Cross A (fun _ => 1) ∂haar) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  simpa only [Pi.one_apply, mul_one] using
    (p4Q2PT_originalGaugeWeight_finiteLinkHaar_invariant H φ hφ hGauge
      (periodicHypercubicEvenSpatialSliceLinkList H) B)

/-- Gauge invariance of the ORIGINAL action second moment:
the Haar-integration variable X is genuinely transformed along
with the right spatial boundary B, and Haar is preserved. -/
theorem p4Q2PT_originalSecondMoment_gaugeInvariant
    (γ : Gauge) (B : Cfg) :
    b (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ B) =
      b B := by
  let T : Cfg → Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  have hPres : MeasurePreserving T haar haar :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H 2 γ
  have hPair : Continuous (fun X : Cfg => (X, T B)) :=
    continuous_id.prodMk continuous_const
  have hS :
      Continuous (fun X : Cfg => S X (T B)) := by
    have hCont := (p4Q2IW_originalWilsonOneSlabAction_continuous H).comp hPair
    simpa only [Function.comp_def] using hCont
  let f : Cfg → ℝ := fun X => (S X (T B)) ^ 2
  have hf : AEStronglyMeasurable f haar :=
    (hS.pow 2).measurable.aestronglyMeasurable
  have hmap : Measure.map T haar = haar := hPres.map_eq
  have hfm : AEStronglyMeasurable f (Measure.map T haar) := by
    rw [hmap]
    exact hf
  change (∫ X : Cfg, (S X (T B)) ^ 2 ∂haar) =
    (∫ X : Cfg, (S X B) ^ 2 ∂haar)
  calc
    (∫ X : Cfg, (S X (T B)) ^ 2 ∂haar) =
        ∫ X : Cfg, f X ∂haar := rfl
    _ = ∫ X : Cfg, f X ∂Measure.map T haar := by rw [hmap]
    _ = ∫ X : Cfg, f (T X) ∂haar :=
      MeasureTheory.integral_map hPres.measurable.aemeasurable hfm
    _ = ∫ X : Cfg, (S X B) ^ 2 ∂haar := by
      apply integral_congr_ae
      filter_upwards with X
      change (S (T X) (T B)) ^ 2 = (S X B) ^ 2
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_gaugeInvariant
        H 2 γ X B]

/-- The genuine second one-slab Haar action moment is continuous
in the physical right SU(2) spatial boundary. -/
theorem p4Q2PT_originalSecondMoment_continuous :
    Continuous (fun B : Cfg => b B) := by
  let f : C(Cfg × Cfg, ℝ) :=
    ⟨(fun p => (S p.1 p.2) ^ 2),
      (p4Q2IW_originalWilsonOneSlabAction_continuous H).pow 2⟩
  let v : C(Cfg, C(Cfg, ℝ)) := f.curry
  have hv : Integrable (fun A : Cfg => v A) haar :=
    v.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfun :
      (fun B : Cfg => ∫ A : Cfg, f (A, B) ∂haar) =
        (fun B : Cfg => (∫ A : Cfg, v A ∂haar) B) := by
    funext B
    rw [ContinuousMap.integral_apply hv B]
    rfl
  have hCont : Continuous (fun B : Cfg => ∫ A : Cfg, f (A, B) ∂haar) := by
    rw [hfun]
    exact (∫ A : Cfg, v A ∂haar).continuous
  change Continuous (fun B : Cfg => b B) at hCont
  exact hCont

/-- The exact PS weight of the single-crossing coefficient.
The full left spatial Wilson action w(A) is NOT discarded. -/
noncomputable def p4Q2PT_originalSingleCrossingWardWeight (A : Cfg) : ℝ :=
  2 * w A * h A - b A

local notation "k" => p4Q2PT_originalSingleCrossingWardWeight H

theorem p4Q2PT_originalSingleCrossingWardWeight_continuous :
    Continuous (fun A : Cfg => k A) := by
  have hW : Continuous (fun A : Cfg => w A) := by
    change Continuous (fun A : Cfg => (1 / 2 : ℝ) * W A)
    exact continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)
  have ha : Continuous (fun A : Cfg => a A) := by
    have heq : (fun A : Cfg => a A) =
        fun A : Cfg =>
          -(1 / 2 : ℝ) * W A -
            p4Q2JE_originalWilsonHaarZeroDerivativeConstant H := by
      funext A
      exact p4Q2PM_originalFirstMoment_spatialWilson H A
    rw [heq]
    exact (continuous_const.mul
      (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2)).sub
      continuous_const
  have hh : Continuous (fun A : Cfg => h A) := by
    change Continuous (fun A : Cfg =>
      a A - p4Q2PQ_originalFirstActionMean H)
    exact ha.sub continuous_const
  have hb : Continuous (fun A : Cfg => b A) :=
    p4Q2PT_originalSecondMoment_continuous H
  change Continuous (fun A : Cfg => 2 * w A * h A - b A)
  exact ((continuous_const.mul hW).mul hh).sub hb

theorem p4Q2PT_originalSingleCrossingWardWeight_gaugeInvariant
    (γ : Gauge) (A : Cfg) :
    k (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ A) =
      k A := by
  let T : Cfg → Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  have hW :
      w (T A) = w A := by
    change (1 / 2 : ℝ) * W (T A) = (1 / 2 : ℝ) * W A
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 γ A]
  have hH :
      h (T A) = h A := by
    change a (T A) - p4Q2PQ_originalFirstActionMean H =
      a A - p4Q2PQ_originalFirstActionMean H
    rw [p4Q2PM_originalFirstMoment_spatialWilson H (T A),
      p4Q2PM_originalFirstMoment_spatialWilson H A,
      periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
        H 2 γ A]
  have hB : b (T A) = b A :=
    p4Q2PT_originalSecondMoment_gaugeInvariant H γ A
  unfold p4Q2PT_originalSingleCrossingWardWeight
  rw [hW, hH, hB]

/-- The FULL original PS weight has a boundary-independent genuine
single-crossing Haar integral, with no independence assumption. -/
theorem p4Q2PT_originalSingleCrossingWardHaar_invariant (B : Cfg) :
    (∫ A : Cfg, k A * Cross A B ∂haar) =
      (∫ A : Cfg, k A * Cross A (fun _ => 1) ∂haar) := by
  exact p4Q2PT_originalGaugeWeight_crossingHaar_invariant H k
    (p4Q2PT_originalSingleCrossingWardWeight_continuous H)
    (p4Q2PT_originalSingleCrossingWardWeight_gaugeInvariant H) B

end GenuineGaugeWeightedSingleCrossing
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT_originalGaugeWeight_singleLinkHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT_originalGaugeWeight_finiteLinkHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT_originalGaugeWeight_crossingHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT_originalSecondMoment_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT_originalSecondMoment_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT_originalSingleCrossingWardWeight_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT_originalSingleCrossingWardWeight_gaugeInvariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PT_originalSingleCrossingWardHaar_invariant
