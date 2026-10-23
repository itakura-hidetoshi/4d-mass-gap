import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonTwoSlabFineTaylorJetV5_PK
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeAction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import Mathlib.Tactic

/-!
# P4-Q2-PL — original SU(2) Wilson-weighted crossing Haar invariance

The original spatial plaquette action W(A), unlike a Wilson interacting
posterior substituted into the integral, is invariant under the ACTUAL
spatial vertex gauge transformations. The genuine spatial link product
Haar measure is preserved by the SAME gauge transformations.

For every link e=(v,dir), the target shifted vertex differs from v
in the even periodic lattice. A gauge transformation supported at the
source v can therefore left-translate A(e) by the arbitrary right
boundary link B(e), while leaving W(A) and Haar exactly unchanged.

It follows that the original W(A)-weighted Haar mean of EACH temporal
plaquette energy E(A(e)^(-1) B(e)) is B-independent, and so is the original
full temporal crossing energy sum. No free-link posterior replaces the
original interacting two-posterior GI response: this is a symmetry
of the *reference* Haar integration with the genuine spatial W factor.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators Topology

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PL_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PL_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PL_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PL_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PL_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PL_spatialLinksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section GenuineSpatialWilsonHaarGaugeWard
variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2

/-- Every actual spatial link has different source and target vertices,
including the smallest even periodic length 2. -/
theorem p4Q2PL_originalSpatialLink_target_ne_source
    (e : Link) :
    periodicHypercubicEvenSpatialSliceShift H e.1 e.2 ≠ e.1 := by
  intro h
  have heq :
      periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
        e.1.1 e.2.1 = e.1.1 := by
    exact congrArg Subtype.val h
  exact (periodicHypercubicShift_ne_self
    (PeriodicHypercubicEvenSideLength H)
    (by simp [PeriodicHypercubicEvenSideLength]; omega)
    e.1.1 e.2.1) heq

/-- The actual full spatial Wilson energy weighted by any one temporal
plaquette is independent of its chosen right-boundary SU(2) link. -/
theorem p4Q2PL_originalSpatialWilson_weightedSingleLinkHaar_invariant
    (e : Link) (B : Cfg) :
    (∫ A : Cfg, W A * E ((A e)⁻¹ * B e) ∂haar) =
      (∫ A : Cfg, W A * E ((A e)⁻¹) ∂haar) := by
  let γ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransformation H 2 :=
    fun v => if v = e.1 then B e else 1
  have hsrc : γ e.1 = B e := by simp [γ]
  have htar : γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2) = 1 := by
    simp [γ, p4Q2PL_originalSpatialLink_target_ne_source H e]
  let T : Cfg → Cfg :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeTransform H 2 γ
  have hPres : MeasurePreserving T haar haar :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaar_measurePreserving H 2 γ
  have hrel (A : Cfg) :
      ((T A e)⁻¹ * B e) = (A e)⁻¹ := by
    change
      ((γ e.1 * A e *
          (γ (periodicHypercubicEvenSpatialSliceShift H e.1 e.2))⁻¹)⁻¹ *
          B e) = (A e)⁻¹
    rw [hsrc, htar]
    group
  let f : Cfg → ℝ := fun A => W A * E ((A e)⁻¹ * B e)
  let g : Cfg → ℝ := fun A => W A * E ((A e)⁻¹)
  have hW : Continuous W :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  have hE : Continuous (fun A : Cfg => E ((A e)⁻¹ * B e)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_apply e).inv.mul continuous_const)
  have hf : AEStronglyMeasurable f haar :=
    (hW.mul hE).measurable.aestronglyMeasurable
  have hpoint (A : Cfg) : f (T A) = g A := by
    change W (T A) * E ((T A e)⁻¹ * B e) =
      W A * E ((A e)⁻¹)
    rw [periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_gaugeInvariant
      H 2 γ A, hrel A]
  have hmap : Measure.map T haar = haar := hPres.map_eq
  have hfm : AEStronglyMeasurable f (Measure.map T haar) := by
    rw [hmap]
    exact hf
  calc
    (∫ A : Cfg, W A * E ((A e)⁻¹ * B e) ∂haar) =
        ∫ A : Cfg, f A ∂haar := rfl
    _ = ∫ A : Cfg, f A ∂Measure.map T haar := by rw [hmap]
    _ = ∫ A : Cfg, f (T A) ∂haar :=
      MeasureTheory.integral_map hPres.measurable.aemeasurable hfm
    _ = ∫ A : Cfg, g A ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      exact hpoint A
    _ = (∫ A : Cfg, W A * E ((A e)⁻¹) ∂haar) := rfl

/-- Extend each genuine one-link Ward identity to an arbitrary finite
list of temporal plaquettes, retaining the full coupled spatial W(A).
No independence is assumed among plaquettes. -/
theorem p4Q2PL_originalSpatialWilson_weightedFiniteLinkHaar_invariant
    (es : List Link) (B : Cfg) :
    (∫ A : Cfg,
        W A * ((es.map fun e => E ((A e)⁻¹ * B e)).sum) ∂haar) =
      (∫ A : Cfg,
        W A * ((es.map fun e => E ((A e)⁻¹)).sum) ∂haar) := by
  have hW : Continuous W :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
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
        simpa only [List.map_cons, List.sum_cons] using
          (hEc e B).add ih
  have hInt (xs : List Link) (B : Cfg) :
      Integrable (fun A : Cfg =>
        W A * ((xs.map fun e => E ((A e)⁻¹ * B e)).sum)) haar :=
    (hW.mul (hSum xs B)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntZero (xs : List Link) :
      Integrable (fun A : Cfg =>
        W A * ((xs.map fun e => E ((A e)⁻¹)).sum)) haar := by
    simpa only [Pi.one_apply, mul_one] using
      (hInt xs (fun _ => (1 : G)))
  induction es with
  | nil => simp
  | cons e es ih =>
      simp only [List.map_cons, List.sum_cons, mul_add]
      rw [
        integral_add
          ((hW.mul (hEc e B)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)) (hInt es B),
        integral_add
          ((hW.mul (by
            simpa only [Pi.one_apply, mul_one] using
              (hEc e (fun _ => (1 : G))))).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)) (hIntZero es),
        p4Q2PL_originalSpatialWilson_weightedSingleLinkHaar_invariant H e B,
        ih]

/-- The ORIGINAL complete temporal crossing Wilson action's
spatial-Wilson-weighted *reference* Haar mean is exactly independent
of its genuine right spatial SU(2) boundary, by vertex gauge symmetry. -/
theorem p4Q2PL_originalSpatialWilson_weightedCrossingHaar_invariant
    (B : Cfg) :
    (∫ A : Cfg, W A * Cross A B ∂haar) =
      (∫ A : Cfg, W A * Cross A (fun _ => 1) ∂haar) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  simpa only [Pi.one_apply, mul_one] using
    (p4Q2PL_originalSpatialWilson_weightedFiniteLinkHaar_invariant H
      (periodicHypercubicEvenSpatialSliceLinkList H) B)

end GenuineSpatialWilsonHaarGaugeWard
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PL_originalSpatialLink_target_ne_source
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PL_originalSpatialWilson_weightedSingleLinkHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PL_originalSpatialWilson_weightedFiniteLinkHaar_invariant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PL_originalSpatialWilson_weightedCrossingHaar_invariant
