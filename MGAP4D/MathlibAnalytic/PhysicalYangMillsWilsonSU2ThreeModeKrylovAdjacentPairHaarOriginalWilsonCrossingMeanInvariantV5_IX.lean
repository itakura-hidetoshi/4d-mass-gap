import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonHaarBetaDerivativeSplitV5_IW
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitarySpatialSliceGaugeAction
import Mathlib.Tactic

/-!
# P4-Q2-IX — literal temporal Wilson crossing Haar mean is right-boundary independent

Prove a new **actual physical product-Haar** measure-preserving translation on
every spatial-slice link, then exactly cancel the right SU(2) boundary in the
original temporal crossing action. The measure is the true finite normalized
Haar on independent SU(2) spatial links, not the interacting Wilson posterior
and not the outer comparison pair-Haar of the GI detector.

Consequently the crossing-action left-Haar average is independent of the right
boundary. Combining this with P4-Q2-IW gives an exact spatial-plaquette-only
formula for the difference of beta-zero derivatives of two literal Wilson rows.

To turn this into small-positive-beta nonconstancy one still needs to construct
two genuine right boundaries with different spatial Wilson action.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IX_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IX_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IX_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IX_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IX_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2IX_spatialLinksFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A deliberately small, universe-polymorphic Haar transport lemma.  The
kernel reduction of the full lattice Wilson action is kept outside the proof
of the Bochner integral transport itself. -/
private theorem p4Q2IX_abstract_integral_transport
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (f g : X → ℝ) (hfg : ∀ x, f (T x) = g x) :
    (∫ x, f x ∂μ) = (∫ x, g x ∂μ) := by
  calc
    (∫ x, f x ∂μ) = (∫ x, f (T x) ∂μ) :=
      (hT.integral_comp' f).symm
    _ = (∫ x, g x ∂μ) := by
      apply integral_congr_ae
      filter_upwards with x
      exact hfg x

section GenuineWilsonCrossing

variable (H : ℕ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "W" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "C" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2

/-- Coordinatewise LEFT multiplication by the literal right-boundary link
variables preserves the entire genuine normalized SU(2) spatial-slice Haar
product. No gauge symmetry of the right boundary is required. -/
theorem p4Q2IX_actualSpatialHaar_leftTranslate_measurePreserving (B : Cfg) :
    MeasurePreserving
      (fun A : Cfg => fun e => B e * A e) haar haar := by
  let G := Matrix.specialUnitaryGroup (Fin 2) ℂ
  let fac : Measure G := normalizedCompactHaar G
  let f : PeriodicHypercubicEvenSpatialSliceLink H → G → G :=
    fun e x => B e * x
  have hEach (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      MeasurePreserving (f e) fac fac := by
    simpa [f, fac] using
      (normalizedCompactHaar_measurePreserving_mul_left_right
        G (B e) 1)
  have hMeas : ∀ e, AEMeasurable (f e) fac :=
    fun e => (hEach e).measurable.aemeasurable
  letI : ∀ e, SigmaFinite (Measure.map (f e) fac) :=
    fun e => by
      rw [(hEach e).map_eq]
      infer_instance
  refine ⟨?_, ?_⟩
  · fun_prop
  · unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    change Measure.map (fun A : Cfg => fun e => f e (A e))
      (Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => fac)) =
      Measure.pi (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => fac)
    rw [Measure.pi_map_pi hMeas]
    congr 1
    funext e
    exact (hEach e).map_eq

/-- Original temporal crossing action under the genuine Haar translation:
multiplying every left link by the corresponding right link cancels that right
link *exactly*, before taking either an integral or a derivative. -/
theorem p4Q2IX_originalCrossingAction_leftTranslate
    (B A : Cfg) :
    C (fun e => B e * A e) B = C A (fun _ => 1) := by
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction
  have hcancel (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      ((B e * A e)⁻¹ * B e) = (A e)⁻¹ := by
    group
  simp only [hcancel, mul_one]

/-- The left-Haar mean of the ACTUAL SU(2) temporal crossing action depends
on no right-boundary link at all: it equals the crossing mean at the literal
all-identity right boundary. -/
theorem p4Q2IX_originalCrossingAction_HaarMean_eq_identity
    (B : Cfg) :
    (∫ A : Cfg, C A B ∂haar) =
      (∫ A : Cfg, C A (fun _ => 1) ∂haar) := by
  let T : Cfg → Cfg := fun A e => B e * A e
  let f : Cfg → ℝ := fun A => C A B
  let g : Cfg → ℝ := fun A => C A (fun _ => 1)
  have hPres : MeasurePreserving T haar haar :=
    p4Q2IX_actualSpatialHaar_leftTranslate_measurePreserving H B
  have hPoint (A : Cfg) : f (T A) = g A :=
    p4Q2IX_originalCrossingAction_leftTranslate H B A
  exact p4Q2IX_abstract_integral_transport haar T hPres f g hPoint

/-- Two genuine physical right boundaries have exactly the same temporal
crossing Haar mean; this removes crossing dependence from the beta-zero
derivative difference in the next theorem. -/
theorem p4Q2IX_originalCrossingAction_HaarMean_eq
    (B₀ B₁ : Cfg) :
    (∫ A : Cfg, C A B₀ ∂haar) =
      (∫ A : Cfg, C A B₁ ∂haar) := by
  rw [p4Q2IX_originalCrossingAction_HaarMean_eq_identity H B₀,
    p4Q2IX_originalCrossingAction_HaarMean_eq_identity H B₁]

/-- At beta=0, the difference of the TRUE Wilson Haar-row derivatives is
exactly minus one half of the spatial plaquette Wilson-energy difference,
with the crossing term rigorously cancelled by physical Haar invariance. -/
theorem p4Q2IX_originalWilsonTwoRowDifference_hasDerivAt_zero
    (B₀ B₁ : Cfg) :
    HasDerivAt
      (fun beta : ℝ =>
        p4Q2IV_originalWilsonUnitHaarKernelSection H beta B₀ -
          p4Q2IV_originalWilsonUnitHaarKernelSection H beta B₁)
      (-(1 / 2 : ℝ) * (W B₀ - W B₁)) 0 := by
  have h₀ := p4Q2IW_originalWilsonHaarRow_hasDerivAt_zero_explicit H B₀
  have h₁ := p4Q2IW_originalWilsonHaarRow_hasDerivAt_zero_explicit H B₁
  have hC : (∫ A : Cfg, C A B₀ ∂haar) =
      (∫ A : Cfg, C A B₁ ∂haar) :=
    p4Q2IX_originalCrossingAction_HaarMean_eq H B₀ B₁
  convert h₀.sub h₁ using 1
  rw [hC]
  ring

end GenuineWilsonCrossing
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IX_actualSpatialHaar_leftTranslate_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IX_originalCrossingAction_leftTranslate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IX_originalCrossingAction_HaarMean_eq_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IX_originalCrossingAction_HaarMean_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IX_originalWilsonTwoRowDifference_hasDerivAt_zero
