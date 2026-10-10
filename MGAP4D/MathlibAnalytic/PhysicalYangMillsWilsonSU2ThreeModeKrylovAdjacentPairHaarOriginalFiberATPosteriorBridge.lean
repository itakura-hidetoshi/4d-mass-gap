import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarContinuousJointAEPosteriorFibers
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitDirectNormalizedFiberBridge
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureNormalizationIdentity
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Tactic

/-!
# P4-Q2-AW: exact original physical ground-state target fiber versus AT posterior

The original Wilson one-slab joint physical measure has been identified,
without proxy transfer operators, with its strictly positive continuous
physical-vacuum joint density (AU). Its normalized singleton-target
conditional fiber equals the continuous density fiber Haar-a.e. in its
left/off-target contexts (AV). Here we bridge the latter to the AS/AT
actual raw one-slab Wilson conditional followed by the genuine continuous
physical top-vacuum Doob weight.

A generic normalization composition identity is established with exact
extended-nonnegative masses. The original physical conditional cannot be
identified pointwise on all exceptional fixed fibers of the old L² vacuum;
the canonical continuous fiber can, and the original conditional agrees
a.e. via AV. The target measure is the existing singleton SU(N) carrier.

No uniform physical time-transfer gap or continuum mass gap is inferred.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Set
open ProbabilityTheory
open scoped ENNReal InnerProductSpace

noncomputable section
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 850000

/-- A nonzero finite overall scalar cancels in EXACT Doob normalization,
including if the unscaled normalization mass is degenerate. -/
theorem p4Q2AW_doobWeightedMeasure_mul_const
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (w : X → ENNReal) (c : ENNReal)
    (hw : AEMeasurable w mu)
    (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    doobWeightedMeasure mu (fun x => w x * c) =
      doobWeightedMeasure mu w := by
  have hm : doobWeightMass mu (fun x => w x * c) =
      doobWeightMass mu w * c := by
    change (∫⁻ x, w x * c ∂mu) = (∫⁻ x, w x ∂mu) * c
    exact lintegral_mul_const'' _ hw
  change mu.withDensity
      (fun x => (w x * c) / doobWeightMass mu (fun x => w x * c)) =
    mu.withDensity (fun x => w x / doobWeightMass mu w)
  apply withDensity_congr_ae
  filter_upwards [] with x
  rw [hm]
  exact ENNReal.mul_div_mul_right (w x) (doobWeightMass mu w) hc0 hctop

/-- EXACT associativity of successive normalization under two honest
one-link positive weights: two Doob steps produce one Doob step weighted
by their product. The first mass is assumed positive and finite to
legitimize division and cancellation. -/
theorem p4Q2AW_doobWeightedMeasure_assoc
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (w v : X → ENNReal)
    (hw : AEMeasurable w mu) (hv : AEMeasurable v mu)
    (hm0 : doobWeightMass mu w ≠ 0)
    (hmtop : doobWeightMass mu w ≠ ∞) :
    doobWeightedMeasure (doobWeightedMeasure mu w) v =
      doobWeightedMeasure mu (fun x => w x * v x) := by
  let m := doobWeightMass mu w
  let nu := doobWeightedMeasure mu w
  let m2 := doobWeightMass nu v
  have hmass : m * m2 = doobWeightMass mu (fun x => w x * v x) := by
    exact doobWeightMass_mul_lintegral_doobWeightedMeasure
      mu w v hw hv hm0 hmtop
  calc
    doobWeightedMeasure nu v =
        (mu.withDensity (fun x => w x / m)).withDensity
          (fun x => v x / m2) := rfl
    _ = mu.withDensity (fun x => (w x / m) * (v x / m2)) := by
      exact (withDensity_mul₀ (hw.div_const _) (hv.div_const _)).symm
    _ = mu.withDensity
        (fun x => (w x * v x) /
          doobWeightMass mu (fun y => w y * v y)) := by
      apply withDensity_congr_ae
      filter_upwards [] with x
      rw [← hmass]
      exact (ENNReal.mul_div_mul_comm (Or.inl hm0) (Or.inl hmtop)).symm
    _ = doobWeightedMeasure mu (fun x => w x * v x) := rfl

/-- The Mathlib exponential tilt by a truly integrable positive weight
equals the canonical normalized Doob measure of the SAME literal weight.
This is the exact bridge between AS's raw Wilson tilted law and the
existing physical-vacuum Doob posterior. -/
theorem p4Q2AW_doobExp_eq_tilted
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (f : X → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) mu) :
    doobWeightedMeasure mu
      (fun x => ENNReal.ofReal (Real.exp (f x))) =
      mu.tilted f := by
  have hZ : 0 < ∫ x, Real.exp (f x) ∂mu := integral_exp_pos hf
  have hmass :
      doobWeightMass mu (fun x => ENNReal.ofReal (Real.exp (f x))) =
        ENNReal.ofReal (∫ x, Real.exp (f x) ∂mu) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal hf
      (ae_of_all mu fun x => (Real.exp_pos _).le)
  change mu.withDensity
      (fun x => ENNReal.ofReal (Real.exp (f x)) /
        doobWeightMass mu (fun y => ENNReal.ofReal (Real.exp (f y)))) =
    mu.withDensity
      (fun x => ENNReal.ofReal
        (Real.exp (f x) / (∫ y, Real.exp (f y) ∂mu)))
  apply withDensity_congr_ae
  filter_upwards [] with x
  rw [hmass, ENNReal.ofReal_div_of_pos hZ]

/-- Exact pushforward of a normalized Doob fiber under an ACTUAL
measure-preserving target-variable measurable equivalence. The
normalizing mass is moved by the same equivalence, not assumed equal. -/
theorem p4Q2AW_measureMap_doobWeightedMeasure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (muX : Measure X) (muY : Measure Y)
    (he : MeasurePreserving e muX muY) (w : Y → ENNReal) :
    Measure.map e (doobWeightedMeasure muX (w ∘ e)) =
      doobWeightedMeasure muY w := by
  have hmass : doobWeightMass muX (w ∘ e) = doobWeightMass muY w := by
    change (∫⁻ x, w (e x) ∂muX) = ∫⁻ y, w y ∂muY
    exact he.lintegral_comp_emb e.measurableEmbedding w
  ext s hs
  rw [Measure.map_apply e.measurable hs]
  change
    (muX.withDensity
      (fun x => (w ∘ e) x / doobWeightMass muX (w ∘ e)))
      (e ⁻¹' s) =
    (muY.withDensity (fun y => w y / doobWeightMass muY w)) s
  rw [withDensity_apply _ (hs.preimage e.measurable), withDensity_apply _ hs]
  rw [hmass]
  exact he.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun y => w y / doobWeightMass muY w) s

end
end MathlibAnalytic
end MGAP4D
