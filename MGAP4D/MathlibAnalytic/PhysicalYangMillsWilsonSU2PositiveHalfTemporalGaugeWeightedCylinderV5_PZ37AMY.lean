import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveTimeOneFiniteCylinderHaarV5_PZ37AMX
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderBetaDerivative
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMY — actual positive Wilson-weight temporal-gauge path cylinder

AMX constructs a concrete nonzero original time-one Wilson finite cylinder in
the spatial-path product-Haar L². This leaf applies the original POSITIVE
finite-temporal-gauge Wilson H+1 slab kernel as the exact ENNReal density of
that same path-Haar measure, then proves that the AMX time-one Wilson finite
cylinder does not disappear under the resulting *interacting* measure.

This is the unnormalized temporal-gauge positive-half path Wilson weight, NOT
the original full-periodic Gibbs probability, NOT a claim of equality to an
arbitrary abstract OS positive-time pullback, and NOT Wilson–OS gluing.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMY_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AMY_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AMY_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AMY_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AMY_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AMY_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- The exact original temporal-gauge Wilson positive-half path kernel,
regarded as an ENNReal density on its original product spatial Haar path. -/
noncomputable def p4Q2PZ37AMY_originalTemporalGaugePathDensity
    (H : ℕ) (beta : ℝ) :
    PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 → ENNReal :=
  fun path =>
    ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        H 2 beta path)

/-- The density is measurable on the native finite temporal-gauge path. -/
theorem p4Q2PZ37AMY_originalTemporalGaugePathDensity_measurable
    (H : ℕ) (beta : ℝ) :
    Measurable (p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta) := by
  exact ENNReal.measurable_ofReal.comp
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_measurable
      H 2 beta)

/-- Original finite Wilson half-path weight is nonzero at every path,
regardless of real beta, by strict positivity of its genuine Boltzmann kernel. -/
theorem p4Q2PZ37AMY_originalTemporalGaugePathDensity_ne_zero
    (H : ℕ) (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2) :
    p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta path ≠ 0 := by
  unfold p4Q2PZ37AMY_originalTemporalGaugePathDensity
  rw [ENNReal.ofReal_ne_zero_iff]
  exact periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_pos
    H 2 beta path

/-- The original finite positive-half temporal-gauge Wilson interaction
measure is the exact Wilson-kernel weighted original spatial-path Haar.
This is intentionally unnormalized; no full-periodic Gibbs equality. -/
noncomputable def p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure
    (H : ℕ) (beta : ℝ) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2) :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2).withDensity
    (p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta)

/-- The strictly positive genuine Wilson path density cannot introduce a
new null set. The reference path Haar is absolutely continuous with respect
to the original temporal-gauge weighted path measure. -/
theorem p4Q2PZ37AMY_originalPathHaar_ac_weightedWilson
    (H : ℕ) (beta : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2 ≪
      p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure H beta := by
  let ρ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2
  let w := p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta
  have hw : AEMeasurable w ρ :=
    (p4Q2PZ37AMY_originalTemporalGaugePathDensity_measurable H beta).aemeasurable
  have hw0 : ∀ᵐ path ∂ρ, w path ≠ 0 :=
    Filter.Eventually.of_forall
      (p4Q2PZ37AMY_originalTemporalGaugePathDensity_ne_zero H beta)
  simpa [p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure, ρ, w] using
    (withDensity_absolutelyContinuous' hw hw0)

/-- The positive temporal-gauge Wilson weight also cannot create any
positive-mass sets from a Haar-null set. -/
theorem p4Q2PZ37AMY_weightedWilson_ac_originalPathHaar
    (H : ℕ) (beta : ℝ) :
    p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure H beta ≪
      periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2 := by
  unfold p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure
  exact withDensity_absolutelyContinuous _ _

/-- The actual AMX nonzero time-one Wilson cylinder remains nonzero under
the true interacting finite temporal-gauge Wilson path weight, without any
assumed norm equivalence or OS-positive-time surjectivity. -/
theorem p4Q2PZ37AMY_exists_nonzero_weighted_originalWilsonTimeOneCylinder
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ c0 c1 : ℝ,
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by norm_num) beta hbeta ∧
      ¬ ((fun path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 =>
            c0 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
              (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
                (path (p4Q2PZ37AMX_positiveTimeOne H))) +
            c1 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
              (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
                (path (p4Q2PZ37AMX_positiveTimeOne H)))) =ᵐ[
        p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure H beta]
          (fun _ => (0 : ℝ))) := by
  obtain ⟨c0, c1, hTop, hNonzero, hRep⟩ :=
    p4Q2PZ37AMX_exists_nonzero_oneStepPositiveHalfWilsonCylinder H beta hbeta
  let ρ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2
  let ν := p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure H beta
  let f : Lp ℝ 2 ρ :=
    p4Q2PZ37AMX_positiveTimeOneL2Pullback H
      ((c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
        Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
  let g : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 → ℝ :=
    fun path =>
      c0 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
          (path (p4Q2PZ37AMX_positiveTimeOne H))) +
      c1 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
          (path (p4Q2PZ37AMX_positiveTimeOne H)))
  have hfne : f ≠ 0 := by
    simpa [f, ρ] using hNonzero
  have hRepRho : f =ᵐ[ρ] g := by
    simpa [f, g, ρ] using hRep
  have hRhoAc : ρ ≪ ν := by
    exact p4Q2PZ37AMY_originalPathHaar_ac_weightedWilson H beta
  have hNeRho : ¬ (f =ᵐ[ρ] (fun _ => (0 : ℝ))) := by
    intro hz
    apply hfne
    exact Lp.eq_zero_iff_ae_eq_zero.mpr hz
  refine ⟨c0, c1, hTop, ?_⟩
  intro hgZero
  have hgZeroNu : g =ᵐ[ν] (fun _ => (0 : ℝ)) := by
    simpa [g, ν] using hgZero
  have hgZeroRho : g =ᵐ[ρ] (fun _ => (0 : ℝ)) :=
    hRhoAc.ae_eq hgZeroNu
  exact hNeRho (hRepRho.trans hgZeroRho)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMY_originalTemporalGaugePathDensity_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMY_originalTemporalGaugePathDensity_ne_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMY_originalPathHaar_ac_weightedWilson
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMY_weightedWilson_ac_originalPathHaar
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMY_exists_nonzero_weighted_originalWilsonTimeOneCylinder
