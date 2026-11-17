import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveHalfTemporalGaugeWeightedCylinderV5_PZ37AMY
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureComparison
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMZ — normalized original positive-half Wilson cylinder probability

AMY constructs the true unnormalized original temporal-gauge positive-half
Wilson path law and proves that the actual physical time-one two-mode Wilson
cylinder is not almost-everywhere zero under that law.  The original
positive-half path Haar law is a probability measure, while the Wilson kernel
is everywhere positive and bounded above by one at beta >= 0.

This additive stage proves, on this *same finite lattice and path space*,
the positivity and finiteness of the original Wilson half-path partition
function, then constructs its exactly normalized probability law.  Finally,
the same concrete physical top-orthogonal time-one Wilson cylinder remains
not almost-everywhere zero under the normalized interacting law.

Neither the full periodic Wilson Gibbs law nor an abstract OS
positive-time observable is identified here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37AMZ_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37AMZ_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AMZ_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AMZ_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AMZ_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AMZ_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- At beta >= 0 the original temporal-gauge Wilson half-path density is
pointwise bounded by one, with no volume-uniform spectral assertion. -/
theorem p4Q2PZ37AMZ_originalPathDensity_le_one
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2) :
    p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta path ≤ 1 := by
  unfold p4Q2PZ37AMY_originalTemporalGaugePathDensity
  have h :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_le_one
      H 2 (by norm_num) beta hbeta path
  simpa using ENNReal.ofReal_le_ofReal h

/-- The genuine original positive-half Wilson partition function is
the exact ENNReal Haar integral of the temporal-gauge path weight. -/
noncomputable def p4Q2PZ37AMZ_originalHalfPathPartitionMass
    (H : ℕ) (beta : ℝ) : ℝ≥0∞ :=
  doobWeightMass
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2)
    (p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta)

/-- Its total mass is at most one at all nonnegative couplings. -/
theorem p4Q2PZ37AMZ_originalHalfPathPartitionMass_le_one
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    p4Q2PZ37AMZ_originalHalfPathPartitionMass H beta ≤ 1 := by
  unfold p4Q2PZ37AMZ_originalHalfPathPartitionMass
  exact doobWeightMass_upper_bound
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2)
    (p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta)
    1
    (p4Q2PZ37AMZ_originalPathDensity_le_one H beta hbeta)

/-- The original Wilson half-path partition mass is nonzero.  This uses
AMY's proven absolute continuity of the nonzero product-Haar law with
respect to its genuine strictly positive Wilson interaction law. -/
theorem p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_zero
    (H : ℕ) (beta : ℝ) :
    p4Q2PZ37AMZ_originalHalfPathPartitionMass H beta ≠ 0 := by
  let μ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2
  let w := p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta
  have hAc : μ ≪ μ.withDensity w := by
    simpa [μ, w, p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure] using
      p4Q2PZ37AMY_originalPathHaar_ac_weightedWilson H beta
  have hMass : (μ.withDensity w) Set.univ ≠ 0 := by
    intro hzero
    have hμzero : μ Set.univ = 0 := hAc hzero
    have hμone : μ Set.univ = 1 := by simp [μ]
    rw [hμone] at hμzero
    exact one_ne_zero hμzero
  have hEq :
      (μ.withDensity w) Set.univ = doobWeightMass μ w := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rfl
  change doobWeightMass μ w ≠ 0
  rw [← hEq]
  exact hMass

/-- The original Wilson half-path partition mass is finite at beta >= 0. -/
theorem p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_top
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    p4Q2PZ37AMZ_originalHalfPathPartitionMass H beta ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp)
    (p4Q2PZ37AMZ_originalHalfPathPartitionMass_le_one H beta hbeta)

/-- The actual interacting Wilson half-path measure is a finite measure,
before and independently of normalization. -/
theorem p4Q2PZ37AMZ_originalWeightedPath_isFiniteMeasure
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsFiniteMeasure (p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure H beta) := by
  change IsFiniteMeasure
    ((periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2).withDensity
      (p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta))
  exact isFiniteMeasure_withDensity
    (p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_top H beta hbeta)

/-- Precisely normalized interacting original positive-half Wilson path law,
distinct from any periodized Gibbs distribution or abstract OS state. -/
noncomputable def p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure
    (H : ℕ) (beta : ℝ) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2) :=
  doobWeightedMeasure
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2)
    (p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta)

/-- The normalized *original* interacting temporal-gauge path law has mass one. -/
theorem p4Q2PZ37AMZ_originalNormalizedHalfPath_isProbabilityMeasure
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure (p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta) := by
  let μ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2
  let w := p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta
  change IsProbabilityMeasure (doobWeightedMeasure μ w)
  refine ⟨doobWeightedMeasure_measure_univ μ w
    (p4Q2PZ37AMY_originalTemporalGaugePathDensity_measurable H beta).aemeasurable
    ?_ ?_⟩
  · exact p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_zero H beta
  · exact p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_top H beta hbeta

/-- The original product-path Haar measure is absolutely continuous with
respect to the exactly normalized positive Wilson half-path probability.
The normalization does not delete any nonzero path-Haar cylinder. -/
theorem p4Q2PZ37AMZ_originalPathHaar_ac_normalizedWilson
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2 ≪
      p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta := by
  let μ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2
  let w := p4Q2PZ37AMY_originalTemporalGaugePathDensity H beta
  let d := doobWeightedDensity μ w
  have hdMeas : AEMeasurable d μ := by
    dsimp [d, doobWeightedDensity]
    exact
      (p4Q2PZ37AMY_originalTemporalGaugePathDensity_measurable H beta).aemeasurable.div_const _
  have hdNonzero : ∀ᵐ path ∂μ, d path ≠ 0 := by
    filter_upwards with path
    change w path / doobWeightMass μ w ≠ 0
    exact (ENNReal.div_ne_zero).2
      ⟨p4Q2PZ37AMY_originalTemporalGaugePathDensity_ne_zero H beta path,
       p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_top H beta hbeta⟩
  change μ ≪ μ.withDensity d
  exact withDensity_absolutelyContinuous' hdMeas hdNonzero

/-- The SAME concrete original top-orthogonal physical two-mode time-one
Wilson cylinder is nonzero under the normalized interacting path probability.
Neither an OS positive-time subalgebra lift nor periodic Gibbs is presumed. -/
theorem p4Q2PZ37AMZ_exists_nonzero_normalized_originalWilsonTimeOneCylinder
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
        p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta]
          (fun _ => (0 : ℝ))) := by
  obtain ⟨c0, c1, hTop, hNonzero⟩ :=
    p4Q2PZ37AMY_exists_nonzero_weighted_originalWilsonTimeOneCylinder H beta hbeta
  let μ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2
  let ν := p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure H beta
  let νnorm := p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta
  let g : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 → ℝ :=
    fun path =>
      c0 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
          (path (p4Q2PZ37AMX_positiveTimeOne H))) +
      c1 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
        (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
          (path (p4Q2PZ37AMX_positiveTimeOne H)))
  have hμac : μ ≪ νnorm :=
    p4Q2PZ37AMZ_originalPathHaar_ac_normalizedWilson H beta hbeta
  have hνac : ν ≪ μ :=
    p4Q2PZ37AMY_weightedWilson_ac_originalPathHaar H beta
  refine ⟨c0, c1, hTop, ?_⟩
  intro hgZero
  have hNorm : g =ᵐ[νnorm] (fun _ => (0 : ℝ)) := by
    simpa [g, νnorm] using hgZero
  have hμ : g =ᵐ[μ] (fun _ => (0 : ℝ)) :=
    hμac.ae_eq hNorm
  have hν : g =ᵐ[ν] (fun _ => (0 : ℝ)) :=
    hνac.ae_eq hμ
  exact hNonzero (by simpa [g, ν] using hν)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMZ_originalPathDensity_le_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMZ_originalHalfPathPartitionMass_le_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMZ_originalHalfPathPartitionMass_ne_top
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMZ_originalWeightedPath_isFiniteMeasure
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMZ_originalNormalizedHalfPath_isProbabilityMeasure
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMZ_originalPathHaar_ac_normalizedWilson
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMZ_exists_nonzero_normalized_originalWilsonTimeOneCylinder
