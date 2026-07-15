import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedBoundedTestInfluence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- The exact normalized one-link Haar density at a fixed background is
measurable in the inserted compact-group value. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measurable (C.singleLinkConditionalDensity target A) := by
  exact
    (measurable_compact_oriented_singleLinkConditionalDensity_uncurry
      C target).comp (measurable_const.prodMk measurable_id)

/-- Pointwise common density of two exact one-link Haar conditional laws. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ≥0∞ :=
  min (C.singleLinkConditionalDensity target A g)
    (C.singleLinkConditionalDensity target B g)

/-- Left density left after removing the common overlap. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ≥0∞ :=
  C.singleLinkConditionalDensity target A g -
    C.singleLinkConditionalOverlapDensity A B target g

/-- Right density left after removing the common overlap. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalRightResidualDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ≥0∞ :=
  C.singleLinkConditionalDensity target B g -
    C.singleLinkConditionalOverlapDensity A B target g

/-- The common overlap density is measurable. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapDensity_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measurable (C.singleLinkConditionalOverlapDensity A B target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapDensity
  exact
    (continuous_compact_oriented_singleLinkConditionalDensity_measurable
      C A target).min
      (continuous_compact_oriented_singleLinkConditionalDensity_measurable
        C B target)

/-- The left residual density is measurable. -/
theorem continuous_compact_oriented_singleLinkConditionalLeftResidualDensity_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measurable (C.singleLinkConditionalLeftResidualDensity A B target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualDensity
  exact
    (continuous_compact_oriented_singleLinkConditionalDensity_measurable
      C A target).sub
      (continuous_compact_oriented_singleLinkConditionalOverlapDensity_measurable
        C A B target)

/-- The right residual density is measurable. -/
theorem continuous_compact_oriented_singleLinkConditionalRightResidualDensity_measurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measurable (C.singleLinkConditionalRightResidualDensity A B target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalRightResidualDensity
  exact
    (continuous_compact_oriented_singleLinkConditionalDensity_measurable
      C B target).sub
      (continuous_compact_oriented_singleLinkConditionalOverlapDensity_measurable
        C A B target)

/-- Common-overlap plus left residual recovers the left conditional density. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapDensity_add_leftResidual
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalOverlapDensity A B target g +
        C.singleLinkConditionalLeftResidualDensity A B target g =
      C.singleLinkConditionalDensity target A g := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapDensity
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualDensity
  exact add_tsub_of_le (min_le_left _ _)

/-- Common-overlap plus right residual recovers the right conditional density. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapDensity_add_rightResidual
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkConditionalOverlapDensity A B target g +
        C.singleLinkConditionalRightResidualDensity A B target g =
      C.singleLinkConditionalDensity target B g := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapDensity
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalRightResidualDensity
  exact add_tsub_of_le (min_le_right _ _)

/-- Common subprobability measure of two exact conditional laws. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) : Measure C.base.Gauge :=
  (normalizedCompactHaar C.base.Gauge).withDensity
    (C.singleLinkConditionalOverlapDensity A B target)

/-- Left residual conditional measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) : Measure C.base.Gauge :=
  (normalizedCompactHaar C.base.Gauge).withDensity
    (C.singleLinkConditionalLeftResidualDensity A B target)

/-- Right residual conditional measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalRightResidualMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) : Measure C.base.Gauge :=
  (normalizedCompactHaar C.base.Gauge).withDensity
    (C.singleLinkConditionalRightResidualDensity A B target)

/-- Exact left conditional law decomposes into common overlap plus left residual. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_leftResidual
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalOverlapMeasure A B target +
        C.singleLinkConditionalLeftResidualMeasure A B target =
      C.singleLinkConditionalMeasure A target := by
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalLeftResidualMeasure
  rw [← withDensity_add_left
    (continuous_compact_oriented_singleLinkConditionalOverlapDensity_measurable
      C A B target)]
  apply withDensity_congr_ae
  filter_upwards [] with g
  exact
    continuous_compact_oriented_singleLinkConditionalOverlapDensity_add_leftResidual
      C A B target g

/-- Exact right conditional law decomposes into common overlap plus right residual. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_rightResidual
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalOverlapMeasure A B target +
        C.singleLinkConditionalRightResidualMeasure A B target =
      C.singleLinkConditionalMeasure B target := by
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalRightResidualMeasure
  rw [← withDensity_add_left
    (continuous_compact_oriented_singleLinkConditionalOverlapDensity_measurable
      C A B target)]
  apply withDensity_congr_ae
  filter_upwards [] with g
  exact
    continuous_compact_oriented_singleLinkConditionalOverlapDensity_add_rightResidual
      C A B target g

/-- The common overlap measure is finite. -/
instance continuousCompactOriented_singleLinkConditionalOverlapMeasure_isFinite
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    IsFiniteMeasure (C.singleLinkConditionalOverlapMeasure A B target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  apply isFiniteMeasure_of_le (C.singleLinkConditionalMeasure A target)
  rw [← continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_leftResidual
    C A B target]
  exact Measure.le_add_right le_rfl

/-- The left residual measure is finite. -/
instance continuousCompactOriented_singleLinkConditionalLeftResidualMeasure_isFinite
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    IsFiniteMeasure (C.singleLinkConditionalLeftResidualMeasure A B target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  apply isFiniteMeasure_of_le (C.singleLinkConditionalMeasure A target)
  rw [← continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_leftResidual
    C A B target]
  exact Measure.le_add_left le_rfl

/-- The right residual measure is finite. -/
instance continuousCompactOriented_singleLinkConditionalRightResidualMeasure_isFinite
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    IsFiniteMeasure (C.singleLinkConditionalRightResidualMeasure A B target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure B target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C B target
  apply isFiniteMeasure_of_le (C.singleLinkConditionalMeasure B target)
  rw [← continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_rightResidual
    C A B target]
  exact Measure.le_add_left le_rfl

/-- The two residual measures have exactly the same total mass. -/
theorem continuous_compact_oriented_singleLinkConditionalResidualMeasure_univ_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalLeftResidualMeasure A B target univ =
      C.singleLinkConditionalRightResidualMeasure A B target univ := by
  let overlap := C.singleLinkConditionalOverlapMeasure A B target
  let left := C.singleLinkConditionalLeftResidualMeasure A B target
  let right := C.singleLinkConditionalRightResidualMeasure A B target
  have hLeft : overlap univ + left univ = 1 := by
    rw [show overlap + left = C.singleLinkConditionalMeasure A target by
      simpa [overlap, left] using
        continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_leftResidual
          C A B target]
    letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
      continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
        C A target
    exact measure_univ
  have hRight : overlap univ + right univ = 1 := by
    rw [show overlap + right = C.singleLinkConditionalMeasure B target by
      simpa [overlap, right] using
        continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_rightResidual
          C A B target]
    letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure B target) :=
      continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
        C B target
    exact measure_univ
  have hOverlapTop : overlap univ ≠ ∞ := by
    exact measure_ne_top overlap univ
  apply (add_right_inj_of_ne_top hOverlapTop).mp
  exact hLeft.trans hRight.symm

/-- Total unmatched mass in the exact conditional overlap decomposition. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalResidualMass
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ≥0∞ :=
  C.singleLinkConditionalLeftResidualMeasure A B target univ

/-- The right residual total mass is the named unmatched mass. -/
theorem continuous_compact_oriented_singleLinkConditionalRightResidualMeasure_univ
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalRightResidualMeasure A B target univ =
      C.singleLinkConditionalResidualMass A B target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalResidualMass
  exact
    (continuous_compact_oriented_singleLinkConditionalResidualMeasure_univ_eq
      C A B target).symm

/-- The unmatched conditional mass is finite. -/
theorem continuous_compact_oriented_singleLinkConditionalResidualMass_ne_top
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalResidualMass A B target ≠ ∞ := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalResidualMass
  exact measure_ne_top _ _

/-- Exact overlap coupling of two one-link compact-Haar conditional laws.
The common mass is coupled diagonally; if unmatched mass is nonzero, the two
residual laws are coupled by their normalized product. -/
noncomputable def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) : Measure (C.base.Gauge × C.base.Gauge) :=
  Measure.map (fun g : C.base.Gauge => (g, g))
      (C.singleLinkConditionalOverlapMeasure A B target) +
    if C.singleLinkConditionalResidualMass A B target = 0 then 0 else
      (C.singleLinkConditionalResidualMass A B target)⁻¹ •
        ((C.singleLinkConditionalLeftResidualMeasure A B target).prod
          (C.singleLinkConditionalRightResidualMeasure A B target))

/-- The first marginal of the overlap coupling is the exact left conditional law. -/
theorem continuous_compact_oriented_map_fst_singleLinkConditionalOverlapCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.fst
        (C.singleLinkConditionalOverlapCouplingMeasure A B target) =
      C.singleLinkConditionalMeasure A target := by
  let overlap := C.singleLinkConditionalOverlapMeasure A B target
  let left := C.singleLinkConditionalLeftResidualMeasure A B target
  let right := C.singleLinkConditionalRightResidualMeasure A B target
  let delta := C.singleLinkConditionalResidualMass A B target
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapCouplingMeasure
  rw [Measure.map_add _ _ measurable_fst,
    Measure.map_map measurable_fst (measurable_id.prodMk measurable_id)]
  simp only [Function.comp_apply]
  rw [Measure.map_id']
  by_cases hdelta : delta = 0
  · rw [if_pos hdelta]
    have hLeftZero : left = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      simpa [delta,
        ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalResidualMass]
        using hdelta
    simpa [overlap, left, hLeftZero] using
      continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_leftResidual
        C A B target
  · rw [if_neg hdelta, Measure.map_smul, Measure.map_fst_prod]
    rw [show right univ = delta by
      simpa [right, delta] using
        continuous_compact_oriented_singleLinkConditionalRightResidualMeasure_univ
          C A B target]
    rw [smul_smul,
      ENNReal.inv_mul_cancel hdelta
        (continuous_compact_oriented_singleLinkConditionalResidualMass_ne_top
          C A B target),
      one_smul]
    simpa [overlap, left] using
      continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_leftResidual
        C A B target

/-- The second marginal of the overlap coupling is the exact right conditional law. -/
theorem continuous_compact_oriented_map_snd_singleLinkConditionalOverlapCouplingMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure.map Prod.snd
        (C.singleLinkConditionalOverlapCouplingMeasure A B target) =
      C.singleLinkConditionalMeasure B target := by
  let overlap := C.singleLinkConditionalOverlapMeasure A B target
  let left := C.singleLinkConditionalLeftResidualMeasure A B target
  let right := C.singleLinkConditionalRightResidualMeasure A B target
  let delta := C.singleLinkConditionalResidualMass A B target
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapCouplingMeasure
  rw [Measure.map_add _ _ measurable_snd,
    Measure.map_map measurable_snd (measurable_id.prodMk measurable_id)]
  simp only [Function.comp_apply]
  rw [Measure.map_id']
  by_cases hdelta : delta = 0
  · rw [if_pos hdelta]
    have hRightZero : right = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      rw [show right univ = delta by
        simpa [right, delta] using
          continuous_compact_oriented_singleLinkConditionalRightResidualMeasure_univ
            C A B target]
      exact hdelta
    simpa [overlap, right, hRightZero] using
      continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_rightResidual
        C A B target
  · rw [if_neg hdelta, Measure.map_smul, Measure.map_snd_prod]
    rw [show left univ = delta by rfl]
    rw [smul_smul,
      ENNReal.inv_mul_cancel hdelta
        (continuous_compact_oriented_singleLinkConditionalResidualMass_ne_top
          C A B target),
      one_smul]
    simpa [overlap, right] using
      continuous_compact_oriented_singleLinkConditionalOverlapMeasure_add_rightResidual
        C A B target

/-- The exact conditional overlap coupling is a probability measure. -/
instance continuousCompactOriented_singleLinkConditionalOverlapCouplingMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.singleLinkConditionalOverlapCouplingMeasure A B target) := by
  constructor
  calc
    C.singleLinkConditionalOverlapCouplingMeasure A B target univ =
        Measure.map Prod.fst
          (C.singleLinkConditionalOverlapCouplingMeasure A B target) univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]
      rfl
    _ = C.singleLinkConditionalMeasure A target univ := by
      rw [continuous_compact_oriented_map_fst_singleLinkConditionalOverlapCouplingMeasure]
    _ = 1 := by
      letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
        continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
          C A target
      exact measure_univ

/-- Under the exact overlap coupling, the probability of unequal target-link
values is at most the unmatched residual mass. -/
theorem continuous_compact_oriented_singleLinkConditionalOverlapCouplingMeasure_ne_diagonal_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalOverlapCouplingMeasure A B target
        {z | z.1 ≠ z.2} ≤
      C.singleLinkConditionalResidualMass A B target := by
  let overlap := C.singleLinkConditionalOverlapMeasure A B target
  let left := C.singleLinkConditionalLeftResidualMeasure A B target
  let right := C.singleLinkConditionalRightResidualMeasure A B target
  let delta := C.singleLinkConditionalResidualMass A B target
  have hNe : MeasurableSet {z : C.base.Gauge × C.base.Gauge | z.1 ≠ z.2} :=
    (isClosed_eq continuous_fst continuous_snd).isOpen_compl.measurableSet
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapCouplingMeasure
  rw [Measure.add_apply hNe]
  have hDiagonalZero :
      Measure.map (fun g : C.base.Gauge => (g, g)) overlap
          {z | z.1 ≠ z.2} = 0 := by
    rw [Measure.map_apply (measurable_id.prodMk measurable_id) hNe]
    simp
  rw [hDiagonalZero, zero_add]
  by_cases hdelta : delta = 0
  · rw [if_pos hdelta]
    simp [hdelta]
  · rw [if_neg hdelta, Measure.smul_apply, smul_eq_mul]
    calc
      delta⁻¹ * (left.prod right) {z | z.1 ≠ z.2} ≤
          delta⁻¹ * (left.prod right) univ := by
        gcongr
        exact measure_mono (subset_univ _)
      _ = delta := by
        rw [← univ_prod_univ, Measure.prod_prod,
          show left univ = delta by rfl,
          show right univ = delta by
            simpa [right, delta] using
              continuous_compact_oriented_singleLinkConditionalRightResidualMeasure_univ
                C A B target]
        calc
          delta⁻¹ * (delta * delta) = (delta⁻¹ * delta) * delta := by
            ac_rfl
          _ = delta := by
            rw [ENNReal.inv_mul_cancel hdelta
              (continuous_compact_oriented_singleLinkConditionalResidualMass_ne_top
                C A B target), one_mul]

end

end MathlibAnalytic
end MGAP4D
