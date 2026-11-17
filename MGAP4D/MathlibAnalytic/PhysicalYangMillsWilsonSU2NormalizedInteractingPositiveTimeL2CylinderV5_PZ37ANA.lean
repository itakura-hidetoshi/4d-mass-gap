import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedPositiveHalfTemporalGaugeCylinderV5_PZ37AMZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANA — actual nonzero normalized interacting Wilson time-one L² state

AMZ proves that the original finite SU(2) temporal-gauge positive-half
Wilson path density has positive finite mass, constructs the exactly normalized
interacting half-path probability and proves that the actual physical
top-orthogonal two-mode time-one cylinder is not almost-everywhere zero.

This stage proves that the SAME pointwise positive-time Wilson cylinder is
also a genuine element of real L² of the normalized interacting Wilson path
probability, and that its L² class is nonzero. No abstract OS carrier
is identified with this concrete finite path Hilbert space.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANA_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2PZ37ANA_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANA_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANA_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANA_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANA_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- The literal original time-one two-Wilson-mode cylinder on the genuine
positive-half temporal-gauge spatial path, with no replacement of its
spatial slice, coefficient functions or time-one index. -/
noncomputable def p4Q2PZ37ANA_timeOneTwoModeWilsonObservable
    (H : ℕ) (c0 c1 : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2) : ℝ :=
  c0 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
    (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
      (path (p4Q2PZ37AMX_positiveTimeOne H))) +
  c1 * specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
    (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
      (path (p4Q2PZ37AMX_positiveTimeOne H)))

/-- Measurability of the concrete cylinder from the existing exact Haar
measure-preserving spatial-slice holonomy and positive-time-one evaluation. -/
theorem p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_measurable
    (H : ℕ) (c0 c1 : ℝ) :
    Measurable (p4Q2PZ37ANA_timeOneTwoModeWilsonObservable H c0 c1) := by
  let e : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
    fun path => path (p4Q2PZ37AMX_positiveTimeOne H)
  let h : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 →
      Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 ∘ e
  have he : Measurable e :=
    (p4Q2PZ37AMX_positiveTimeOne_measurePreserving H).measurable
  have hh : Measurable h :=
    (p4Q2PZ37AMS_measurePreserving_primarySpatialSliceCyclicHolonomy H 2).measurable.comp he
  have h0 : Measurable (fun path =>
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0 (h path)) :=
    (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0).continuous.measurable.comp hh
  have h1 : Measurable (fun path =>
      specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1 (h path)) :=
    (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1).continuous.measurable.comp hh
  simpa [p4Q2PZ37ANA_timeOneTwoModeWilsonObservable, h, e, Function.comp_def] using
    (measurable_const.mul h0).add (measurable_const.mul h1)

/-- The two continuous Wilson-energy class functions give an actual global
finite bound for the SAME positive-time one cylinder (all real coefficients).
Only compactness of the original SU(2) group is used. -/
theorem p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_norm_le
    (H : ℕ) (c0 c1 : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2) :
    ‖p4Q2PZ37ANA_timeOneTwoModeWilsonObservable H c0 c1 path‖ ≤
      |c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
      |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖ := by
  let U := p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2
    (path (p4Q2PZ37AMX_positiveTimeOne H))
  let f0 := specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0
  let f1 := specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1
  have h0 : ‖f0 U‖ ≤ ‖f0‖ := f0.norm_coe_le_norm U
  have h1 : ‖f1 U‖ ≤ ‖f1‖ := f1.norm_coe_le_norm U
  change ‖c0 * f0 U + c1 * f1 U‖ ≤ |c0| * ‖f0‖ + |c1| * ‖f1‖
  calc
    ‖c0 * f0 U + c1 * f1 U‖ ≤
        ‖c0 * f0 U‖ + ‖c1 * f1 U‖ :=
      norm_add_le _ _
    _ = |c0| * ‖f0 U‖ + |c1| * ‖f1 U‖ := by
      simp [norm_mul, Real.norm_eq_abs]
    _ ≤ |c0| * ‖f0‖ + |c1| * ‖f1‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left h0 (abs_nonneg c0))
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg c1))

/-- Every original two-mode time-one Wilson cylinder is square-integrable
with respect to the actual, precisely normalized interacting finite
temporal-gauge Wilson half-path probability (for beta >= 0). -/
theorem p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_memLp
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    MemLp (p4Q2PZ37ANA_timeOneTwoModeWilsonObservable H c0 c1)
      2 (p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta) := by
  letI : IsProbabilityMeasure
      (p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta) :=
    p4Q2PZ37AMZ_originalNormalizedHalfPath_isProbabilityMeasure H beta hbeta
  exact MemLp.of_bound
    (p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_measurable H c0 c1).aestronglyMeasurable
    (|c0| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 0‖ +
      |c1| * ‖specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode 1‖)
    (Filter.Eventually.of_forall
      (p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_norm_le H c0 c1))

/-- Type-correct real L² state of the genuine normalized interacting Wilson
positive-half path, with the exact same literal time-one cylinder function. -/
noncomputable def p4Q2PZ37ANA_normalizedWilsonTimeOneTwoModeL2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    Lp ℝ 2 (p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta) :=
  (p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_memLp H beta hbeta c0 c1).toLp
    (p4Q2PZ37ANA_timeOneTwoModeWilsonObservable H c0 c1)

/-- The constructed L² class has the EXACT original pointwise Wilson mode
as its a.e. representative under the normalized interacting path law. -/
theorem p4Q2PZ37ANA_normalizedWilsonTimeOneTwoModeL2_coeFn
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (c0 c1 : ℝ) :
    p4Q2PZ37ANA_normalizedWilsonTimeOneTwoModeL2 H beta hbeta c0 c1
      =ᵐ[p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta]
        p4Q2PZ37ANA_timeOneTwoModeWilsonObservable H c0 c1 := by
  exact (p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_memLp H beta hbeta c0 c1).coeFn_toLp

/-- Nonzero original physical top-orthogonal two-mode time-one Wilson
cylinder realized as a genuinely nonzero real L² state for the precisely
normalized interacting positive-half temporal-gauge Wilson path law. -/
theorem p4Q2PZ37ANA_exists_nonzero_normalizedInteractingWilsonTimeOneL2
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ c0 c1 : ℝ,
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by norm_num) beta hbeta ∧
      ∃ ψ : Lp ℝ 2 (p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta),
        ψ ≠ 0 ∧
        ψ =ᵐ[p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta]
          p4Q2PZ37ANA_timeOneTwoModeWilsonObservable H c0 c1 := by
  obtain ⟨c0, c1, hTop, hNonzero⟩ :=
    p4Q2PZ37AMZ_exists_nonzero_normalized_originalWilsonTimeOneCylinder H beta hbeta
  let ν := p4Q2PZ37AMZ_originalNormalizedHalfPathMeasure H beta
  let g := p4Q2PZ37ANA_timeOneTwoModeWilsonObservable H c0 c1
  let ψ := p4Q2PZ37ANA_normalizedWilsonTimeOneTwoModeL2 H beta hbeta c0 c1
  have hNonzeroG : ¬ (g =ᵐ[ν] (fun _ => (0 : ℝ))) := by
    simpa [g, ν, p4Q2PZ37ANA_timeOneTwoModeWilsonObservable] using hNonzero
  have hRepresentative : ψ =ᵐ[ν] g := by
    exact p4Q2PZ37ANA_normalizedWilsonTimeOneTwoModeL2_coeFn H beta hbeta c0 c1
  have hψne : ψ ≠ 0 := by
    intro hzero
    have hψ0 : ψ =ᵐ[ν] (fun _ => (0 : ℝ)) := by
      rw [hzero]
      simpa only [Pi.zero_apply] using (Lp.coeFn_zero ℝ 2 ν)
    exact hNonzeroG (hRepresentative.symm.trans hψ0)
  refine ⟨c0, c1, hTop, ψ, hψne, ?_⟩
  simpa [ψ, g, ν] using hRepresentative

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_norm_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_memLp
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANA_normalizedWilsonTimeOneTwoModeL2_coeFn
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANA_exists_nonzero_normalizedInteractingWilsonTimeOneL2
