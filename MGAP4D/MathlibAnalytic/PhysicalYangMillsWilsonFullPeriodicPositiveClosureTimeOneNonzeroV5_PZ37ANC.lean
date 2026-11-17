import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonFullPeriodicPositiveClosureHaarEquivalenceV5_PZ37ANB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NormalizedInteractingPositiveTimeL2CylinderV5_PZ37ANA
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANC — genuine periodic Gibbs time-one cylinder on positive closure

The *same literal* AMY/ANA spatial time-one two-mode Wilson observable is
transported by the existing positive-closure measurable equivalence, without
identifying ANA's separately normalized temporal-gauge half-path probability
with the genuine full-periodic Gibbs positive-closure marginal.

1. The observable on the actual boundary/open-positive-half closure is measurable.
2. Its canonical spatial-path extraction preserves the original product Haar.
3. Original AMY nonzero time-one cylinders remain nonzero under closure Haar.
4. ANB mutual absolute continuity transfers their nonzero a.e. class to the
   genuine full-periodic interacting Gibbs positive-closure marginal.

No new physical Hamiltonian, OS Hilbert identification, density-uniform bound,
intertwining, or continuum mass-gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANC_sideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩
local instance p4Q2PZ37ANC_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANC_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANC_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANC_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANC_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- Typed insertion on genuine positive-closure coordinates: extract the
spatial-path component and apply ANA's unmodified time-one cylinder. -/
noncomputable def p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable
    (H : ℕ) (c0 c1 : ℝ)
    (z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) : ℝ :=
  p4Q2PZ37ANA_timeOneTwoModeWilsonObservable H c0 c1
    ((periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
      H 2 z).1)

/-- The genuine positive-closure time-one insertion is measurable. -/
theorem p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable_measurable
    (H : ℕ) (c0 c1 : ℝ) :
    Measurable (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1) := by
  exact
    (p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_measurable H c0 c1).comp
      (measurable_fst.comp
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H 2).measurable)

/-- Actual boundary/open-half product Haar pushes to the *unchanged*
original positive-half spatial-path Haar along canonical closure reindexing
and first-factor projection. No Wilson/Gibbs law is substituted here. -/
theorem p4Q2PZ37ANC_positiveClosureSpatialPath_measurePreserving
    (H : ℕ) :
    MeasurePreserving
      (fun z : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
          H 2 z).1)
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2) := by
  let ρ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2
  let τ := periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H 2
  have hTransport :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv_measurePreserving_explicitHaar
      H 2
  change
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv H 2)
      ((periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2))
      (ρ.prod τ) at hTransport
  have hFst : MeasurePreserving
      (fun q :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H 2 =>
        q.1)
      (ρ.prod τ) ρ :=
    MeasureTheory.measurePreserving_fst
  simpa [ρ, Function.comp_def] using hFst.comp hTransport

/-- Canonical transfer of the original AMY physical top-orthogonal nonzero
time-one cylinder to the literal positive closure, under product Haar. -/
theorem p4Q2PZ37ANC_exists_nonzero_positiveClosureHaar_timeOneCylinder
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ c0 c1 : ℝ,
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by norm_num) beta hbeta ∧
      ¬ (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1 =ᵐ[
          (periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
            (periodicHypercubicEvenOpenHalfHaarMeasure H 2)]
          (fun _ => (0 : ℝ))) := by
  obtain ⟨c0, c1, hTop, hWeightedNonzero⟩ :=
    p4Q2PZ37AMY_exists_nonzero_weighted_originalWilsonTimeOneCylinder
      H beta hbeta
  let ρ := periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H 2
  let ν := p4Q2PZ37AMY_originalTemporalGaugeWeightedPathMeasure H beta
  let g := p4Q2PZ37ANA_timeOneTwoModeWilsonObservable H c0 c1
  have hνac : ν ≪ ρ := by
    simpa [ν, ρ] using p4Q2PZ37AMY_weightedWilson_ac_originalPathHaar H beta
  have hNonzeroRho : ¬ (g =ᵐ[ρ] (fun _ => (0 : ℝ))) := by
    intro hgRho
    have hgNu : g =ᵐ[ν] (fun _ => (0 : ℝ)) :=
      hνac.ae_eq hgRho
    exact hWeightedNonzero (by
      simpa [g, ν, p4Q2PZ37ANA_timeOneTwoModeWilsonObservable] using hgNu)
  let λ := (periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
    (periodicHypercubicEvenOpenHalfHaarMeasure H 2)
  let t : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) →
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 :=
    fun z => (periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureTransferMeasurableEquiv
      H 2 z).1
  have ht : MeasurePreserving t λ ρ := by
    simpa [t, λ, ρ] using
      p4Q2PZ37ANC_positiveClosureSpatialPath_measurePreserving H
  have hGMeas : Measurable g := by
    exact p4Q2PZ37ANA_timeOneTwoModeWilsonObservable_measurable H c0 c1
  have hSet : MeasurableSet
      {path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H 2 |
        g path = (0 : ℝ)} :=
    measurableSet_eq_fun hGMeas measurable_const
  refine ⟨c0, c1, hTop, ?_⟩
  intro hZeroLambda
  have hZeroMapped : ∀ᵐ path ∂Measure.map t λ, g path = (0 : ℝ) := by
    rw [MeasureTheory.ae_map_iff ht.measurable.aemeasurable hSet]
    simpa [g, t, λ, p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable] using
      hZeroLambda
  rw [ht.map_eq] at hZeroMapped
  exact hNonzeroRho hZeroMapped

/-- The genuine full-periodic positive-closure Gibbs marginal and unmodified
closure Haar give the same a.e.-zero classes, for *any* real observable. -/
theorem p4Q2PZ37ANC_fullPeriodicPositiveClosure_ae_zero_iff_productHaar
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (F : PeriodicHypercubicEvenPositiveHalfClosureConfiguration H
      (Matrix.specialUnitaryGroup (Fin 2) ℂ) → ℝ) :
    (F =ᵐ[
      Measure.map
        (fun A : PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin 2) ℂ =>
          ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
            (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A))
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta).gibbsMeasure]
      (fun _ => (0 : ℝ))) ↔
    (F =ᵐ[
      (periodicHypercubicEvenBoundaryHaarMeasure H 2).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H 2)]
      (fun _ => (0 : ℝ))) := by
  constructor
  · exact (p4Q2PZ37ANB_positiveClosureProductHaar_ac_fullPeriodicGibbs
      H 2 (by norm_num) beta hbeta).ae_eq
  · exact (p4Q2PZ37ANB_fullPeriodicPositiveClosureGibbs_ac_productHaar
      H 2 (by norm_num) beta hbeta).ae_eq

/-- The transported true physical two-mode time-one cylinder is nonzero
under the original *full-periodic interacting* Wilson Gibbs positive-closure
marginal, rather than only the ANA/AMY temporal-gauge half-path law. -/
theorem p4Q2PZ37ANC_exists_nonzero_truePeriodicGibbsPositiveClosureTimeOneCylinder
    (H : ℕ) [Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ c0 c1 : ℝ,
      (c0 • p4Q2PZ37AMU_actualPhysicalGaussMode H 0 +
        c1 • p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by norm_num) beta hbeta ∧
      ¬ (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1 =ᵐ[
        Measure.map
          (fun A : PeriodicHypercubicEvenEdge H →
              Matrix.specialUnitaryGroup (Fin 2) ℂ =>
            ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryRestriction A,
              (periodicHypercubicEvenEdgeOrbitPartition H).positiveRestriction A))
          (periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) 2 (by norm_num) beta hbeta).gibbsMeasure]
          (fun _ => (0 : ℝ))) := by
  obtain ⟨c0, c1, hTop, hHaarNonzero⟩ :=
    p4Q2PZ37ANC_exists_nonzero_positiveClosureHaar_timeOneCylinder H beta hbeta
  refine ⟨c0, c1, hTop, ?_⟩
  intro hGibbsZero
  exact hHaarNonzero
    ((p4Q2PZ37ANC_fullPeriodicPositiveClosure_ae_zero_iff_productHaar
      H beta hbeta
      (p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable H c0 c1)).mp hGibbsZero)

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANC_timeOneTwoModePositiveClosureObservable_measurable
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANC_positiveClosureSpatialPath_measurePreserving
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANC_exists_nonzero_positiveClosureHaar_timeOneCylinder
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANC_fullPeriodicPositiveClosure_ae_zero_iff_productHaar
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANC_exists_nonzero_truePeriodicGibbsPositiveClosureTimeOneCylinder
