import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoWilsonEnergyContinuousGramSchmidtClassFunction

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

local instance specialUnitaryTwoBoundaryRepresentativeTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance specialUnitaryTwoBoundaryRepresentativeCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance specialUnitaryTwoBoundaryRepresentativeSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance specialUnitaryTwoBoundaryRepresentativeMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance specialUnitaryTwoBoundaryRepresentativeBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- The theorem-generated primary-plaquette boundary-Haar `L²` mode is exactly
the measure-preserving pullback of the canonical continuous Gram--Schmidt
representative before passing to its `L²` class. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_eq_continuousModePullback
    (H k : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        H k =
      periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback H 2
        (ContinuousMap.toLp
          (E := ℝ) 2
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
          (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k)) := by
  rw [specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode_toLp]
  rfl

/-- The actual boundary observable from the continuous class-function layer is
an a.e. representative of the theorem-generated boundary-Haar `L²` mode.

This is the exact bridge from the abstract `Lp` equivalence class back to the
pointwise Wilson observable.  It uses only Mathlib's canonical
`ContinuousMap.toLp` representative theorem and pullback along the
measure-preserving primary-plaquette cyclic holonomy. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_coeFn
    (H k : ℕ) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2
        H k =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H 2]
      periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable
        H k := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryHaarL2_eq_continuousModePullback]
  let hMP :=
    measurePreserving_periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy
      H 2
  let f : SpecialUnitaryNormalizedHaarL2 2 :=
    ContinuousMap.toLp
      (E := ℝ) 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)) ℝ
      (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k)
  have hComp :
      periodicHypercubicEvenPrimarySpatialPlaquetteHolonomyBoundaryL2Pullback H 2 f
          =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H 2]
        f ∘ periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 := by
    exact Lp.coeFn_compMeasurePreserving f hMP
  have hSource :
      f =ᵐ[normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)]
        specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ))
      (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k)
  have hPulled :
      f ∘ periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2
          =ᵐ[periodicHypercubicEvenBoundaryHaarMeasure H 2]
        (specialUnitaryWilsonPlaquetteEnergyTwoContinuousGramSchmidtMode k) ∘
          periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 :=
    hMP.quasiMeasurePreserving.ae_eq hSource
  exact hComp.trans (by
    simpa [periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtBoundaryObservable,
      Function.comp_def] using hPulled)

end

end MathlibAnalytic
end MGAP4D
