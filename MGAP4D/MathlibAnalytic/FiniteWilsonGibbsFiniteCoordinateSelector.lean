import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsFiniteCoordinateSeparation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
A constructive finite-coordinate route to Wilson observation faithfulness.

Instead of assuming only that some coordinate separates every unequal pair, this
package records a selector which chooses such a coordinate from the inequality
proof.  Forgetting the selector gives the coordinate-separation package and all
of its downstream interaction and exact-gap consequences.
-/

/-- A finite observation support together with an explicit separating-coordinate
selector for every unequal pair of source configurations. -/
structure FiniteWilsonGibbsFiniteCoordinateSelector
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  support : Finset EuclideanFourSpace
  select :
    ∀ {A B : (W.system R.sourceScale).Configuration},
      A ≠ B → support
  select_separates :
    ∀ {A B : (W.system R.sourceScale).Configuration}
      (hAB : A ≠ B),
      R.observe support A (select hAB) ≠
        R.observe support B (select hAB)

/-- Forgetting the chosen witness yields finite coordinate separation. -/
def FiniteWilsonGibbsFiniteCoordinateSelector.toCoordinateSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteCoordinateSelector R) :
    FiniteWilsonGibbsFiniteCoordinateSeparation R where
  support := S.support
  separates := by
    intro A B hAB
    exact ⟨S.select hAB, S.select_separates hAB⟩

/-- The selected coordinate directly contradicts equality of the finite
observation functions. -/
theorem FiniteWilsonGibbsFiniteCoordinateSelector.observe_ne
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteCoordinateSelector R)
    {A B : (W.system R.sourceScale).Configuration}
    (hAB : A ≠ B) :
    R.observe S.support A ≠ R.observe S.support B := by
  intro hEq
  exact S.select_separates hAB (congrFun hEq (S.select hAB))

/-- A finite separating-coordinate selector proves injectivity of the finite
observation map. -/
theorem FiniteWilsonGibbsFiniteCoordinateSelector.injective_observe
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteCoordinateSelector R) :
    Function.Injective (R.observe S.support) := by
  intro A B hEq
  by_contra hAB
  exact S.observe_ne hAB hEq

/-- Package finite observation separation from the selector. -/
def FiniteWilsonGibbsFiniteCoordinateSelector.toFiniteObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteCoordinateSelector R) :
    FiniteWilsonGibbsFiniteObservationSeparation R where
  support := S.support
  injective_observe := S.injective_observe

/-- The selector proves faithfulness of the global observation map. -/
def FiniteWilsonGibbsFiniteCoordinateSelector.toFaithfulGlobalObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteCoordinateSelector R) :
    FiniteWilsonGibbsFaithfulGlobalObservation R :=
  S.toFiniteObservationSeparation.toFaithfulGlobalObservation

/-- Source nontriviality and a selector generate globally separated Wilson
configurations. -/
noncomputable def
    FiniteWilsonGibbsFiniteCoordinateSelector.toGlobalObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    (S : FiniteWilsonGibbsFiniteCoordinateSelector R) :
    FiniteWilsonGibbsGlobalObservationSeparation R :=
  S.toFaithfulGlobalObservation.toGlobalObservationSeparation

/-- A selector generates the finite cylinder interaction witness. -/
noncomputable def
    FiniteWilsonGibbsFiniteCoordinateSelector.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (S : FiniteWilsonGibbsFiniteCoordinateSelector R) :
    FiniteWilsonGibbsCylinderInteractionWitness R :=
  S.toFaithfulGlobalObservation.toInteractionWitness

/-- The selected-coordinate interaction witness survives in the continuum law. -/
theorem finite_wilson_finite_coordinate_selector_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (S : FiniteWilsonGibbsFiniteCoordinateSelector R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R L
      S.toInteractionWitness.support
      S.toInteractionWitness.leftObservable
      S.toInteractionWitness.rightObservable ≠ 0 := by
  exact finite_wilson_faithful_global_observation_interaction_passes_to_continuum
    R L S.toFaithfulGlobalObservation

/-- The selector route reaches the exact-threshold spectral separation endpoint. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.finiteCoordinateSelector_exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (S : FiniteWilsonGibbsFiniteCoordinateSelector R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpineOfGlobalObservationSeparation
        S.toGlobalObservationSeparation).toConstructionSpine := by
  exact C.globalObservation_exactThresholdSeparation
    S.toGlobalObservationSeparation

end

end MathlibAnalytic
end MGAP4D
