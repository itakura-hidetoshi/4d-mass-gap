import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsNondegenerateEventInteraction
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsHilbertEquivalence
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveLimitExistence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Generate the nondegenerate cylinder event required by the interaction frontier
from two finite Wilson source configurations separated by the global
observation.

Every finite Wilson Gibbs configuration has strictly positive mass.  Therefore
the singleton cylinder event determined by one observed configuration has
positive probability.  If a second source configuration has a different
finite observation, its positive singleton mass lies in the complement, so the
same event has probability strictly below one.
-/

/-- Every source configuration has strictly positive real singleton mass under
the finite Wilson Gibbs measure. -/
theorem finite_lattice_gibbsMeasure_real_singleton_pos
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) :
    0 < L.gibbsMeasure.real ({A} : Set L.Configuration) := by
  change 0 < (L.gibbsMeasure ({A} : Set L.Configuration)).toReal
  unfold FiniteLatticeWilsonSystem.gibbsMeasure
  rw [L.gibbsPMF.toMeasure_apply_singleton A (measurableSet_singleton A)]
  simpa [FiniteLatticeWilsonSystem.gibbsProbabilityReal] using
    finite_lattice_gibbsProbabilityReal_pos L A

/-- The singleton cylinder event containing the observation of a source
configuration has positive Wilson Gibbs probability. -/
theorem finite_wilson_gibbs_singleton_observation_event_probability_pos
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (J : Finset EuclideanFourSpace)
    (A : (W.system R.sourceScale).Configuration) :
    0 < finiteWilsonGibbsCylinderEventProbability R J
      ({R.observe J A} : Set (FiniteWilsonGibbsCylinderConfiguration R J)) := by
  change
    0 < ((W.system R.sourceScale).gibbsMeasure.map (R.observe J)).real
      ({R.observe J A} : Set (FiniteWilsonGibbsCylinderConfiguration R J))
  rw [map_measureReal_apply (R.observe_measurable J)
    (MeasurableSet.singleton (R.observe J A))]
  exact
    (finite_lattice_gibbsMeasure_real_singleton_pos
      (W.system R.sourceScale) A).trans_le
      (measureReal_mono (by
        intro X hX
        have hXA : X = A := by simpa using hX
        subst X
        simp))

/-- If two source configurations have different finite observations, the
singleton cylinder event of the first observation has probability below one. -/
theorem finite_wilson_gibbs_singleton_observation_event_probability_lt_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (J : Finset EuclideanFourSpace)
    (A B : (W.system R.sourceScale).Configuration)
    (hAB : R.observe J A ≠ R.observe J B) :
    finiteWilsonGibbsCylinderEventProbability R J
      ({R.observe J A} : Set (FiniteWilsonGibbsCylinderConfiguration R J)) < 1 := by
  let t : Set (W.system R.sourceScale).Configuration :=
    (R.observe J) ⁻¹'
      ({R.observe J A} : Set (FiniteWilsonGibbsCylinderConfiguration R J))
  have ht : MeasurableSet t :=
    (R.observe_measurable J)
      (MeasurableSet.singleton (R.observe J A))
  change
    ((W.system R.sourceScale).gibbsMeasure.map (R.observe J)).real
      ({R.observe J A} : Set (FiniteWilsonGibbsCylinderConfiguration R J)) < 1
  rw [map_measureReal_apply (R.observe_measurable J)
    (MeasurableSet.singleton (R.observe J A))]
  change (W.system R.sourceScale).gibbsMeasure.real t < 1
  have hcomp_pos :
      0 < (W.system R.sourceScale).gibbsMeasure.real tᶜ := by
    exact
      (finite_lattice_gibbsMeasure_real_singleton_pos
        (W.system R.sourceScale) B).trans_le
        (measureReal_mono (by
          intro X hX
          have hXB : X = B := by simpa using hX
          subst X
          show R.observe J B ∉
            ({R.observe J A} :
              Set (FiniteWilsonGibbsCylinderConfiguration R J))
          simpa using hAB.symm))
  have hsum :
      (W.system R.sourceScale).gibbsMeasure.real t +
          (W.system R.sourceScale).gibbsMeasure.real tᶜ = 1 :=
    probReal_add_probReal_compl ht
  nlinarith

/-- Two source configurations separated by the full global observation. -/
structure FiniteWilsonGibbsGlobalObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  sourceLeft : (W.system R.sourceScale).Configuration
  sourceRight : (W.system R.sourceScale).Configuration
  globalObserve_ne :
    R.globalObserve sourceLeft ≠ R.globalObserve sourceRight

/-- Global observation separation yields a singleton finite-cylinder event with
probability strictly between zero and one. -/
noncomputable def
    FiniteWilsonGibbsGlobalObservationSeparation.toNondegenerateEvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    FiniteWilsonGibbsCylinderNondegenerateEvent R := by
  classical
  have hex : ∃ x : EuclideanFourSpace,
      R.globalObserve G.sourceLeft x ≠ R.globalObserve G.sourceRight x := by
    by_contra hno
    apply G.globalObserve_ne
    funext x
    by_contra hx
    exact hno ⟨x, hx⟩
  let x := Classical.choose hex
  have hx :
      R.globalObserve G.sourceLeft x ≠ R.globalObserve G.sourceRight x :=
    Classical.choose_spec hex
  have hobserve :
      R.observe ({x} : Finset EuclideanFourSpace) G.sourceLeft ≠
        R.observe ({x} : Finset EuclideanFourSpace) G.sourceRight := by
    intro h
    have hpoint := congrFun h
      (⟨x, by simp⟩ : ↥({x} : Finset EuclideanFourSpace))
    exact hx (by
      simpa [FiniteWilsonGibbsSingleSourceProjectiveRealization.globalObserve]
        using hpoint)
  exact
    { support := {x}
      event :=
        ({R.observe ({x} : Finset EuclideanFourSpace) G.sourceLeft} :
          Set (FiniteWilsonGibbsCylinderConfiguration R
            ({x} : Finset EuclideanFourSpace)))
      event_measurable := MeasurableSet.singleton _
      probability_pos :=
        finite_wilson_gibbs_singleton_observation_event_probability_pos
          R ({x} : Finset EuclideanFourSpace) G.sourceLeft
      probability_lt_one :=
        finite_wilson_gibbs_singleton_observation_event_probability_lt_one
          R ({x} : Finset EuclideanFourSpace)
          G.sourceLeft G.sourceRight hobserve }

/-- Global observation separation theorem-generates the finite interaction
witness introduced by the nondegenerate-event frontier. -/
noncomputable def
    FiniteWilsonGibbsGlobalObservationSeparation.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    FiniteWilsonGibbsCylinderInteractionWitness R :=
  finiteWilsonGibbsInteractionWitnessOfNondegenerateEvent
    R G.toNondegenerateEvent

/-- The interaction witness generated from global observation separation
survives as a nonzero continuum connected correlation. -/
theorem finite_wilson_global_observation_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R D
      G.toInteractionWitness.support
      G.toInteractionWitness.leftObservable
      G.toInteractionWitness.rightObservable ≠ 0 := by
  exact finite_wilson_cylinder_interaction_passes_to_continuum
    R D G.toInteractionWitness

end

end MathlibAnalytic
end MGAP4D
