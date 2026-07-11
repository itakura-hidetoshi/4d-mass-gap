import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsFiniteCoordinateSelector

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Extract a single finite separating observation support from pointwise global
separation when the finite Wilson source configuration space is finite.

For every unequal pair of source configurations, choose one spacetime point at
which their global observations differ.  Since the source configuration space
is finite, the subtype of unequal pairs is finite.  The image of the chosen
points is therefore one finite support separating every pair simultaneously.
-/

/-- Every unequal pair of finite Wilson source configurations is separated by
at least one coordinate of the global observation. -/
structure FiniteWilsonGibbsGlobalPointSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  separates :
    ∀ {A B : (W.system R.sourceScale).Configuration},
      A ≠ B →
        ∃ x : EuclideanFourSpace,
          R.globalObserve A x ≠ R.globalObserve B x

/-- The finite type of ordered unequal source-configuration pairs. -/
abbrev FiniteWilsonUnequalConfigurationPair
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) :=
  {p : (W.system R.sourceScale).Configuration ×
      (W.system R.sourceScale).Configuration // p.1 ≠ p.2}

/-- Choose one separating spacetime point for each unequal pair. -/
noncomputable def FiniteWilsonGibbsGlobalPointSeparation.separatingPoint
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (P : FiniteWilsonGibbsGlobalPointSeparation R)
    (p : FiniteWilsonUnequalConfigurationPair R) : EuclideanFourSpace :=
  Classical.choose (P.separates p.property)

/-- The chosen point really separates its associated pair. -/
theorem FiniteWilsonGibbsGlobalPointSeparation.separatingPoint_spec
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (P : FiniteWilsonGibbsGlobalPointSeparation R)
    (p : FiniteWilsonUnequalConfigurationPair R) :
    R.globalObserve p.1.1 (P.separatingPoint p) ≠
      R.globalObserve p.1.2 (P.separatingPoint p) :=
  Classical.choose_spec (P.separates p.property)

/-- The image of all chosen pair-separating points is a finite support. -/
noncomputable def FiniteWilsonGibbsGlobalPointSeparation.support
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Fintype (W.system R.sourceScale).Configuration]
    (P : FiniteWilsonGibbsGlobalPointSeparation R) :
    Finset EuclideanFourSpace := by
  classical
  exact Finset.univ.image P.separatingPoint

/-- Every chosen point belongs to the extracted finite support. -/
theorem FiniteWilsonGibbsGlobalPointSeparation.separatingPoint_mem_support
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Fintype (W.system R.sourceScale).Configuration]
    (P : FiniteWilsonGibbsGlobalPointSeparation R)
    (p : FiniteWilsonUnequalConfigurationPair R) :
    P.separatingPoint p ∈ P.support := by
  classical
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩

/-- Pointwise separation on a finite source space canonically produces the
constructive finite-coordinate selector from the preceding theorem layer. -/
noncomputable def
    FiniteWilsonGibbsGlobalPointSeparation.toFiniteCoordinateSelector
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Fintype (W.system R.sourceScale).Configuration]
    (P : FiniteWilsonGibbsGlobalPointSeparation R) :
    FiniteWilsonGibbsFiniteCoordinateSelector R where
  support := P.support
  select := by
    intro A B hAB
    let p : FiniteWilsonUnequalConfigurationPair R := ⟨(A, B), hAB⟩
    exact ⟨P.separatingPoint p, P.separatingPoint_mem_support p⟩
  select_separates := by
    intro A B hAB
    let p : FiniteWilsonUnequalConfigurationPair R := ⟨(A, B), hAB⟩
    let x : P.support :=
      ⟨P.separatingPoint p, P.separatingPoint_mem_support p⟩
    intro hEq
    apply P.separatingPoint_spec p
    calc
      R.globalObserve A (P.separatingPoint p) =
          P.support.restrict (R.globalObserve A) x := rfl
      _ = R.observe P.support A x :=
        congrFun
          (finite_wilson_gibbs_single_source_globalObserve_restrict
            R P.support A) x
      _ = R.observe P.support B x := hEq
      _ = P.support.restrict (R.globalObserve B) x :=
        (congrFun
          (finite_wilson_gibbs_single_source_globalObserve_restrict
            R P.support B) x).symm
      _ = R.globalObserve B (P.separatingPoint p) := rfl

/-- The extracted finite support proves faithfulness of the global observation. -/
def FiniteWilsonGibbsGlobalPointSeparation.toFaithfulGlobalObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Fintype (W.system R.sourceScale).Configuration]
    (P : FiniteWilsonGibbsGlobalPointSeparation R) :
    FiniteWilsonGibbsFaithfulGlobalObservation R :=
  P.toFiniteCoordinateSelector.toFaithfulGlobalObservation

/-- Pointwise global separation, finite source configurations, and source
nontriviality generate the finite interaction witness. -/
noncomputable def FiniteWilsonGibbsGlobalPointSeparation.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Fintype (W.system R.sourceScale).Configuration]
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (P : FiniteWilsonGibbsGlobalPointSeparation R) :
    FiniteWilsonGibbsCylinderInteractionWitness R :=
  P.toFiniteCoordinateSelector.toInteractionWitness

/-- The extracted finite-support interaction witness survives in the continuum
connected correlation. -/
theorem finite_wilson_global_point_separation_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [Fintype (W.system R.sourceScale).Configuration]
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (P : FiniteWilsonGibbsGlobalPointSeparation R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R L
      P.toInteractionWitness.support
      P.toInteractionWitness.leftObservable
      P.toInteractionWitness.rightObservable ≠ 0 := by
  exact finite_wilson_finite_coordinate_selector_interaction_passes_to_continuum
    R L P.toFiniteCoordinateSelector

/-- The finite-support extraction route reaches exact-threshold spectral
separation. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.globalPointSeparation_exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Fintype (W.system R.sourceScale).Configuration]
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (P : FiniteWilsonGibbsGlobalPointSeparation R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpineOfGlobalObservationSeparation
        P.toFiniteCoordinateSelector.toGlobalObservationSeparation).toConstructionSpine := by
  exact C.finiteCoordinateSelector_exactThresholdSeparation
    P.toFiniteCoordinateSelector

end

end MathlibAnalytic
end MGAP4D
