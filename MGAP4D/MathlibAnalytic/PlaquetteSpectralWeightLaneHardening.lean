import MGAP4D.MathlibAnalytic.ContinuumYangMillsLaneHardening
import MGAP4D.MathlibAnalytic.ObservableAtomTheoremTheorem
import MGAP4D.MathlibAnalytic.CompactPlaquetteConstructionTheorem
import MGAP4D.MathlibAnalytic.OperatorMeasureCompatibilityTheorem
import MGAP4D.MathlibAnalytic.ExactGapTheoremBodyClosure

namespace MGAP4D
namespace MathlibAnalytic

/-- Hardening surface for the plaquette spectral-weight lane.

This refines `plaquetteSpectralWeightLane` into an ordered review-level chain:
observable atom theorem, compact plaquette construction, operator-measure
compatibility, and exact theorem-body weight closure. It remains review-level
and preserves the public boundary. -/
structure PlaquetteSpectralWeightLaneHardeningData where
  continuumYMLaneReady : continuumYangMillsLaneHardeningData.ready
  observableAtomReady : observableAtomTheoremTheoremReviewSurface.ready
  compactPlaquetteReady : compactPlaquetteConstructionTheoremReviewSurface.ready
  operatorMeasureReady : operatorMeasureCompatibilityTheoremReviewSurface.ready
  exactBodyClosureReady : exactGapTheoremBodyClosure.ready
  compactSupportHardened : Prop
  centeredHardened : Prop
  smearedHardened : Prop
  plaquetteConstructionHardened : Prop
  observableAtomHardened : Prop
  positiveWeightHardened : Prop
  nonzeroWeightHardened : Prop
  weightEqualsPVMMassHardened : Prop
  operatorMeasureCompatibilityHardened : Prop
  exactBodyWeightClosureHardened : Prop
  concretePlaquetteBoundaryVisible : Prop
  concreteOperatorMeasureBoundaryVisible : Prop
  hardPhysicalBoundaryVisible : Prop
  exactValuePreserved : exactGapValueReal = (33 : ℝ) / 20
  reviewLevelOnly : Prop
  publicBoundaryHeld : Prop
  finalReleaseHeld : Prop

/-- Ready predicate for the plaquette spectral-weight hardening lane. -/
def PlaquetteSpectralWeightLaneHardeningData.ready
    (D : PlaquetteSpectralWeightLaneHardeningData) : Prop :=
  continuumYangMillsLaneHardeningData.ready ∧
  observableAtomTheoremTheoremReviewSurface.ready ∧
  compactPlaquetteConstructionTheoremReviewSurface.ready ∧
  operatorMeasureCompatibilityTheoremReviewSurface.ready ∧
  exactGapTheoremBodyClosure.ready ∧
  D.compactSupportHardened ∧
  D.centeredHardened ∧
  D.smearedHardened ∧
  D.plaquetteConstructionHardened ∧
  D.observableAtomHardened ∧
  D.positiveWeightHardened ∧
  D.nonzeroWeightHardened ∧
  D.weightEqualsPVMMassHardened ∧
  D.operatorMeasureCompatibilityHardened ∧
  D.exactBodyWeightClosureHardened ∧
  D.concretePlaquetteBoundaryVisible ∧
  D.concreteOperatorMeasureBoundaryVisible ∧
  D.hardPhysicalBoundaryVisible ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  D.reviewLevelOnly ∧
  D.publicBoundaryHeld ∧
  D.finalReleaseHeld

/-- Compact support surface is hardened. -/
theorem plaquette_weight_compact_support_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.compactSupportHardened := by
  rcases hD with ⟨_, _, _, _, _, h, _⟩
  exact h

/-- Centered observable surface is hardened. -/
theorem plaquette_weight_centered_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.centeredHardened := by
  rcases hD with ⟨_, _, _, _, _, _, h, _⟩
  exact h

/-- Smeared observable surface is hardened. -/
theorem plaquette_weight_smeared_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.smearedHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, h, _⟩
  exact h

/-- Compact plaquette construction surface is hardened. -/
theorem plaquette_weight_construction_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.plaquetteConstructionHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Observable atom surface is hardened. -/
theorem plaquette_weight_observable_atom_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.observableAtomHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Positive spectral weight surface is hardened. -/
theorem plaquette_weight_positive_weight_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.positiveWeightHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Nonzero spectral weight surface is hardened. -/
theorem plaquette_weight_nonzero_weight_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.nonzeroWeightHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Equality of observable weight and PVM exact-atom mass is hardened. -/
theorem plaquette_weight_equals_pvm_mass_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.weightEqualsPVMMassHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Operator-measure compatibility surface is hardened. -/
theorem plaquette_weight_operator_measure_compatibility_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.operatorMeasureCompatibilityHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Exact theorem-body weight closure is hardened. -/
theorem plaquette_weight_exact_body_weight_closure_hardened
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.exactBodyWeightClosureHardened := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Concrete plaquette boundary remains visible. -/
theorem plaquette_weight_concrete_plaquette_boundary_visible
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.concretePlaquetteBoundaryVisible := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Concrete operator-measure boundary remains visible. -/
theorem plaquette_weight_operator_measure_boundary_visible
    (D : PlaquetteSpectralWeightLaneHardeningData) (hD : D.ready) :
    D.concreteOperatorMeasureBoundaryVisible := by
  rcases hD with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

/-- Exact normalized value is preserved by the plaquette spectral-weight lane. -/
theorem plaquette_weight_exact_value_preserved
    (D : PlaquetteSpectralWeightLaneHardeningData) (_hD : D.ready) :
    exactGapValueReal = (33 : ℝ) / 20 := by
  exact D.exactValuePreserved

/-- Installed plaquette spectral-weight hardening lane. -/
def plaquetteSpectralWeightLaneHardeningData : PlaquetteSpectralWeightLaneHardeningData :=
  { continuumYMLaneReady := continuum_yang_mills_lane_hardening_ready
    observableAtomReady := observable_atom_theorem_theorem_review_surface_ready
    compactPlaquetteReady := compact_plaquette_construction_theorem_review_surface_ready
    operatorMeasureReady := operator_measure_compatibility_theorem_review_surface_ready
    exactBodyClosureReady := exact_gap_theorem_body_closure_ready
    compactSupportHardened :=
      singletonObservableAtomTheoremTheoremData.compactSupport
        singletonObservableAtomTheoremTheoremData.chosenObservable
    centeredHardened :=
      singletonObservableAtomTheoremTheoremData.centered
        singletonObservableAtomTheoremTheoremData.chosenObservable
    smearedHardened :=
      singletonObservableAtomTheoremTheoremData.smeared
        singletonObservableAtomTheoremTheoremData.chosenObservable
    plaquetteConstructionHardened := compactPlaquetteConstructionTheoremReviewSurface.ready
    observableAtomHardened := observableAtomTheoremTheoremReviewSurface.ready
    positiveWeightHardened :=
      0 < singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
        singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
        singletonOperatorMeasureCompatibilityTheoremData.exactAtom
    nonzeroWeightHardened :=
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
        singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
        singletonOperatorMeasureCompatibilityTheoremData.exactAtom ≠ 0
    weightEqualsPVMMassHardened :=
      singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.spectralWeight
        singletonOperatorMeasureCompatibilityTheoremData.constructedObservable
        singletonOperatorMeasureCompatibilityTheoremData.exactAtom =
        singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.projectionMass
          singletonOperatorMeasureCompatibilityTheoremData.observableAtomData.pvmData.exactAtom
    operatorMeasureCompatibilityHardened := operatorMeasureCompatibilityTheoremReviewSurface.ready
    exactBodyWeightClosureHardened := exactGapTheoremBodyClosure.ready
    concretePlaquetteBoundaryVisible :=
      compactPlaquetteConstructionTheoremReviewSurface.concreteLatticeGaugePlaquetteStillOpen
        compactPlaquetteConstructionTheoremReviewSurface
    concreteOperatorMeasureBoundaryVisible :=
      operatorMeasureCompatibilityTheoremReviewSurface.concreteOperatorMeasureRealizationStillOpen
        operatorMeasureCompatibilityTheoremReviewSurface
    hardPhysicalBoundaryVisible :=
      compactPlaquetteConstructionTheoremReviewSurface.concreteLatticeGaugePlaquetteStillOpen
        compactPlaquetteConstructionTheoremReviewSurface ∧
      operatorMeasureCompatibilityTheoremReviewSurface.concreteOperatorMeasureRealizationStillOpen
        operatorMeasureCompatibilityTheoremReviewSurface
    exactValuePreserved := exactGapValueReal_eq
    reviewLevelOnly :=
      observableAtomTheoremTheoremReviewSurface.concretePlaquetteConstructionStillOpen
        observableAtomTheoremTheoremReviewSurface ∧
      observableAtomTheoremTheoremReviewSurface.concreteOperatorMeasureCompatibilityStillOpen
        observableAtomTheoremTheoremReviewSurface ∧
      compactPlaquetteConstructionTheoremReviewSurface.concreteLatticeGaugePlaquetteStillOpen
        compactPlaquetteConstructionTheoremReviewSurface ∧
      operatorMeasureCompatibilityTheoremReviewSurface.concreteOperatorMeasureRealizationStillOpen
        operatorMeasureCompatibilityTheoremReviewSurface
    publicBoundaryHeld :=
      observableAtomTheoremTheoremReviewSurface.publicBoundaryHeld
        observableAtomTheoremTheoremReviewSurface ∧
      compactPlaquetteConstructionTheoremReviewSurface.publicBoundaryHeld
        compactPlaquetteConstructionTheoremReviewSurface ∧
      operatorMeasureCompatibilityTheoremReviewSurface.publicBoundaryHeld
        operatorMeasureCompatibilityTheoremReviewSurface ∧
      exactGapTheoremBodyClosure.publicBoundaryHeld
    finalReleaseHeld :=
      observableAtomTheoremTheoremReviewSurface.finalReleaseHeld
        observableAtomTheoremTheoremReviewSurface ∧
      compactPlaquetteConstructionTheoremReviewSurface.finalReleaseHeld
        compactPlaquetteConstructionTheoremReviewSurface ∧
      operatorMeasureCompatibilityTheoremReviewSurface.finalReleaseHeld
        operatorMeasureCompatibilityTheoremReviewSurface ∧
      exactGapTheoremBodyClosure.finalReleaseHeld }

/-- The installed plaquette spectral-weight hardening lane is ready. -/
theorem plaquette_spectral_weight_lane_hardening_ready :
    plaquetteSpectralWeightLaneHardeningData.ready := by
  rcases observable_atom_theorem_theorem_review_surface_ready with
    ⟨_, _, _, _, _, _, _, _, _, _, hObsPlaquetteOpen, hObsOperatorOpen, hObsFinal, hObsPublic⟩
  rcases compact_plaquette_construction_theorem_review_surface_ready with
    ⟨_, _, _, _, _, _, _, hCompactPlaquetteOpen, hCompactFinal, hCompactPublic⟩
  rcases operator_measure_compatibility_theorem_review_surface_ready with
    ⟨_, _, _, _, _, _, hOperatorOpen, hOperatorFinal, hOperatorPublic⟩
  exact And.intro plaquetteSpectralWeightLaneHardeningData.continuumYMLaneReady <|
    And.intro plaquetteSpectralWeightLaneHardeningData.observableAtomReady <|
    And.intro plaquetteSpectralWeightLaneHardeningData.compactPlaquetteReady <|
    And.intro plaquetteSpectralWeightLaneHardeningData.operatorMeasureReady <|
    And.intro plaquetteSpectralWeightLaneHardeningData.exactBodyClosureReady <|
    And.intro singleton_observable_atom_theorem_compact_support <|
    And.intro singleton_observable_atom_theorem_centered <|
    And.intro singleton_observable_atom_theorem_smeared <|
    And.intro compact_plaquette_construction_theorem_review_surface_ready <|
    And.intro observable_atom_theorem_theorem_review_surface_ready <|
    And.intro singleton_operator_measure_compatibility_positive_weight <|
    And.intro singleton_operator_measure_compatibility_nonzero_weight <|
    And.intro singleton_operator_measure_compatibility_weight_equals_pvm_mass <|
    And.intro operator_measure_compatibility_theorem_review_surface_ready <|
    And.intro exact_gap_theorem_body_closure_ready <|
    And.intro hCompactPlaquetteOpen <|
    And.intro hOperatorOpen <|
    And.intro (And.intro hCompactPlaquetteOpen hOperatorOpen) <|
    And.intro plaquetteSpectralWeightLaneHardeningData.exactValuePreserved <|
    And.intro (And.intro hObsPlaquetteOpen <|
      And.intro hObsOperatorOpen <|
        And.intro hCompactPlaquetteOpen hOperatorOpen) <|
    And.intro
      (And.intro hObsPublic <|
        And.intro hCompactPublic <|
          And.intro hOperatorPublic exact_gap_theorem_body_closure_public_boundary_held) <|
    And.intro hObsFinal <|
      And.intro hCompactFinal <|
        And.intro hOperatorFinal exact_gap_theorem_body_closure_final_release_held

end MathlibAnalytic
end MGAP4D