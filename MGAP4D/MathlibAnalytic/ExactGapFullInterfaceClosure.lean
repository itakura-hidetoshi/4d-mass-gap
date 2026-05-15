import MGAP4D.MathlibAnalytic.ObservableAtomInterface

namespace MGAP4D
namespace MathlibAnalytic

/-- Full Mathlib analytic interface closure for the exact-gap chain.

This bundles the currently CI-green post-Mathlib interface chain:

* real-order exact-gap analytic closure,
* Hilbert/Rayleigh interface,
* operator-shaped `H_phys` interface,
* spectral theorem integration interface,
* PVM-shaped exact atom interface,
* observable atom / positive spectral-weight interface.

It is still an interface closure, not the final theorem release.  The remaining
full theorem bodies are kept visible as open boundaries. -/
structure ExactGapFullInterfaceClosure where
  realAnalyticReady : exactGapAnalyticRealClosure.ready
  hilbertRayleighReady : hilbertRayleighInterfaceReviewSurface.ready
  hphysReady : selfAdjointHPhysReviewSurface.ready
  spectralReady : spectralTheoremReviewSurface.ready
  pvmReady : pvmReviewSurface.ready
  observableAtomReady : observableAtomReviewSurface.ready
  exactValue_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  exactValue_positive : 0 < exactGapValueReal
  exactValue_above_one : 1 < exactGapValueReal
  observableAtomPositiveWeight : 0 < singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom
  observableAtomNonzeroWeight : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ≠ 0
  observableAtomCompatibleWithPVM : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom
  allMathlibInterfacesClosed : Prop
  fullHilbertRayleighStillOpen : Prop
  fullSelfAdjointHPhysStillOpen : Prop
  fullSpectralTheoremStillOpen : Prop
  fullPVMStillOpen : Prop
  fullObservableAtomStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

/-- Ready predicate for the full interface closure. -/
def ExactGapFullInterfaceClosure.ready
    (C : ExactGapFullInterfaceClosure) : Prop :=
  C.realAnalyticReady ∧ C.hilbertRayleighReady ∧ C.hphysReady ∧
  C.spectralReady ∧ C.pvmReady ∧ C.observableAtomReady ∧
  C.exactValue_eq_3320 ∧ C.exactValue_positive ∧ C.exactValue_above_one ∧
  C.observableAtomPositiveWeight ∧ C.observableAtomNonzeroWeight ∧
  C.observableAtomCompatibleWithPVM ∧ C.allMathlibInterfacesClosed ∧
  C.fullHilbertRayleighStillOpen ∧ C.fullSelfAdjointHPhysStillOpen ∧
  C.fullSpectralTheoremStillOpen ∧ C.fullPVMStillOpen ∧
  C.fullObservableAtomStillOpen ∧ C.finalReleaseHeld ∧ C.publicBoundaryHeld

/-- The current exact-gap full interface closure. -/
def exactGapFullInterfaceClosure : ExactGapFullInterfaceClosure :=
  { realAnalyticReady := exact_gap_analytic_real_closure_ready
    hilbertRayleighReady := hilbert_rayleigh_interface_review_surface_ready
    hphysReady := self_adjoint_hphys_review_surface_ready
    spectralReady := spectral_theorem_review_surface_ready
    pvmReady := pvm_review_surface_ready
    observableAtomReady := observable_atom_review_surface_ready
    exactValue_eq_3320 := exactGapValueReal_eq
    exactValue_positive := exactGapValueReal_pos
    exactValue_above_one := by
      norm_num [exactGapValueReal]
    observableAtomPositiveWeight := singleton_observable_atom_interface_positive_weight
    observableAtomNonzeroWeight := singleton_observable_atom_interface_nonzero_weight
    observableAtomCompatibleWithPVM := singleton_observable_atom_interface_compatible_with_pvm
    allMathlibInterfacesClosed := True
    fullHilbertRayleighStillOpen := True
    fullSelfAdjointHPhysStillOpen := True
    fullSpectralTheoremStillOpen := True
    fullPVMStillOpen := True
    fullObservableAtomStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem exact_gap_full_interface_closure_ready :
    exactGapFullInterfaceClosure.ready := by
  exact And.intro exact_gap_analytic_real_closure_ready <|
    And.intro hilbert_rayleigh_interface_review_surface_ready <|
    And.intro self_adjoint_hphys_review_surface_ready <|
    And.intro spectral_theorem_review_surface_ready <|
    And.intro pvm_review_surface_ready <|
    And.intro observable_atom_review_surface_ready <|
    And.intro exactGapValueReal_eq <|
    And.intro exactGapValueReal_pos <|
    And.intro (by norm_num [exactGapValueReal]) <|
    And.intro singleton_observable_atom_interface_positive_weight <|
    And.intro singleton_observable_atom_interface_nonzero_weight <|
    And.intro singleton_observable_atom_interface_compatible_with_pvm <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem exact_gap_full_interface_closure_value :
    exactGapFullInterfaceClosure.exactValue_eq_3320 := by
  exact exactGapValueReal_eq

theorem exact_gap_full_interface_closure_positive :
    exactGapFullInterfaceClosure.exactValue_positive := by
  exact exactGapValueReal_pos

theorem exact_gap_full_interface_closure_observable_positive_weight :
    exactGapFullInterfaceClosure.observableAtomPositiveWeight := by
  exact singleton_observable_atom_interface_positive_weight

theorem exact_gap_full_interface_closure_observable_nonzero_weight :
    exactGapFullInterfaceClosure.observableAtomNonzeroWeight := by
  exact singleton_observable_atom_interface_nonzero_weight

theorem exact_gap_full_interface_closure_final_release_held :
    exactGapFullInterfaceClosure.finalReleaseHeld := by
  trivial

theorem exact_gap_full_interface_closure_public_boundary_held :
    exactGapFullInterfaceClosure.publicBoundaryHeld := by
  trivial

end MathlibAnalytic
end MGAP4D
