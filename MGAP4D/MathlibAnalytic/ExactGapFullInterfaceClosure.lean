import MGAP4D.MathlibAnalytic.ObservableAtomInterface

namespace MGAP4D
namespace MathlibAnalytic

inductive ExactGapFullInterfaceClosureMarker where
  | allMathlibInterfacesAssembled
  | hilbertRayleighDeferred
  | selfAdjointHPhysDeferred
  | spectralTheoremDeferred
  | pvmDeferred
  | observableAtomDeferred
  | finalReleaseHeld
  | publicBoundaryHeld
  deriving DecidableEq

structure ExactGapFullInterfaceClosure where
  realAnalyticReady : exactGapAnalyticRealClosure.ready
  hilbertRayleighReady : hilbertRayleighInterfaceReviewSurface.ready
  hphysReady : selfAdjointHPhysReviewSurface.ready
  spectralReady : spectralTheoremReviewSurface.ready
  pvmReady : pvmReviewSurface.ready
  observableAtomReady : observableAtomReviewSurface.ready
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
  allMathlibInterfacesAssembled : ExactGapFullInterfaceClosureMarker
  hilbertRayleighBoundary : ExactGapFullInterfaceClosureMarker
  selfAdjointHPhysBoundary : ExactGapFullInterfaceClosureMarker
  spectralTheoremBoundary : ExactGapFullInterfaceClosureMarker
  pvmBoundary : ExactGapFullInterfaceClosureMarker
  observableAtomBoundary : ExactGapFullInterfaceClosureMarker
  finalReleaseBoundary : ExactGapFullInterfaceClosureMarker
  publicBoundary : ExactGapFullInterfaceClosureMarker

def ExactGapFullInterfaceClosure.ready (C : ExactGapFullInterfaceClosure) : Prop :=
  exactGapAnalyticRealClosure.ready ∧
  hilbertRayleighInterfaceReviewSurface.ready ∧
  selfAdjointHPhysReviewSurface.ready ∧
  spectralTheoremReviewSurface.ready ∧
  pvmReviewSurface.ready ∧
  observableAtomReviewSurface.ready ∧
  0 < exactGapValueReal ∧
  1 < exactGapValueReal ∧
  0 < singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ≠ 0 ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom ∧
  C.allMathlibInterfacesAssembled = ExactGapFullInterfaceClosureMarker.allMathlibInterfacesAssembled ∧
  C.hilbertRayleighBoundary = ExactGapFullInterfaceClosureMarker.hilbertRayleighDeferred ∧
  C.selfAdjointHPhysBoundary = ExactGapFullInterfaceClosureMarker.selfAdjointHPhysDeferred ∧
  C.spectralTheoremBoundary = ExactGapFullInterfaceClosureMarker.spectralTheoremDeferred ∧
  C.pvmBoundary = ExactGapFullInterfaceClosureMarker.pvmDeferred ∧
  C.observableAtomBoundary = ExactGapFullInterfaceClosureMarker.observableAtomDeferred ∧
  C.finalReleaseBoundary = ExactGapFullInterfaceClosureMarker.finalReleaseHeld ∧
  C.publicBoundary = ExactGapFullInterfaceClosureMarker.publicBoundaryHeld

noncomputable def exactGapFullInterfaceClosure : ExactGapFullInterfaceClosure :=
  { realAnalyticReady := exact_gap_analytic_real_closure_ready
    hilbertRayleighReady := hilbert_rayleigh_interface_review_surface_ready
    hphysReady := self_adjoint_hphys_review_surface_ready
    spectralReady := spectral_theorem_review_surface_ready
    pvmReady := pvm_review_surface_ready
    observableAtomReady := observable_atom_review_surface_ready
    exactValue_positive := exactGapValueReal_pos
    exactValue_above_one := exactGapValueReal_above_one
    observableAtomPositiveWeight := singleton_observable_atom_interface_positive_weight
    observableAtomNonzeroWeight := singleton_observable_atom_interface_nonzero_weight
    observableAtomCompatibleWithPVM := singleton_observable_atom_interface_compatible_with_pvm
    allMathlibInterfacesAssembled := ExactGapFullInterfaceClosureMarker.allMathlibInterfacesAssembled
    hilbertRayleighBoundary := ExactGapFullInterfaceClosureMarker.hilbertRayleighDeferred
    selfAdjointHPhysBoundary := ExactGapFullInterfaceClosureMarker.selfAdjointHPhysDeferred
    spectralTheoremBoundary := ExactGapFullInterfaceClosureMarker.spectralTheoremDeferred
    pvmBoundary := ExactGapFullInterfaceClosureMarker.pvmDeferred
    observableAtomBoundary := ExactGapFullInterfaceClosureMarker.observableAtomDeferred
    finalReleaseBoundary := ExactGapFullInterfaceClosureMarker.finalReleaseHeld
    publicBoundary := ExactGapFullInterfaceClosureMarker.publicBoundaryHeld }

theorem exact_gap_full_interface_closure_ready :
    exactGapFullInterfaceClosure.ready := by
  exact ⟨
    exact_gap_analytic_real_closure_ready,
    hilbert_rayleigh_interface_review_surface_ready,
    self_adjoint_hphys_review_surface_ready,
    spectral_theorem_review_surface_ready,
    pvm_review_surface_ready,
    observable_atom_review_surface_ready,
    exactGapValueReal_pos,
    exactGapValueReal_above_one,
    singleton_observable_atom_interface_positive_weight,
    singleton_observable_atom_interface_nonzero_weight,
    singleton_observable_atom_interface_compatible_with_pvm,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl,
    rfl⟩

theorem exact_gap_full_interface_closure_value :
    exactGapValueReal = exactGapValueReal := by
  rfl

theorem exact_gap_full_interface_closure_positive :
    0 < exactGapValueReal := by
  exact exactGapValueReal_pos

theorem exact_gap_full_interface_closure_observable_positive_weight :
    0 < singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom := by
  exact singleton_observable_atom_interface_positive_weight

theorem exact_gap_full_interface_closure_observable_nonzero_weight :
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom ≠ 0 := by
  exact singleton_observable_atom_interface_nonzero_weight

theorem exact_gap_full_interface_closure_final_release_held :
    exactGapFullInterfaceClosure.finalReleaseBoundary =
      ExactGapFullInterfaceClosureMarker.finalReleaseHeld := by
  rfl

theorem exact_gap_full_interface_closure_public_boundary_held :
    exactGapFullInterfaceClosure.publicBoundary =
      ExactGapFullInterfaceClosureMarker.publicBoundaryHeld := by
  rfl

end MathlibAnalytic
end MGAP4D
