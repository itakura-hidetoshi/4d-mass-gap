import MGAP4D.MathlibAnalytic.ObservableAtomInterface

namespace MGAP4D
namespace MathlibAnalytic

structure ExactGapFullInterfaceClosure where
  realAnalyticReady : exactGapAnalyticRealClosure.ready
  hilbertRayleighReady : hilbertRayleighInterfaceReviewSurface.ready
  hphysReady : selfAdjointHPhysReviewSurface.ready
  spectralReady : spectralTheoremReviewSurface.ready
  pvmReady : pvmReviewSurface.ready
  observableAtomReady : observableAtomReviewSurface.ready
  exactValue_positive : 0 < exactGapValueReal
  exactValue_above_one : 1 < exactGapValueReal
  exactValue_in_energyRay : exactGapValueReal ∈ exactGapEnergyRay
  exactValue_in_positive_ray : exactGapValueReal ∈ Set.Ioi (0 : ℝ)
  observableAtomPositiveWeight : 0 < singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom
  observableAtomNonzeroWeight : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ≠ 0
  observableAtomWeightInPositiveRay : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ∈ Set.Ioi (0 : ℝ)
  observableAtomCompatibleWithPVM : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom
  observableAtom_def : singletonObservableAtomInterface.atom = exactGapAtomReal
  pvmExactAtom_def : singletonPVMInterface.exactAtom = Set.singleton exactGapValueReal

def ExactGapFullInterfaceClosure.ready (C : ExactGapFullInterfaceClosure) : Prop :=
  exactGapAnalyticRealClosure.ready ∧
  hilbertRayleighInterfaceReviewSurface.ready ∧
  selfAdjointHPhysReviewSurface.ready ∧
  spectralTheoremReviewSurface.ready ∧
  pvmReviewSurface.ready ∧
  observableAtomReviewSurface.ready ∧
  0 < exactGapValueReal ∧
  1 < exactGapValueReal ∧
  exactGapValueReal ∈ exactGapEnergyRay ∧
  exactGapValueReal ∈ Set.Ioi (0 : ℝ) ∧
  0 < singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ≠ 0 ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ∈ Set.Ioi (0 : ℝ) ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom ∧
  singletonObservableAtomInterface.atom = exactGapAtomReal ∧
  singletonPVMInterface.exactAtom = Set.singleton exactGapValueReal

noncomputable def exactGapFullInterfaceClosure : ExactGapFullInterfaceClosure :=
  { realAnalyticReady := exact_gap_analytic_real_closure_ready
    hilbertRayleighReady := hilbert_rayleigh_interface_review_surface_ready
    hphysReady := self_adjoint_hphys_review_surface_ready
    spectralReady := spectral_theorem_review_surface_ready
    pvmReady := pvm_review_surface_ready
    observableAtomReady := observable_atom_review_surface_ready
    exactValue_positive := exactGapValueReal_pos
    exactValue_above_one := exactGapValueReal_above_one
    exactValue_in_energyRay := exactGapValueReal_mem_energyRay
    exactValue_in_positive_ray := exactGapValueReal_mem_positive_ray
    observableAtomPositiveWeight := singleton_observable_atom_interface_positive_weight
    observableAtomNonzeroWeight := singleton_observable_atom_interface_nonzero_weight
    observableAtomWeightInPositiveRay := singleton_observable_atom_interface_weight_in_positive_ray
    observableAtomCompatibleWithPVM := singleton_observable_atom_interface_compatible_with_pvm
    observableAtom_def := rfl
    pvmExactAtom_def := rfl }

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
    exactGapValueReal_mem_energyRay,
    exactGapValueReal_mem_positive_ray,
    singleton_observable_atom_interface_positive_weight,
    singleton_observable_atom_interface_nonzero_weight,
    singleton_observable_atom_interface_weight_in_positive_ray,
    singleton_observable_atom_interface_compatible_with_pvm,
    rfl,
    rfl⟩

theorem exact_gap_full_interface_closure_value :
    exactGapValueReal = exactGapValueReal := by
  rfl

theorem exact_gap_full_interface_closure_positive :
    0 < exactGapValueReal := by
  exact exactGapValueReal_pos

theorem exact_gap_full_interface_closure_exact_value_in_energyRay :
    exactGapValueReal ∈ exactGapEnergyRay := by
  exact exactGapValueReal_mem_energyRay

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

theorem exact_gap_full_interface_closure_observable_weight_in_positive_ray :
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom ∈ Set.Ioi (0 : ℝ) := by
  exact singleton_observable_atom_interface_weight_in_positive_ray

theorem exact_gap_full_interface_closure_observable_atom_def :
    singletonObservableAtomInterface.atom = exactGapAtomReal := by
  rfl

end MathlibAnalytic
end MGAP4D
