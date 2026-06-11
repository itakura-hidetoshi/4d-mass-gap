import MGAP4D.MathlibAnalytic.ObservableAtomInterface

namespace MGAP4D
namespace MathlibAnalytic

structure ExactGapFullInterfaceClosure where
  realAnalyticCertified : exactGapAnalyticRealClosure.certified
  hilbertRayleighCertified : hilbertRayleighInterfaceReviewSurface.certified
  hphysCertified : selfAdjointHPhysReviewSurface.certified
  spectralCertified : spectralTheoremReviewSurface.certified
  pvmCertified : pvmReviewSurface.certified
  observableAtomCertified : observableAtomReviewSurface.certified
  exactValue_positive : 0 < exactGapValueReal
  exactValue_above_one : 1 < exactGapValueReal
  exactValue_in_energyRay : exactGapValueReal ∈ exactGapEnergyRay
  exactValue_in_positive_ray : exactGapValueReal ∈ Set.Ioi (0 : ℝ)
  observableAtomPositiveWeight : 0 < exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom
  observableAtomNonzeroWeight : exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ≠ 0
  observableAtomWeightInPositiveRay : exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ∈ Set.Ioi (0 : ℝ)
  observableAtomCompatibleWithPVM : exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom =
    exactAtomObservableInterface.pvm.projectionMass
      exactAtomObservableInterface.pvm.exactAtom
  observableAtom_def : exactAtomObservableInterface.atom = exactGapAtomReal
  pvmExactAtom_def : exactAtomPVMInterface.exactAtom = Set.singleton exactGapValueReal

/-- Concrete certification predicate for the full interface closure. -/
def ExactGapFullInterfaceClosure.certified (_C : ExactGapFullInterfaceClosure) : Prop :=
  exactGapAnalyticRealClosure.certified ∧
  hilbertRayleighInterfaceReviewSurface.certified ∧
  selfAdjointHPhysReviewSurface.certified ∧
  spectralTheoremReviewSurface.certified ∧
  pvmReviewSurface.certified ∧
  observableAtomReviewSurface.certified ∧
  0 < exactGapValueReal ∧
  1 < exactGapValueReal ∧
  exactGapValueReal ∈ exactGapEnergyRay ∧
  exactGapValueReal ∈ Set.Ioi (0 : ℝ) ∧
  0 < exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ≠ 0 ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ∈ Set.Ioi (0 : ℝ) ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom =
    exactAtomObservableInterface.pvm.projectionMass
      exactAtomObservableInterface.pvm.exactAtom ∧
  exactAtomObservableInterface.atom = exactGapAtomReal ∧
  exactAtomPVMInterface.exactAtom = Set.singleton exactGapValueReal

/-- Backward-compatible readiness name during downstream migration. -/
def ExactGapFullInterfaceClosure.ready (C : ExactGapFullInterfaceClosure) : Prop :=
  C.certified

noncomputable def exactGapFullInterfaceClosure : ExactGapFullInterfaceClosure :=
  { realAnalyticCertified := exact_gap_analytic_real_closure_certified
    hilbertRayleighCertified := hilbert_rayleigh_interface_review_surface_certified
    hphysCertified := self_adjoint_hphys_review_surface_certified
    spectralCertified := spectral_theorem_review_surface_certified
    pvmCertified := pvm_review_surface_certified
    observableAtomCertified := observable_atom_review_surface_certified
    exactValue_positive := exactGapValueReal_pos
    exactValue_above_one := exactGapValueReal_above_one
    exactValue_in_energyRay := exactGapValueReal_mem_energyRay
    exactValue_in_positive_ray := exactGapValueReal_mem_positive_ray
    observableAtomPositiveWeight := exact_atom_observable_interface_positive_weight
    observableAtomNonzeroWeight := exact_atom_observable_interface_nonzero_weight
    observableAtomWeightInPositiveRay := exact_atom_observable_interface_weight_in_positive_ray
    observableAtomCompatibleWithPVM := exact_atom_observable_interface_compatible_with_pvm
    observableAtom_def := rfl
    pvmExactAtom_def := rfl }

theorem exact_gap_full_interface_closure_certified :
    exactGapFullInterfaceClosure.certified := by
  exact ⟨
    exact_gap_analytic_real_closure_certified,
    hilbert_rayleigh_interface_review_surface_certified,
    self_adjoint_hphys_review_surface_certified,
    spectral_theorem_review_surface_certified,
    pvm_review_surface_certified,
    observable_atom_review_surface_certified,
    exactGapValueReal_pos,
    exactGapValueReal_above_one,
    exactGapValueReal_mem_energyRay,
    exactGapValueReal_mem_positive_ray,
    exact_atom_observable_interface_positive_weight,
    exact_atom_observable_interface_nonzero_weight,
    exact_atom_observable_interface_weight_in_positive_ray,
    exact_atom_observable_interface_compatible_with_pvm,
    rfl,
    rfl⟩

/-- Backward-compatible theorem name during downstream migration. -/
theorem exact_gap_full_interface_closure_ready :
    exactGapFullInterfaceClosure.ready := by
  exact exact_gap_full_interface_closure_certified

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
    0 < exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom := by
  exact exact_atom_observable_interface_positive_weight

theorem exact_gap_full_interface_closure_observable_nonzero_weight :
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom ≠ 0 := by
  exact exact_atom_observable_interface_nonzero_weight

theorem exact_gap_full_interface_closure_observable_weight_in_positive_ray :
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom ∈ Set.Ioi (0 : ℝ) := by
  exact exact_atom_observable_interface_weight_in_positive_ray

theorem exact_gap_full_interface_closure_observable_atom_def :
    exactAtomObservableInterface.atom = exactGapAtomReal := by
  rfl

end MathlibAnalytic
end MGAP4D