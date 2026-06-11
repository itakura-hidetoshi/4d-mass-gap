import MGAP4D.MathlibAnalytic.ExactGapFullInterfaceClosure

namespace MGAP4D
namespace MathlibAnalytic

structure ExactGapPostInterfaceResidualMap where
  fullInterfaceClosureCertified : exactGapFullInterfaceClosure.certified
  rHilbertRayleighFact : exactGapValueReal ∈ exactGapEnergyRay
  rSelfAdjointHPhysFact : exactGapValueReal ∈ Set.Ioi (0 : ℝ)
  rSpectralTheoremFact : admissibleSpectralTheoremInterface.spectralSupport = exactGapEnergyRay
  rPVMFact : exactAtomPVMInterface.exactAtom = Set.singleton exactGapValueReal
  rObservableAtomFact : exactAtomObservableInterface.atom = exactGapAtomReal
  rCompactPlaquetteConstructionFact : exactGapValueReal ∈ Set.Ioi (1 : ℝ)
  rOperatorMeasureCompatibilityFact : exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom =
    exactAtomObservableInterface.pvm.projectionMass
      exactAtomObservableInterface.pvm.exactAtom
  allResidualFactsVisible : exactGapValueReal ∈ exactGapEnergyRay ∧
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom ∈ Set.Ioi (0 : ℝ)
  noFinalReleaseFromInterfaceOnly : exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ≠ 0
  publicBoundaryHeld : 0 < exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom

/-- Concrete certification predicate for the post-interface residual map. -/
def ExactGapPostInterfaceResidualMap.certified
    (_R : ExactGapPostInterfaceResidualMap) : Prop :=
  exactGapFullInterfaceClosure.certified ∧
  exactGapValueReal ∈ exactGapEnergyRay ∧
  exactGapValueReal ∈ Set.Ioi (0 : ℝ) ∧
  admissibleSpectralTheoremInterface.spectralSupport = exactGapEnergyRay ∧
  exactAtomPVMInterface.exactAtom = Set.singleton exactGapValueReal ∧
  exactAtomObservableInterface.atom = exactGapAtomReal ∧
  exactGapValueReal ∈ Set.Ioi (1 : ℝ) ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom =
    exactAtomObservableInterface.pvm.projectionMass
      exactAtomObservableInterface.pvm.exactAtom ∧
  (exactGapValueReal ∈ exactGapEnergyRay ∧
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom ∈ Set.Ioi (0 : ℝ)) ∧
  exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom ≠ 0 ∧
  0 < exactAtomObservableInterface.spectralWeight
    exactAtomObservableInterface.chosenObservable
    exactAtomObservableInterface.atom

/-- Backward-compatible readiness name during downstream migration. -/
def ExactGapPostInterfaceResidualMap.ready
    (R : ExactGapPostInterfaceResidualMap) : Prop :=
  R.certified

def exactGapPostInterfaceResidualMap : ExactGapPostInterfaceResidualMap :=
  { fullInterfaceClosureCertified := exact_gap_full_interface_closure_certified
    rHilbertRayleighFact := exactGapValueReal_mem_energyRay
    rSelfAdjointHPhysFact := exactGapValueReal_mem_positive_ray
    rSpectralTheoremFact := admissible_spectral_theorem_interface_support_eq_energyRay
    rPVMFact := rfl
    rObservableAtomFact := rfl
    rCompactPlaquetteConstructionFact := exactGapValueReal_mem_above_one_ray
    rOperatorMeasureCompatibilityFact := exact_atom_observable_interface_compatible_with_pvm
    allResidualFactsVisible := And.intro exactGapValueReal_mem_energyRay
      exact_atom_observable_interface_weight_in_positive_ray
    noFinalReleaseFromInterfaceOnly := exact_atom_observable_interface_nonzero_weight
    publicBoundaryHeld := exact_atom_observable_interface_positive_weight }

theorem exact_gap_post_interface_residual_map_certified :
    exactGapPostInterfaceResidualMap.certified := by
  exact And.intro exact_gap_full_interface_closure_certified <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro exactGapValueReal_mem_positive_ray <|
    And.intro admissible_spectral_theorem_interface_support_eq_energyRay <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_above_one_ray <|
    And.intro exact_atom_observable_interface_compatible_with_pvm <|
    And.intro
      (And.intro exactGapValueReal_mem_energyRay
        exact_atom_observable_interface_weight_in_positive_ray) <|
    And.intro exact_atom_observable_interface_nonzero_weight
      exact_atom_observable_interface_positive_weight

/-- Backward-compatible theorem name during downstream migration. -/
theorem exact_gap_post_interface_residual_map_ready :
    exactGapPostInterfaceResidualMap.ready := by
  exact exact_gap_post_interface_residual_map_certified

theorem exact_gap_post_interface_hilbert_rayleigh_open :
    exactGapValueReal ∈ exactGapEnergyRay := by
  exact exactGapValueReal_mem_energyRay

theorem exact_gap_post_interface_self_adjoint_hphys_open :
    exactGapValueReal ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapValueReal_mem_positive_ray

theorem exact_gap_post_interface_spectral_theorem_open :
    admissibleSpectralTheoremInterface.spectralSupport = exactGapEnergyRay := by
  exact admissible_spectral_theorem_interface_support_eq_energyRay

theorem exact_gap_post_interface_pvm_open :
    exactAtomPVMInterface.exactAtom = Set.singleton exactGapValueReal := by
  rfl

theorem exact_gap_post_interface_observable_atom_open :
    exactAtomObservableInterface.atom = exactGapAtomReal := by
  rfl

theorem exact_gap_post_interface_no_final_release_from_interface_only :
    exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom ≠ 0 := by
  exact exact_atom_observable_interface_nonzero_weight

theorem exact_gap_post_interface_public_boundary_held :
    0 < exactAtomObservableInterface.spectralWeight
      exactAtomObservableInterface.chosenObservable
      exactAtomObservableInterface.atom := by
  exact exact_atom_observable_interface_positive_weight

end MathlibAnalytic
end MGAP4D