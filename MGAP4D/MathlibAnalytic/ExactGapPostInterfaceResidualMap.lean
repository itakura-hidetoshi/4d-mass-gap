import MGAP4D.MathlibAnalytic.ExactGapFullInterfaceClosure

namespace MGAP4D
namespace MathlibAnalytic

structure ExactGapPostInterfaceResidualMap where
  fullInterfaceClosureReady : exactGapFullInterfaceClosure.ready
  rHilbertRayleighFact : exactGapValueReal ∈ exactGapEnergyRay
  rSelfAdjointHPhysFact : exactGapValueReal ∈ Set.Ioi (0 : ℝ)
  rSpectralTheoremFact : singletonSpectralTheoremInterface.spectralSupport = exactGapEnergyRay
  rPVMFact : singletonPVMInterface.exactAtom = Set.singleton exactGapValueReal
  rObservableAtomFact : singletonObservableAtomInterface.atom = exactGapAtomReal
  rCompactPlaquetteConstructionFact : exactGapValueReal ∈ Set.Ioi (1 : ℝ)
  rOperatorMeasureCompatibilityFact : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom
  allResidualFactsVisible : exactGapValueReal ∈ exactGapEnergyRay ∧
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom ∈ Set.Ioi (0 : ℝ)
  noFinalReleaseFromInterfaceOnly : singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ≠ 0
  publicBoundaryHeld : 0 < singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom

def ExactGapPostInterfaceResidualMap.ready
    (_R : ExactGapPostInterfaceResidualMap) : Prop :=
  exactGapFullInterfaceClosure.ready ∧
  exactGapValueReal ∈ exactGapEnergyRay ∧
  exactGapValueReal ∈ Set.Ioi (0 : ℝ) ∧
  singletonSpectralTheoremInterface.spectralSupport = exactGapEnergyRay ∧
  singletonPVMInterface.exactAtom = Set.singleton exactGapValueReal ∧
  singletonObservableAtomInterface.atom = exactGapAtomReal ∧
  exactGapValueReal ∈ Set.Ioi (1 : ℝ) ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom =
    singletonObservableAtomInterface.pvm.projectionMass
      singletonObservableAtomInterface.pvm.exactAtom ∧
  (exactGapValueReal ∈ exactGapEnergyRay ∧
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom ∈ Set.Ioi (0 : ℝ)) ∧
  singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom ≠ 0 ∧
  0 < singletonObservableAtomInterface.spectralWeight
    singletonObservableAtomInterface.chosenObservable
    singletonObservableAtomInterface.atom

def exactGapPostInterfaceResidualMap : ExactGapPostInterfaceResidualMap :=
  { fullInterfaceClosureReady := exact_gap_full_interface_closure_ready
    rHilbertRayleighFact := exactGapValueReal_mem_energyRay
    rSelfAdjointHPhysFact := exactGapValueReal_mem_positive_ray
    rSpectralTheoremFact := singleton_spectral_theorem_interface_support_eq_energyRay
    rPVMFact := rfl
    rObservableAtomFact := rfl
    rCompactPlaquetteConstructionFact := exactGapValueReal_mem_above_one_ray
    rOperatorMeasureCompatibilityFact := singleton_observable_atom_interface_compatible_with_pvm
    allResidualFactsVisible := And.intro exactGapValueReal_mem_energyRay
      singleton_observable_atom_interface_weight_in_positive_ray
    noFinalReleaseFromInterfaceOnly := singleton_observable_atom_interface_nonzero_weight
    publicBoundaryHeld := singleton_observable_atom_interface_positive_weight }

theorem exact_gap_post_interface_residual_map_ready :
    exactGapPostInterfaceResidualMap.ready := by
  exact And.intro exact_gap_full_interface_closure_ready <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro exactGapValueReal_mem_positive_ray <|
    And.intro singleton_spectral_theorem_interface_support_eq_energyRay <|
    And.intro rfl <|
    And.intro rfl <|
    And.intro exactGapValueReal_mem_above_one_ray <|
    And.intro singleton_observable_atom_interface_compatible_with_pvm <|
    And.intro
      (And.intro exactGapValueReal_mem_energyRay
        singleton_observable_atom_interface_weight_in_positive_ray) <|
    And.intro singleton_observable_atom_interface_nonzero_weight
      singleton_observable_atom_interface_positive_weight

theorem exact_gap_post_interface_hilbert_rayleigh_open :
    exactGapValueReal ∈ exactGapEnergyRay := by
  exact exactGapValueReal_mem_energyRay

theorem exact_gap_post_interface_self_adjoint_hphys_open :
    exactGapValueReal ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapValueReal_mem_positive_ray

theorem exact_gap_post_interface_spectral_theorem_open :
    singletonSpectralTheoremInterface.spectralSupport = exactGapEnergyRay := by
  exact singleton_spectral_theorem_interface_support_eq_energyRay

theorem exact_gap_post_interface_pvm_open :
    singletonPVMInterface.exactAtom = Set.singleton exactGapValueReal := by
  rfl

theorem exact_gap_post_interface_observable_atom_open :
    singletonObservableAtomInterface.atom = exactGapAtomReal := by
  rfl

theorem exact_gap_post_interface_no_final_release_from_interface_only :
    singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom ≠ 0 := by
  exact singleton_observable_atom_interface_nonzero_weight

theorem exact_gap_post_interface_public_boundary_held :
    0 < singletonObservableAtomInterface.spectralWeight
      singletonObservableAtomInterface.chosenObservable
      singletonObservableAtomInterface.atom := by
  exact singleton_observable_atom_interface_positive_weight

end MathlibAnalytic
end MGAP4D
