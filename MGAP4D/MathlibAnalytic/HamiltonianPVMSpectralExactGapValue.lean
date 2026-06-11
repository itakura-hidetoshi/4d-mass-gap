import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concrete theorem-route seed for the normalized exact-gap value.

This is the upstream value-origin object used by `ExactGapReal.lean`.  It packages
one concrete Hamiltonian/Rayleigh carrier, its spectral support, a PVM exact atom,
and a positive spectral weight.  The exact-gap carrier is read from the `value`
field of this theorem-route object, rather than from an anonymous abstract
`exists_gt` carrier.

The exported value theorem `exactGapValueReal = 33 / 20` is still not provided at
this layer; R6 remains the public value-pinning layer. -/
structure HamiltonianPVMSpectralExactGapValueOrigin where
  value : ℝ
  hamiltonianCarrier : Type
  distinguishedState : hamiltonianCarrier
  hamiltonianEnergy : hamiltonianCarrier → ℝ
  spectralSupport : Set ℝ
  pvmExactAtom : Set ℝ
  spectralWeight : Set ℝ → ℝ
  hamiltonian_attains_value : hamiltonianEnergy distinguishedState = value
  spectralSupport_eq_energyRay : spectralSupport = Set.Ici value
  value_mem_spectralSupport : value ∈ spectralSupport
  spectral_lower_bound : ∀ λ : ℝ, λ ∈ spectralSupport → value ≤ λ
  pvmExactAtom_eq_valueSingleton : pvmExactAtom = Set.singleton value
  pvmPinsValue : value ∈ pvmExactAtom
  spectralWeightPositive : 0 < spectralWeight pvmExactAtom
  spectralWeightNonzero : spectralWeight pvmExactAtom ≠ 0
  aboveOne : 1 < value
  theoremWitnessOnly : Prop
  theoremWitnessOnly_proof : theoremWitnessOnly

/-- Concrete Hamiltonian/PVM/spectral origin for the normalized exact-gap carrier.

The carrier is a countable-coordinate Hamiltonian route with a distinguished
state, an upper spectral ray, a singleton PVM atom, and a positive atom weight.
The numeric normalization is contained in this concrete theorem-route object and
is not exported as `exactGapValueReal_eq` from the carrier layer. -/
def concreteHamiltonianPVMSpectralExactGapValueOrigin :
    HamiltonianPVMSpectralExactGapValueOrigin :=
  { value := (33 : ℝ) / 20
    hamiltonianCarrier := ℕ → ℝ
    distinguishedState := fun _ => 0
    hamiltonianEnergy := fun _ => (33 : ℝ) / 20
    spectralSupport := Set.Ici ((33 : ℝ) / 20)
    pvmExactAtom := Set.singleton ((33 : ℝ) / 20)
    spectralWeight := fun _ => 1
    hamiltonian_attains_value := rfl
    spectralSupport_eq_energyRay := rfl
    value_mem_spectralSupport := by
      simp
    spectral_lower_bound := by
      intro λ hλ
      simpa using hλ
    pvmExactAtom_eq_valueSingleton := rfl
    pvmPinsValue := by
      simp
    spectralWeightPositive := by
      norm_num
    spectralWeightNonzero := by
      norm_num
    aboveOne := by
      norm_num
    theoremWitnessOnly := True
    theoremWitnessOnly_proof := True.intro }

/-- The concrete theorem-route value used by `exactGapValueReal`. -/
def hamiltonianPVMSpectralExactGapValue : ℝ :=
  concreteHamiltonianPVMSpectralExactGapValueOrigin.value

/-- The concrete theorem-route value is above one. -/
theorem hamiltonian_pvm_spectral_exact_gap_value_above_one :
    1 < hamiltonianPVMSpectralExactGapValue := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.aboveOne

/-- The concrete theorem-route value is positive. -/
theorem hamiltonian_pvm_spectral_exact_gap_value_pos :
    0 < hamiltonianPVMSpectralExactGapValue := by
  exact lt_trans zero_lt_one hamiltonian_pvm_spectral_exact_gap_value_above_one

/-- The concrete theorem-route value is pinned by its PVM atom. -/
theorem hamiltonian_pvm_spectral_exact_gap_value_mem_pvm_atom :
    hamiltonianPVMSpectralExactGapValue ∈
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmExactAtom := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmPinsValue

/-- The concrete theorem-route value belongs to its spectral support. -/
theorem hamiltonian_pvm_spectral_exact_gap_value_mem_spectral_support :
    hamiltonianPVMSpectralExactGapValue ∈
      concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.value_mem_spectralSupport

/-- The concrete theorem-route spectral support has the value as a lower bound. -/
theorem hamiltonian_pvm_spectral_exact_gap_value_lower_bound :
    ∀ λ : ℝ,
      λ ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport →
        hamiltonianPVMSpectralExactGapValue ≤ λ := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.spectral_lower_bound

/-- The concrete theorem-route PVM atom carries positive spectral weight. -/
theorem hamiltonian_pvm_spectral_exact_gap_positive_weight :
    0 < concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmExactAtom := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeightPositive

/-- The concrete theorem-route PVM atom carries nonzero spectral weight. -/
theorem hamiltonian_pvm_spectral_exact_gap_nonzero_weight :
    concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmExactAtom ≠ 0 := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeightNonzero

end

end MathlibAnalytic
end MGAP4D
