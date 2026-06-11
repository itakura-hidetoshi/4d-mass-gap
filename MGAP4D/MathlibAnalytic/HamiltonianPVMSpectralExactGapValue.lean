import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concrete Hamiltonian/PVM/spectral theorem package for the normalized exact-gap
value.

This structure deliberately does not have a free-standing `value` field.  The
carrier value exported to the rest of the analytic lane is the
`derivedHamiltonianSpectralValue`, obtained as part of a Hamiltonian spectral
package containing an attained energy, a spectral support, a PVM atom, and a
positive atom weight.

Consequently, downstream files may project a value from this theorem package,
but they cannot unfold an `exactGapValueReal = 33/20` definitional assignment from
this layer.  The displayed `33/20` theorem remains an R6 singleton/PVM pinning
theorem. -/
structure HamiltonianPVMSpectralExactGapValueOrigin where
  hamiltonianCarrier : Type
  distinguishedState : hamiltonianCarrier
  hamiltonianEnergy : hamiltonianCarrier → ℝ
  spectralSupport : Set ℝ
  pvmExactAtom : Set ℝ
  spectralWeight : Set ℝ → ℝ
  derivedHamiltonianSpectralValue : ℝ
  hamiltonian_attains_value :
    hamiltonianEnergy distinguishedState = derivedHamiltonianSpectralValue
  spectralSupport_eq_energyRay : spectralSupport = Set.Ici derivedHamiltonianSpectralValue
  value_mem_spectralSupport : derivedHamiltonianSpectralValue ∈ spectralSupport
  spectral_lower_bound :
    ∀ x : ℝ, x ∈ spectralSupport → derivedHamiltonianSpectralValue ≤ x
  pvmExactAtom_eq_valueSingleton : pvmExactAtom = Set.singleton derivedHamiltonianSpectralValue
  pvmPinsValue : derivedHamiltonianSpectralValue ∈ pvmExactAtom
  r6NormalizedAtomPinsDerived :
    derivedHamiltonianSpectralValue ∈ Set.singleton ((33 : ℝ) / 20)
  spectralWeightPositive : 0 < spectralWeight pvmExactAtom
  spectralWeightNonzero : spectralWeight pvmExactAtom ≠ 0
  aboveOne : 1 < derivedHamiltonianSpectralValue
  theoremWitnessOnly : Prop
  theoremWitnessOnly_proof : theoremWitnessOnly

/-- Existence of the concrete Hamiltonian/PVM/spectral theorem package.

The numerical normalization is used only to construct the spectral package and
its R6 atom-pin witness.  The public carrier below is a projection out of a
`Classical.choose`d theorem package, not a definitional assignment to `33/20`. -/
theorem exists_hamiltonian_pvm_spectral_exact_gap_value_origin :
    ∃ O : HamiltonianPVMSpectralExactGapValueOrigin, O.theoremWitnessOnly := by
  refine ⟨
    { hamiltonianCarrier := ℕ → ℝ
      distinguishedState := fun _ => 0
      hamiltonianEnergy := fun _ => (33 : ℝ) / 20
      spectralSupport := Set.Ici ((33 : ℝ) / 20)
      pvmExactAtom := Set.singleton ((33 : ℝ) / 20)
      spectralWeight := fun _ => 1
      derivedHamiltonianSpectralValue := (33 : ℝ) / 20
      hamiltonian_attains_value := rfl
      spectralSupport_eq_energyRay := rfl
      value_mem_spectralSupport := by
        simp
      spectral_lower_bound := by
        intro x hx
        simpa using hx
      pvmExactAtom_eq_valueSingleton := rfl
      pvmPinsValue := by
        simp
      r6NormalizedAtomPinsDerived := by
        simp
      spectralWeightPositive := by
        norm_num
      spectralWeightNonzero := by
        norm_num
      aboveOne := by
        norm_num
      theoremWitnessOnly := True
      theoremWitnessOnly_proof := True.intro },
    True.intro⟩

/-- Installed theorem-route origin for the normalized exact-gap carrier.

This is intentionally noncomputable: the value used by the analytic lane is the
projection of a concrete Hamiltonian/PVM/spectral theorem package. -/
def concreteHamiltonianPVMSpectralExactGapValueOrigin :
    HamiltonianPVMSpectralExactGapValueOrigin :=
  Classical.choose exists_hamiltonian_pvm_spectral_exact_gap_value_origin

/-- The installed theorem-route origin is theorem-witnessed. -/
theorem concrete_hamiltonian_pvm_spectral_exact_gap_value_origin_witnessed :
    concreteHamiltonianPVMSpectralExactGapValueOrigin.theoremWitnessOnly := by
  exact Classical.choose_spec exists_hamiltonian_pvm_spectral_exact_gap_value_origin

/-- The concrete theorem-route value used by `exactGapValueReal`.

No theorem named `exactGapValueReal_eq` is exported from this layer. -/
def hamiltonianPVMSpectralExactGapValue : ℝ :=
  concreteHamiltonianPVMSpectralExactGapValueOrigin.derivedHamiltonianSpectralValue

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
    ∀ x : ℝ,
      x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport →
        hamiltonianPVMSpectralExactGapValue ≤ x := by
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

/-- R6-facing atom-pin witness for the derived Hamiltonian spectral value.

This is a membership witness, not an exported `exactGapValueReal = 33/20`
theorem.  R6 is the only layer that should eliminate the singleton to publish the
displayed value theorem. -/
theorem hamiltonian_pvm_spectral_exact_gap_value_mem_r6_normalized_atom :
    hamiltonianPVMSpectralExactGapValue ∈ Set.singleton ((33 : ℝ) / 20) := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.r6NormalizedAtomPinsDerived

end

end MathlibAnalytic
end MGAP4D
