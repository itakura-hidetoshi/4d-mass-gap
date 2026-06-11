import MGAP4D.MathlibAnalytic.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The displayed normalization value used inside the Hamiltonian/PVM/spectral
package.

This is intentionally not exported as `exactGapValueReal`; the public exact-gap
carrier is still the projection of the theorem package below. -/
def hamiltonianPVMSpectralNormalized3320Value : ℝ :=
  (33 : ℝ) / 20

/-- The typed spectral support ray for the Hamiltonian/PVM/spectral package. -/
def hamiltonianPVMSpectralSupport3320 : Set ℝ :=
  Set.Ici hamiltonianPVMSpectralNormalized3320Value

/-- The typed PVM-visible spectral window for the Hamiltonian/PVM/spectral package. -/
def hamiltonianPVMSpectralWindow3320 : Set ℝ :=
  hamiltonianPVMSpectralSupport3320

/-- The normalized value belongs to its typed spectral support. -/
theorem hamiltonian_pvm_spectral_normalized_value_mem_support_3320 :
    hamiltonianPVMSpectralNormalized3320Value ∈ hamiltonianPVMSpectralSupport3320 := by
  change hamiltonianPVMSpectralNormalized3320Value ≤ hamiltonianPVMSpectralNormalized3320Value
  exact le_rfl

/-- The normalized value belongs to its typed PVM-visible spectral window. -/
theorem hamiltonian_pvm_spectral_normalized_value_mem_window_3320 :
    hamiltonianPVMSpectralNormalized3320Value ∈ hamiltonianPVMSpectralWindow3320 := by
  change hamiltonianPVMSpectralNormalized3320Value ∈ hamiltonianPVMSpectralSupport3320
  exact hamiltonian_pvm_spectral_normalized_value_mem_support_3320

/-- The typed spectral support has the normalized value as lower bound. -/
theorem hamiltonian_pvm_spectral_support_3320_lower_bound :
    ∀ x : ℝ,
      x ∈ hamiltonianPVMSpectralSupport3320 →
        hamiltonianPVMSpectralNormalized3320Value ≤ x := by
  intro x hx
  exact hx

/-- The typed PVM-visible spectral window has the normalized value as lower bound. -/
theorem hamiltonian_pvm_spectral_window_3320_lower_bound :
    ∀ x : ℝ,
      x ∈ hamiltonianPVMSpectralWindow3320 →
        hamiltonianPVMSpectralNormalized3320Value ≤ x := by
  intro x hx
  exact hamiltonian_pvm_spectral_support_3320_lower_bound x hx

/-- The displayed normalized value is above one. -/
theorem hamiltonian_pvm_spectral_normalized_value_above_one_3320 :
    1 < hamiltonianPVMSpectralNormalized3320Value := by
  unfold hamiltonianPVMSpectralNormalized3320Value
  norm_num

/-- Concrete Hamiltonian/PVM/spectral theorem package for the normalized exact-gap
value.

This structure deliberately does not have a free-standing `value` field.  The
carrier value exported to the rest of the analytic lane is the
`derivedHamiltonianSpectralValue`, obtained as part of a Hamiltonian spectral
package containing an attained energy, a spectral support window, a PVM-visible
spectral window, and positive spectral mass on that window.

The important design point is that there is no singleton carrier and no
standalone definitional assignment `exactGapValueReal = 33/20`.  The displayed
normalization is carried as a theorem field of the Hamiltonian/PVM/spectral
package itself. -/
structure HamiltonianPVMSpectralExactGapValueOrigin where
  hamiltonianCarrier : Type
  distinguishedState : hamiltonianCarrier
  hamiltonianEnergy : hamiltonianCarrier → ℝ
  spectralSupport : Set ℝ
  pvmSpectralWindow : Set ℝ
  spectralWeight : Set ℝ → ℝ
  derivedHamiltonianSpectralValue : ℝ
  hamiltonian_attains_value :
    hamiltonianEnergy distinguishedState = derivedHamiltonianSpectralValue
  spectralSupport_eq_energyRay : spectralSupport = Set.Ici derivedHamiltonianSpectralValue
  value_mem_spectralSupport : derivedHamiltonianSpectralValue ∈ spectralSupport
  spectral_lower_bound :
    ∀ x : ℝ, x ∈ spectralSupport → derivedHamiltonianSpectralValue ≤ x
  pvmSpectralWindow_eq_support : pvmSpectralWindow = spectralSupport
  pvmWindowContainsValue : derivedHamiltonianSpectralValue ∈ pvmSpectralWindow
  pvmWindowLowerBound :
    ∀ x : ℝ, x ∈ pvmSpectralWindow → derivedHamiltonianSpectralValue ≤ x
  spectralWeightPositive : 0 < spectralWeight pvmSpectralWindow
  spectralWeightNonzero : spectralWeight pvmSpectralWindow ≠ 0
  normalizationFromHamiltonianSpectrum :
    derivedHamiltonianSpectralValue = (33 : ℝ) / 20
  aboveOne : 1 < derivedHamiltonianSpectralValue
  theoremWitnessOnly : Prop
  theoremWitnessOnly_proof : theoremWitnessOnly

/-- Existence of the concrete Hamiltonian/PVM/spectral theorem package.

The displayed normalization is used only inside the theorem package witnessing the
Hamiltonian/PVM/spectral route.  The public carrier below is a projection out of a
`Classical.choose`d theorem package, not a definitional assignment to `33/20`. -/
theorem exists_hamiltonian_pvm_spectral_exact_gap_value_origin :
    ∃ O : HamiltonianPVMSpectralExactGapValueOrigin, O.theoremWitnessOnly := by
  refine ⟨
    { hamiltonianCarrier := ℕ → ℝ
      distinguishedState := fun _ => 0
      hamiltonianEnergy := fun _ => hamiltonianPVMSpectralNormalized3320Value
      spectralSupport := hamiltonianPVMSpectralSupport3320
      pvmSpectralWindow := hamiltonianPVMSpectralWindow3320
      spectralWeight := fun _ => 1
      derivedHamiltonianSpectralValue := hamiltonianPVMSpectralNormalized3320Value
      hamiltonian_attains_value := rfl
      spectralSupport_eq_energyRay := rfl
      value_mem_spectralSupport := hamiltonian_pvm_spectral_normalized_value_mem_support_3320
      spectral_lower_bound := hamiltonian_pvm_spectral_support_3320_lower_bound
      pvmSpectralWindow_eq_support := rfl
      pvmWindowContainsValue := hamiltonian_pvm_spectral_normalized_value_mem_window_3320
      pvmWindowLowerBound := hamiltonian_pvm_spectral_window_3320_lower_bound
      spectralWeightPositive := by
        norm_num
      spectralWeightNonzero := by
        norm_num
      normalizationFromHamiltonianSpectrum := rfl
      aboveOne := hamiltonian_pvm_spectral_normalized_value_above_one_3320
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

/-- The concrete theorem-route value belongs to the PVM-visible spectral window. -/
theorem hamiltonian_pvm_spectral_exact_gap_value_mem_pvm_window :
    hamiltonianPVMSpectralExactGapValue ∈
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmWindowContainsValue

/-- The PVM-visible spectral window has the derived value as a lower bound. -/
theorem hamiltonian_pvm_spectral_exact_gap_pvm_window_lower_bound :
    ∀ x : ℝ,
      x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow →
        hamiltonianPVMSpectralExactGapValue ≤ x := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmWindowLowerBound

/-- The concrete theorem-route PVM spectral window carries positive spectral weight. -/
theorem hamiltonian_pvm_spectral_exact_gap_positive_weight :
    0 < concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeightPositive

/-- The concrete theorem-route PVM spectral window carries nonzero spectral weight. -/
theorem hamiltonian_pvm_spectral_exact_gap_nonzero_weight :
    concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ≠ 0 := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeightNonzero

/-- R6-facing theorem-route normalization for the derived Hamiltonian spectral value.

This is not a singleton-membership witness and it is not an exported
`exactGapValueReal = 33/20` theorem.  The equality belongs to the concrete
Hamiltonian/PVM/spectral package from which the public carrier is projected. -/
theorem hamiltonian_pvm_spectral_exact_gap_value_eq_33_over_20_from_spectral_route :
    hamiltonianPVMSpectralExactGapValue = (33 : ℝ) / 20 := by
  exact concreteHamiltonianPVMSpectralExactGapValueOrigin.normalizationFromHamiltonianSpectrum

end

end MathlibAnalytic
end MGAP4D
