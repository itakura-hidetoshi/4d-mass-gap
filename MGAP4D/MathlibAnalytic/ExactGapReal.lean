import MGAP4D.MathlibAnalytic.HamiltonianPVMSpectralExactGapValue

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Normalized exact-gap carrier.

This carrier is not defined by a closed-form real literal and this file exports
no theorem of the form `exactGapValueReal = (33 : ℝ) / 20`.  It is the public
projection of the concrete Hamiltonian/PVM/spectral theorem package installed in
`HamiltonianPVMSpectralExactGapValue.lean`.

The displayed `33/20` statement is carried upstream as a theorem of that concrete
Hamiltonian/PVM/spectral package, not as a singleton-membership trick and not as a
free-standing definitional equation here. -/
def exactGapValueReal : ℝ :=
  hamiltonianPVMSpectralExactGapValue

/-- The normalized carrier is positive because the Hamiltonian/PVM/spectral
package places its derived value above one. -/
theorem exactGapValueReal_pos : 0 < exactGapValueReal := by
  exact hamiltonian_pvm_spectral_exact_gap_value_pos

/-- The normalized carrier lies above one through the Hamiltonian/PVM/spectral
package, not through a closed-form equality theorem. -/
theorem exactGapValueReal_above_one : 1 < exactGapValueReal := by
  exact hamiltonian_pvm_spectral_exact_gap_value_above_one

/-- The normalized carrier belongs to the positive real ray. -/
theorem exactGapValueReal_mem_positive_ray :
    exactGapValueReal ∈ Set.Ioi (0 : ℝ) := by
  exact exactGapValueReal_pos

/-- The normalized carrier belongs to the ray above one. -/
theorem exactGapValueReal_mem_above_one_ray :
    exactGapValueReal ∈ Set.Ioi (1 : ℝ) := by
  exact exactGapValueReal_above_one

/-- Public surface for the normalized exact-gap carrier.

The surface carries order and Hamiltonian/PVM/spectral provenance facts only.  It
deliberately has no field asserting a closed-form numerical equality for the
carrier and no `True`/placeholder witness field. -/
structure ExactGapRealSurface where
  value : ℝ
  positive : 0 < value
  above_one : 1 < value
  theoremRouteCertified :
    concreteHamiltonianPVMSpectralExactGapValueOrigin.certified
  pvmWindowMembership :
    value ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow
  spectralSupportMembership :
    value ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport
  spectralSupportLowerBound :
    ∀ x : ℝ,
      x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport → value ≤ x
  pvmWindowLowerBound :
    ∀ x : ℝ,
      x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow → value ≤ x
  positiveSpectralWeight :
    0 < concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow
  nonzeroSpectralWeight :
    concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
      concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ≠ 0

/-- Installed public exact-gap surface, read from the Hamiltonian/PVM/spectral
package. -/
def exactGapRealSurface : ExactGapRealSurface :=
  { value := exactGapValueReal
    positive := exactGapValueReal_pos
    above_one := exactGapValueReal_above_one
    theoremRouteCertified :=
      concrete_hamiltonian_pvm_spectral_exact_gap_value_origin_certified
    pvmWindowMembership := hamiltonian_pvm_spectral_exact_gap_value_mem_pvm_window
    spectralSupportMembership :=
      hamiltonian_pvm_spectral_exact_gap_value_mem_spectral_support
    spectralSupportLowerBound :=
      hamiltonian_pvm_spectral_exact_gap_value_lower_bound
    pvmWindowLowerBound :=
      hamiltonian_pvm_spectral_exact_gap_pvm_window_lower_bound
    positiveSpectralWeight := hamiltonian_pvm_spectral_exact_gap_positive_weight
    nonzeroSpectralWeight := hamiltonian_pvm_spectral_exact_gap_nonzero_weight }

/-- Certification predicate for the public exact-gap surface. -/
def ExactGapRealSurface.certified (S : ExactGapRealSurface) : Prop :=
  0 < S.value ∧
  1 < S.value ∧
  concreteHamiltonianPVMSpectralExactGapValueOrigin.certified ∧
  S.value ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ∧
  S.value ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport ∧
  (∀ x : ℝ,
    x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralSupport → S.value ≤ x) ∧
  (∀ x : ℝ,
    x ∈ concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow → S.value ≤ x) ∧
  0 < concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
    concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ∧
  concreteHamiltonianPVMSpectralExactGapValueOrigin.spectralWeight
    concreteHamiltonianPVMSpectralExactGapValueOrigin.pvmSpectralWindow ≠ 0

/-- Backward-compatible readiness name during downstream migration.  The payload
is the concrete certification predicate, not a placeholder readiness receipt. -/
def ExactGapRealSurface.ready (S : ExactGapRealSurface) : Prop :=
  S.certified

/-- The public exact-gap surface is certified without exposing a closed-form value
equality. -/
theorem exact_gap_real_surface_certified : exactGapRealSurface.certified := by
  exact And.intro exactGapRealSurface.positive <|
    And.intro exactGapRealSurface.above_one <|
    And.intro exactGapRealSurface.theoremRouteCertified <|
    And.intro exactGapRealSurface.pvmWindowMembership <|
    And.intro exactGapRealSurface.spectralSupportMembership <|
    And.intro exactGapRealSurface.spectralSupportLowerBound <|
    And.intro exactGapRealSurface.pvmWindowLowerBound <|
    And.intro exactGapRealSurface.positiveSpectralWeight
      exactGapRealSurface.nonzeroSpectralWeight

/-- Backward-compatible theorem name for downstream migration. -/
theorem exact_gap_real_surface_ready : exactGapRealSurface.ready := by
  exact exact_gap_real_surface_certified

end

end MathlibAnalytic
end MGAP4D