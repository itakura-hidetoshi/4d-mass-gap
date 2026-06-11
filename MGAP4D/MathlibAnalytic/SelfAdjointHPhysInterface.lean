import MGAP4D.MathlibAnalytic.HilbertRayleighInterface

namespace MGAP4D
namespace MathlibAnalytic

/-- Abstract operator interface for the next `H_phys` layer.

This is not yet the full unbounded self-adjoint-operator theorem.  It records
an operator-facing interface compatible with the Hilbert/Rayleigh surface:
there is a carrier, an inner pairing, an operator `H_phys`, a symmetry witness,
a Rayleigh interface, and compatibility between the operator energy and the
Rayleigh-energy map.  It deliberately carries no upstream `33/20` theorem. -/
structure SelfAdjointHPhysInterface where
  state : Type
  inner : state → state → ℝ
  H_phys : state → state
  rayleigh : HilbertRayleighInterface
  state_to_rayleigh : state → rayleigh.state
  witness : state
  symmetric : ∀ ψ φ, inner (H_phys ψ) φ = inner ψ (H_phys φ)
  witness_rayleigh_admissible : rayleigh.admissible (state_to_rayleigh witness)
  witness_energy_eq_exact :
    rayleigh.rayleighEnergy (state_to_rayleigh witness) = exactGapValueReal
  lower_bound : ∀ ψ, rayleigh.admissible (state_to_rayleigh ψ) →
    exactGapValueReal ≤ rayleigh.rayleighEnergy (state_to_rayleigh ψ)
  exact_value_positive : 0 < exactGapValueReal
  exact_value_in_energyRay : exactGapValueReal ∈ exactGapEnergyRay

/-- Ready predicate for the operator-facing `H_phys` interface. -/
def SelfAdjointHPhysInterface.ready (I : SelfAdjointHPhysInterface) : Prop :=
  (∀ ψ φ, I.inner (I.H_phys ψ) φ = I.inner ψ (I.H_phys φ)) ∧
  I.rayleigh.admissible (I.state_to_rayleigh I.witness) ∧
  I.rayleigh.rayleighEnergy (I.state_to_rayleigh I.witness) = exactGapValueReal ∧
  (∀ ψ, I.rayleigh.admissible (I.state_to_rayleigh ψ) →
    exactGapValueReal ≤ I.rayleigh.rayleighEnergy (I.state_to_rayleigh ψ)) ∧
  0 < exactGapValueReal ∧
  exactGapValueReal ∈ exactGapEnergyRay

/-- Singleton operator prototype.  This is a compilation-safe bridge from the
Rayleigh interface to an operator-shaped surface, while keeping the true
self-adjoint theorem open. -/
noncomputable def singletonSelfAdjointHPhysInterface : SelfAdjointHPhysInterface :=
  { state := PUnit
    inner := fun _ _ => 1
    H_phys := fun ψ => ψ
    rayleigh := singletonHilbertRayleighInterface
    state_to_rayleigh := fun _ => PUnit.unit
    witness := PUnit.unit
    symmetric := by
      intro _ _
      rfl
    witness_rayleigh_admissible := exactGapValueReal_mem_energyRay
    witness_energy_eq_exact := rfl
    lower_bound := by
      intro _ _
      exact le_rfl
    exact_value_positive := exactGapValueReal_pos
    exact_value_in_energyRay := exactGapValueReal_mem_energyRay }

theorem singleton_self_adjoint_hphys_interface_ready :
    singletonSelfAdjointHPhysInterface.ready := by
  exact And.intro (by intro _ _; rfl) <|
    And.intro exactGapValueReal_mem_energyRay <|
    And.intro rfl <|
    And.intro (by intro _ _; exact le_rfl) <|
    And.intro exactGapValueReal_pos exactGapValueReal_mem_energyRay

theorem singleton_self_adjoint_hphys_interface_symmetric :
    ∀ ψ φ, singletonSelfAdjointHPhysInterface.inner
        (singletonSelfAdjointHPhysInterface.H_phys ψ) φ =
      singletonSelfAdjointHPhysInterface.inner ψ
        (singletonSelfAdjointHPhysInterface.H_phys φ) := by
  intro _ _
  rfl

theorem singleton_self_adjoint_hphys_interface_witness_admissible :
    singletonSelfAdjointHPhysInterface.rayleigh.admissible
      (singletonSelfAdjointHPhysInterface.state_to_rayleigh
        singletonSelfAdjointHPhysInterface.witness) := by
  exact exactGapValueReal_mem_energyRay

theorem singleton_self_adjoint_hphys_interface_witness_attains :
    singletonSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
      (singletonSelfAdjointHPhysInterface.state_to_rayleigh
        singletonSelfAdjointHPhysInterface.witness) = exactGapValueReal := by
  rfl

theorem singleton_self_adjoint_hphys_interface_lower_bound
    (ψ : singletonSelfAdjointHPhysInterface.state)
    (_hψ : singletonSelfAdjointHPhysInterface.rayleigh.admissible
      (singletonSelfAdjointHPhysInterface.state_to_rayleigh ψ)) :
    exactGapValueReal ≤
      singletonSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
        (singletonSelfAdjointHPhysInterface.state_to_rayleigh ψ) := by
  exact le_rfl

/-- Review surface linking the Hilbert/Rayleigh interface to the operator-shaped
`H_phys` interface. -/
structure SelfAdjointHPhysReviewSurface where
  hilbertRayleighReady : hilbertRayleighInterfaceReviewSurface.ready
  hphysInterfaceReady : singletonSelfAdjointHPhysInterface.ready
  symmetryReady : ∀ ψ φ, singletonSelfAdjointHPhysInterface.inner
      (singletonSelfAdjointHPhysInterface.H_phys ψ) φ =
    singletonSelfAdjointHPhysInterface.inner ψ
      (singletonSelfAdjointHPhysInterface.H_phys φ)
  witnessAdmissible : singletonSelfAdjointHPhysInterface.rayleigh.admissible
    (singletonSelfAdjointHPhysInterface.state_to_rayleigh
      singletonSelfAdjointHPhysInterface.witness)
  witnessAttains : singletonSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
    (singletonSelfAdjointHPhysInterface.state_to_rayleigh
      singletonSelfAdjointHPhysInterface.witness) = exactGapValueReal
  lowerBoundCompatible : ∀ ψ,
    singletonSelfAdjointHPhysInterface.rayleigh.admissible
      (singletonSelfAdjointHPhysInterface.state_to_rayleigh ψ) →
    exactGapValueReal ≤
      singletonSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
        (singletonSelfAdjointHPhysInterface.state_to_rayleigh ψ)
  exactValue_in_energyRay : exactGapValueReal ∈ exactGapEnergyRay
  exactValue_in_positive_ray : exactGapValueReal ∈ Set.Ioi (0 : ℝ)

def SelfAdjointHPhysReviewSurface.ready
    (_S : SelfAdjointHPhysReviewSurface) : Prop :=
  hilbertRayleighInterfaceReviewSurface.ready ∧
  singletonSelfAdjointHPhysInterface.ready ∧
  (∀ ψ φ, singletonSelfAdjointHPhysInterface.inner
      (singletonSelfAdjointHPhysInterface.H_phys ψ) φ =
    singletonSelfAdjointHPhysInterface.inner ψ
      (singletonSelfAdjointHPhysInterface.H_phys φ)) ∧
  singletonSelfAdjointHPhysInterface.rayleigh.admissible
    (singletonSelfAdjointHPhysInterface.state_to_rayleigh
      singletonSelfAdjointHPhysInterface.witness) ∧
  singletonSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
    (singletonSelfAdjointHPhysInterface.state_to_rayleigh
      singletonSelfAdjointHPhysInterface.witness) = exactGapValueReal ∧
  (∀ ψ, singletonSelfAdjointHPhysInterface.rayleigh.admissible
      (singletonSelfAdjointHPhysInterface.state_to_rayleigh ψ) →
    exactGapValueReal ≤
      singletonSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
        (singletonSelfAdjointHPhysInterface.state_to_rayleigh ψ)) ∧
  exactGapValueReal ∈ exactGapEnergyRay ∧ exactGapValueReal ∈ Set.Ioi (0 : ℝ)

noncomputable def selfAdjointHPhysReviewSurface : SelfAdjointHPhysReviewSurface :=
  { hilbertRayleighReady := hilbert_rayleigh_interface_review_surface_ready
    hphysInterfaceReady := singleton_self_adjoint_hphys_interface_ready
    symmetryReady := singleton_self_adjoint_hphys_interface_symmetric
    witnessAdmissible := singleton_self_adjoint_hphys_interface_witness_admissible
    witnessAttains := singleton_self_adjoint_hphys_interface_witness_attains
    lowerBoundCompatible := singleton_self_adjoint_hphys_interface_lower_bound
    exactValue_in_energyRay := exactGapValueReal_mem_energyRay
    exactValue_in_positive_ray := exactGapValueReal_mem_positive_ray }

theorem self_adjoint_hphys_review_surface_ready :
    selfAdjointHPhysReviewSurface.ready := by
  exact And.intro hilbert_rayleigh_interface_review_surface_ready <|
    And.intro singleton_self_adjoint_hphys_interface_ready <|
    And.intro singleton_self_adjoint_hphys_interface_symmetric <|
    And.intro singleton_self_adjoint_hphys_interface_witness_admissible <|
    And.intro singleton_self_adjoint_hphys_interface_witness_attains <|
    And.intro singleton_self_adjoint_hphys_interface_lower_bound <|
    And.intro exactGapValueReal_mem_energyRay exactGapValueReal_mem_positive_ray

theorem self_adjoint_hphys_review_surface_exact_value_in_energyRay :
    exactGapValueReal ∈ exactGapEnergyRay := by
  exact exactGapValueReal_mem_energyRay

end MathlibAnalytic
end MGAP4D
