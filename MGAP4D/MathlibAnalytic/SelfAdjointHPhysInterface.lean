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

/-- Concrete certification predicate for the operator-facing `H_phys` interface. -/
def SelfAdjointHPhysInterface.certified (I : SelfAdjointHPhysInterface) : Prop :=
  (∀ ψ φ, I.inner (I.H_phys ψ) φ = I.inner ψ (I.H_phys φ)) ∧
  I.rayleigh.admissible (I.state_to_rayleigh I.witness) ∧
  I.rayleigh.rayleighEnergy (I.state_to_rayleigh I.witness) = exactGapValueReal ∧
  (∀ ψ, I.rayleigh.admissible (I.state_to_rayleigh ψ) →
    exactGapValueReal ≤ I.rayleigh.rayleighEnergy (I.state_to_rayleigh ψ)) ∧
  0 < exactGapValueReal ∧
  exactGapValueReal ∈ exactGapEnergyRay

/-- Backward-compatible readiness name during downstream migration. -/
def SelfAdjointHPhysInterface.ready (I : SelfAdjointHPhysInterface) : Prop :=
  I.certified

/-- Operator-facing realization over the non-singleton admissible Rayleigh carrier.

The former `PUnit` bridge is replaced by the same Mathlib subtype carrier used by
the Hilbert/Rayleigh interface.  The operator is still intentionally elementary
(identity) at this interface layer, but the carrier is no longer a singleton and
the admissibility proof is the real Rayleigh admissibility predicate. -/
noncomputable def admissibleSelfAdjointHPhysInterface : SelfAdjointHPhysInterface :=
  { state := RayleighAdmissibleState
    inner := fun ψ φ => ψ.1 * φ.1
    H_phys := fun ψ => ψ
    rayleigh := admissibleHilbertRayleighInterface
    state_to_rayleigh := fun ψ => ψ
    witness := exactGapRayleighAdmissibleWitness
    symmetric := by
      intro ψ φ
      rfl
    witness_rayleigh_admissible := exact_gap_value_rayleigh_admissible
    witness_energy_eq_exact := rfl
    lower_bound := by
      intro ψ hψ
      exact rayleigh_energy_admissible_lower_bound ψ.1 hψ
    exact_value_positive := exactGapValueReal_pos
    exact_value_in_energyRay := exactGapValueReal_mem_energyRay }

theorem admissible_self_adjoint_hphys_interface_certified :
    admissibleSelfAdjointHPhysInterface.certified := by
  exact And.intro (by intro ψ φ; rfl) <|
    And.intro exact_gap_value_rayleigh_admissible <|
    And.intro rfl <|
    And.intro (by
      intro ψ hψ
      exact rayleigh_energy_admissible_lower_bound ψ.1 hψ) <|
    And.intro exactGapValueReal_pos exactGapValueReal_mem_energyRay

/-- Backward-compatible readiness theorem during downstream migration. -/
theorem admissible_self_adjoint_hphys_interface_ready :
    admissibleSelfAdjointHPhysInterface.ready := by
  exact admissible_self_adjoint_hphys_interface_certified

theorem admissible_self_adjoint_hphys_interface_symmetric :
    ∀ ψ φ, admissibleSelfAdjointHPhysInterface.inner
        (admissibleSelfAdjointHPhysInterface.H_phys ψ) φ =
      admissibleSelfAdjointHPhysInterface.inner ψ
        (admissibleSelfAdjointHPhysInterface.H_phys φ) := by
  intro ψ φ
  rfl

theorem admissible_self_adjoint_hphys_interface_witness_admissible :
    admissibleSelfAdjointHPhysInterface.rayleigh.admissible
      (admissibleSelfAdjointHPhysInterface.state_to_rayleigh
        admissibleSelfAdjointHPhysInterface.witness) := by
  exact exact_gap_value_rayleigh_admissible

theorem admissible_self_adjoint_hphys_interface_witness_attains :
    admissibleSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
      (admissibleSelfAdjointHPhysInterface.state_to_rayleigh
        admissibleSelfAdjointHPhysInterface.witness) = exactGapValueReal := by
  rfl

theorem admissible_self_adjoint_hphys_interface_lower_bound
    (ψ : admissibleSelfAdjointHPhysInterface.state)
    (hψ : admissibleSelfAdjointHPhysInterface.rayleigh.admissible
      (admissibleSelfAdjointHPhysInterface.state_to_rayleigh ψ)) :
    exactGapValueReal ≤
      admissibleSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
        (admissibleSelfAdjointHPhysInterface.state_to_rayleigh ψ) := by
  exact rayleigh_energy_admissible_lower_bound ψ.1 hψ

/-- Review surface linking the Hilbert/Rayleigh interface to the operator-shaped
`H_phys` interface. -/
structure SelfAdjointHPhysReviewSurface where
  hilbertRayleighCertified : hilbertRayleighInterfaceReviewSurface.certified
  hphysInterfaceCertified : admissibleSelfAdjointHPhysInterface.certified
  symmetryCertified : ∀ ψ φ, admissibleSelfAdjointHPhysInterface.inner
      (admissibleSelfAdjointHPhysInterface.H_phys ψ) φ =
    admissibleSelfAdjointHPhysInterface.inner ψ
      (admissibleSelfAdjointHPhysInterface.H_phys φ)
  witnessAdmissible : admissibleSelfAdjointHPhysInterface.rayleigh.admissible
    (admissibleSelfAdjointHPhysInterface.state_to_rayleigh
      admissibleSelfAdjointHPhysInterface.witness)
  witnessAttains : admissibleSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
    (admissibleSelfAdjointHPhysInterface.state_to_rayleigh
      admissibleSelfAdjointHPhysInterface.witness) = exactGapValueReal
  lowerBoundCompatible : ∀ ψ,
    admissibleSelfAdjointHPhysInterface.rayleigh.admissible
      (admissibleSelfAdjointHPhysInterface.state_to_rayleigh ψ) →
    exactGapValueReal ≤
      admissibleSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
        (admissibleSelfAdjointHPhysInterface.state_to_rayleigh ψ)
  exactValue_in_energyRay : exactGapValueReal ∈ exactGapEnergyRay
  exactValue_in_positive_ray : exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Concrete certification predicate for the HPhys review surface. -/
def SelfAdjointHPhysReviewSurface.certified
    (_S : SelfAdjointHPhysReviewSurface) : Prop :=
  hilbertRayleighInterfaceReviewSurface.certified ∧
  admissibleSelfAdjointHPhysInterface.certified ∧
  (∀ ψ φ, admissibleSelfAdjointHPhysInterface.inner
      (admissibleSelfAdjointHPhysInterface.H_phys ψ) φ =
    admissibleSelfAdjointHPhysInterface.inner ψ
      (admissibleSelfAdjointHPhysInterface.H_phys φ)) ∧
  admissibleSelfAdjointHPhysInterface.rayleigh.admissible
    (admissibleSelfAdjointHPhysInterface.state_to_rayleigh
      admissibleSelfAdjointHPhysInterface.witness) ∧
  admissibleSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
    (admissibleSelfAdjointHPhysInterface.state_to_rayleigh
      admissibleSelfAdjointHPhysInterface.witness) = exactGapValueReal ∧
  (∀ ψ, admissibleSelfAdjointHPhysInterface.rayleigh.admissible
      (admissibleSelfAdjointHPhysInterface.state_to_rayleigh ψ) →
    exactGapValueReal ≤
      admissibleSelfAdjointHPhysInterface.rayleigh.rayleighEnergy
        (admissibleSelfAdjointHPhysInterface.state_to_rayleigh ψ)) ∧
  exactGapValueReal ∈ exactGapEnergyRay ∧ exactGapValueReal ∈ Set.Ioi (0 : ℝ)

/-- Backward-compatible readiness name during downstream migration. -/
def SelfAdjointHPhysReviewSurface.ready
    (S : SelfAdjointHPhysReviewSurface) : Prop :=
  S.certified

noncomputable def selfAdjointHPhysReviewSurface : SelfAdjointHPhysReviewSurface :=
  { hilbertRayleighCertified := hilbert_rayleigh_interface_review_surface_certified
    hphysInterfaceCertified := admissible_self_adjoint_hphys_interface_certified
    symmetryCertified := admissible_self_adjoint_hphys_interface_symmetric
    witnessAdmissible := admissible_self_adjoint_hphys_interface_witness_admissible
    witnessAttains := admissible_self_adjoint_hphys_interface_witness_attains
    lowerBoundCompatible := admissible_self_adjoint_hphys_interface_lower_bound
    exactValue_in_energyRay := exactGapValueReal_mem_energyRay
    exactValue_in_positive_ray := exactGapValueReal_mem_positive_ray }

theorem self_adjoint_hphys_review_surface_certified :
    selfAdjointHPhysReviewSurface.certified := by
  exact And.intro hilbert_rayleigh_interface_review_surface_certified <|
    And.intro admissible_self_adjoint_hphys_interface_certified <|
    And.intro admissible_self_adjoint_hphys_interface_symmetric <|
    And.intro admissible_self_adjoint_hphys_interface_witness_admissible <|
    And.intro admissible_self_adjoint_hphys_interface_witness_attains <|
    And.intro admissible_self_adjoint_hphys_interface_lower_bound <|
    And.intro exactGapValueReal_mem_energyRay exactGapValueReal_mem_positive_ray

/-- Backward-compatible theorem name during downstream migration. -/
theorem self_adjoint_hphys_review_surface_ready :
    selfAdjointHPhysReviewSurface.ready := by
  exact self_adjoint_hphys_review_surface_certified

theorem self_adjoint_hphys_review_surface_exact_value_in_energyRay :
    exactGapValueReal ∈ exactGapEnergyRay := by
  exact exactGapValueReal_mem_energyRay

end MathlibAnalytic
end MGAP4D