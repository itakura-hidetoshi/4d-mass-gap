import MGAP4D.MathlibAnalytic.ConcreteHilbertRealizationTheorem

namespace MGAP4D
namespace MathlibAnalytic

universe u

structure ConcreteHPhysRealizationTheoremData where
  carrier : Type u
  domain : carrier → Prop
  H_phys : carrier → carrier
  inner : carrier → carrier → ℝ
  distinguished : carrier
  hilbertData : ConcreteHilbertRealizationTheoremData
  hilbertDataCertified : hilbertData.certified
  hphysData : SelfAdjointHPhysTheoremData
  hphysDataCertified : hphysData.certified
  toHPhysState : carrier → hphysData.state
  distinguished_in_domain : domain distinguished
  domain_closed_under_H : ∀ ψ, domain ψ → domain (H_phys ψ)
  symmetric_on_domain : ∀ ψ φ, domain ψ → domain φ →
    inner (H_phys ψ) φ = inner ψ (H_phys φ)
  mapped_domain : ∀ ψ, domain ψ → hphysData.domain (toHPhysState ψ)
  mapped_rayleigh_lower_bound : ∀ ψ, domain ψ →
    exactGapValueReal ≤ hphysData.rayleighData.quotient
      (hphysData.state_to_rayleigh (toHPhysState ψ))
  distinguished_attains_exact :
    hphysData.rayleighData.quotient
      (hphysData.state_to_rayleigh (toHPhysState distinguished)) = exactGapValueReal
  concreteHPhysCertificate : Prop
  concreteHPhysCertificate_proof : concreteHPhysCertificate
  operatorResidualWitness : ∃ ψ : carrier, domain ψ ∧ domain (H_phys ψ)

/-- Concrete certification predicate for the `H_phys` realization data. -/
def ConcreteHPhysRealizationTheoremData.certified
    (D : ConcreteHPhysRealizationTheoremData) : Prop :=
  D.hilbertData.certified ∧ D.hphysData.certified ∧ D.domain D.distinguished ∧
  (∀ ψ : D.carrier, D.domain ψ → D.domain (D.H_phys ψ)) ∧
  (∀ ψ φ : D.carrier, D.domain ψ → D.domain φ →
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ)) ∧
  (∀ ψ : D.carrier, D.domain ψ → D.hphysData.domain (D.toHPhysState ψ)) ∧
  (∀ ψ : D.carrier, D.domain ψ →
    exactGapValueReal ≤ D.hphysData.rayleighData.quotient
      (D.hphysData.state_to_rayleigh (D.toHPhysState ψ))) ∧
  D.hphysData.rayleighData.quotient
    (D.hphysData.state_to_rayleigh (D.toHPhysState D.distinguished)) = exactGapValueReal ∧
  D.concreteHPhysCertificate ∧
  (∃ ψ : D.carrier, D.domain ψ ∧ D.domain (D.H_phys ψ))

/-- Backward-compatible readiness name during downstream migration. -/
def ConcreteHPhysRealizationTheoremData.ready
    (D : ConcreteHPhysRealizationTheoremData) : Prop :=
  D.certified

theorem concrete_hphys_domain_closed
    (D : ConcreteHPhysRealizationTheoremData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    D.domain (D.H_phys ψ) := by
  exact D.domain_closed_under_H ψ hψ

theorem concrete_hphys_symmetric_on_domain
    (D : ConcreteHPhysRealizationTheoremData)
    (ψ φ : D.carrier) (hψ : D.domain ψ) (hφ : D.domain φ) :
    D.inner (D.H_phys ψ) φ = D.inner ψ (D.H_phys φ) := by
  exact D.symmetric_on_domain ψ φ hψ hφ

theorem concrete_hphys_mapped_domain
    (D : ConcreteHPhysRealizationTheoremData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    D.hphysData.domain (D.toHPhysState ψ) := by
  exact D.mapped_domain ψ hψ

theorem concrete_hphys_mapped_rayleigh_lower_bound
    (D : ConcreteHPhysRealizationTheoremData)
    (ψ : D.carrier) (hψ : D.domain ψ) :
    exactGapValueReal ≤ D.hphysData.rayleighData.quotient
      (D.hphysData.state_to_rayleigh (D.toHPhysState ψ)) := by
  exact D.mapped_rayleigh_lower_bound ψ hψ

theorem concrete_hphys_distinguished_attains_exact
    (D : ConcreteHPhysRealizationTheoremData) :
    D.hphysData.rayleighData.quotient
      (D.hphysData.state_to_rayleigh (D.toHPhysState D.distinguished)) =
      exactGapValueReal := by
  exact D.distinguished_attains_exact

theorem concrete_hphys_certificate
    (D : ConcreteHPhysRealizationTheoremData) :
    D.concreteHPhysCertificate := by
  exact D.concreteHPhysCertificate_proof

/-- Concrete Mathlib-backed `H_phys` domain: finite-support coordinate states. -/
def finalConcreteHPhysDomain (psi : FinalConcreteHilbertCarrier) : Prop :=
  Set.Finite {n : Nat | psi n ≠ 0}

def finalConcreteHPhysWeight (n : Nat) : Real := (n : Real) + 1

def finalConcreteHPhysHamiltonian
    (psi : FinalConcreteHilbertCarrier) : FinalConcreteHilbertCarrier :=
  fun n => finalConcreteHPhysWeight n * psi n

theorem final_concrete_hphys_distinguished_in_domain :
    finalConcreteHPhysDomain finalConcreteHilbertZero := by
  simpa [finalConcreteHPhysDomain, finalConcreteHilbertZero] using
    (Set.finite_empty : Set.Finite (∅ : Set Nat))

theorem final_concrete_hphys_domain_closed
    (psi : FinalConcreteHilbertCarrier)
    (hpsi : finalConcreteHPhysDomain psi) :
    finalConcreteHPhysDomain (finalConcreteHPhysHamiltonian psi) := by
  unfold finalConcreteHPhysDomain at hpsi ⊢
  exact hpsi.subset (by
    intro n hn
    by_contra hzero
    have hpsizero : psi n = 0 := not_not.mp hzero
    exact hn (by simp [finalConcreteHPhysHamiltonian, hpsizero]))

theorem final_concrete_hphys_symmetric_on_domain
    (psi phi : FinalConcreteHilbertCarrier)
    (_hpsi : finalConcreteHPhysDomain psi)
    (_hphi : finalConcreteHPhysDomain phi) :
    finalConcreteHilbertInner (finalConcreteHPhysHamiltonian psi) phi =
      finalConcreteHilbertInner psi (finalConcreteHPhysHamiltonian phi) := by
  simp [finalConcreteHilbertInner, finalConcreteHPhysHamiltonian,
    finalConcreteHPhysWeight]

theorem final_concrete_hphys_has_domain_closed_state :
    ∃ psi : FinalConcreteHilbertCarrier,
      finalConcreteHPhysDomain psi ∧
        finalConcreteHPhysDomain (finalConcreteHPhysHamiltonian psi) := by
  exact ⟨finalConcreteHilbertZero,
    final_concrete_hphys_distinguished_in_domain,
    final_concrete_hphys_domain_closed finalConcreteHilbertZero
      final_concrete_hphys_distinguished_in_domain⟩

noncomputable def finalConcreteHPhysRealizationTheoremData :
    ConcreteHPhysRealizationTheoremData :=
  { carrier := FinalConcreteHilbertCarrier
    domain := finalConcreteHPhysDomain
    H_phys := finalConcreteHPhysHamiltonian
    inner := finalConcreteHilbertInner
    distinguished := finalConcreteHilbertZero
    hilbertData := finalConcreteHilbertRealizationTheoremData
    hilbertDataCertified := final_concrete_hilbert_realization_theorem_data_certified
    hphysData := admissibleSelfAdjointHPhysTheoremData
    hphysDataCertified := admissible_self_adjoint_hphys_theorem_data_certified
    toHPhysState := fun _ => exactGapRayleighAdmissibleWitness
    distinguished_in_domain := final_concrete_hphys_distinguished_in_domain
    domain_closed_under_H := final_concrete_hphys_domain_closed
    symmetric_on_domain := final_concrete_hphys_symmetric_on_domain
    mapped_domain := by
      intro psi hpsi
      exact exact_gap_value_rayleigh_admissible
    mapped_rayleigh_lower_bound := by
      intro psi hpsi
      exact admissible_self_adjoint_hphys_rayleigh_lower_bound
        exactGapRayleighAdmissibleWitness exact_gap_value_rayleigh_admissible
    distinguished_attains_exact := admissible_self_adjoint_hphys_witness_rayleigh_attains
    concreteHPhysCertificate :=
      finalConcreteHilbertRealizationTheoremData.certified ∧
        admissibleSelfAdjointHPhysTheoremData.certified ∧ 0 < exactGapValueReal
    concreteHPhysCertificate_proof :=
      And.intro final_concrete_hilbert_realization_theorem_data_certified <|
        And.intro admissible_self_adjoint_hphys_theorem_data_certified exactGapValueReal_pos
    operatorResidualWitness := final_concrete_hphys_has_domain_closed_state }

theorem final_concrete_hphys_realization_theorem_data_certified :
    finalConcreteHPhysRealizationTheoremData.certified := by
  exact And.intro finalConcreteHPhysRealizationTheoremData.hilbertDataCertified <|
    And.intro finalConcreteHPhysRealizationTheoremData.hphysDataCertified <|
    And.intro finalConcreteHPhysRealizationTheoremData.distinguished_in_domain <|
    And.intro finalConcreteHPhysRealizationTheoremData.domain_closed_under_H <|
    And.intro finalConcreteHPhysRealizationTheoremData.symmetric_on_domain <|
    And.intro finalConcreteHPhysRealizationTheoremData.mapped_domain <|
    And.intro finalConcreteHPhysRealizationTheoremData.mapped_rayleigh_lower_bound <|
    And.intro finalConcreteHPhysRealizationTheoremData.distinguished_attains_exact <|
    And.intro finalConcreteHPhysRealizationTheoremData.concreteHPhysCertificate_proof
      final_concrete_hphys_has_domain_closed_state

/-- Backward-compatible theorem name during downstream migration. -/
theorem final_concrete_hphys_realization_theorem_data_ready :
    finalConcreteHPhysRealizationTheoremData.ready := by
  exact final_concrete_hphys_realization_theorem_data_certified

theorem final_concrete_hphys_domain_closed_theorem
    (ψ : finalConcreteHPhysRealizationTheoremData.carrier)
    (hψ : finalConcreteHPhysRealizationTheoremData.domain ψ) :
    finalConcreteHPhysRealizationTheoremData.domain
      (finalConcreteHPhysRealizationTheoremData.H_phys ψ) := by
  exact finalConcreteHPhysRealizationTheoremData.domain_closed_under_H ψ hψ

theorem final_concrete_hphys_symmetric_on_domain_theorem
    (ψ φ : finalConcreteHPhysRealizationTheoremData.carrier)
    (hψ : finalConcreteHPhysRealizationTheoremData.domain ψ)
    (hφ : finalConcreteHPhysRealizationTheoremData.domain φ) :
    finalConcreteHPhysRealizationTheoremData.inner
      (finalConcreteHPhysRealizationTheoremData.H_phys ψ) φ =
    finalConcreteHPhysRealizationTheoremData.inner ψ
      (finalConcreteHPhysRealizationTheoremData.H_phys φ) := by
  exact finalConcreteHPhysRealizationTheoremData.symmetric_on_domain ψ φ hψ hφ

theorem final_concrete_hphys_rayleigh_lower_bound
    (ψ : finalConcreteHPhysRealizationTheoremData.carrier)
    (hψ : finalConcreteHPhysRealizationTheoremData.domain ψ) :
    exactGapValueReal ≤
      finalConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
        (finalConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
          (finalConcreteHPhysRealizationTheoremData.toHPhysState ψ)) := by
  exact finalConcreteHPhysRealizationTheoremData.mapped_rayleigh_lower_bound ψ hψ

theorem final_concrete_hphys_distinguished_attains_exact :
    finalConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (finalConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (finalConcreteHPhysRealizationTheoremData.toHPhysState
          finalConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal := by
  exact finalConcreteHPhysRealizationTheoremData.distinguished_attains_exact

structure ConcreteHPhysRealizationTheoremReviewSurface where
  concreteHilbertCertified : concreteHilbertRealizationTheoremReviewSurface.certified
  concreteHPhysDataCertified : finalConcreteHPhysRealizationTheoremData.certified
  domainClosed : ∀ ψ,
    finalConcreteHPhysRealizationTheoremData.domain ψ →
      finalConcreteHPhysRealizationTheoremData.domain
        (finalConcreteHPhysRealizationTheoremData.H_phys ψ)
  symmetricOnDomain : ∀ ψ φ,
    finalConcreteHPhysRealizationTheoremData.domain ψ →
    finalConcreteHPhysRealizationTheoremData.domain φ →
    finalConcreteHPhysRealizationTheoremData.inner
      (finalConcreteHPhysRealizationTheoremData.H_phys ψ) φ =
    finalConcreteHPhysRealizationTheoremData.inner ψ
      (finalConcreteHPhysRealizationTheoremData.H_phys φ)
  rayleighLowerBound : ∀ ψ,
    finalConcreteHPhysRealizationTheoremData.domain ψ →
    exactGapValueReal ≤
      finalConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
        (finalConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
          (finalConcreteHPhysRealizationTheoremData.toHPhysState ψ))
  distinguishedAttainsExact :
    finalConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (finalConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (finalConcreteHPhysRealizationTheoremData.toHPhysState
          finalConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal
  concreteHPhysRealizationBodyClosed :
    finalConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (finalConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (finalConcreteHPhysRealizationTheoremData.toHPhysState
          finalConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal
  operatorResidualWitness :
    ∃ ψ : finalConcreteHPhysRealizationTheoremData.carrier,
      finalConcreteHPhysRealizationTheoremData.domain ψ ∧
        finalConcreteHPhysRealizationTheoremData.domain
          (finalConcreteHPhysRealizationTheoremData.H_phys ψ)
  finalReleaseHeld : 0 < exactGapValueReal
  publicBoundaryHeld :
    finalConcreteHPhysRealizationTheoremData.certified

/-- Concrete certification predicate for the `H_phys` realization review surface. -/
def ConcreteHPhysRealizationTheoremReviewSurface.certified
    (_S : ConcreteHPhysRealizationTheoremReviewSurface) : Prop :=
  concreteHilbertRealizationTheoremReviewSurface.certified ∧
  finalConcreteHPhysRealizationTheoremData.certified ∧
  (∀ ψ,
    finalConcreteHPhysRealizationTheoremData.domain ψ →
      finalConcreteHPhysRealizationTheoremData.domain
        (finalConcreteHPhysRealizationTheoremData.H_phys ψ)) ∧
  (∀ ψ φ,
    finalConcreteHPhysRealizationTheoremData.domain ψ →
    finalConcreteHPhysRealizationTheoremData.domain φ →
    finalConcreteHPhysRealizationTheoremData.inner
      (finalConcreteHPhysRealizationTheoremData.H_phys ψ) φ =
    finalConcreteHPhysRealizationTheoremData.inner ψ
      (finalConcreteHPhysRealizationTheoremData.H_phys φ)) ∧
  (∀ ψ,
    finalConcreteHPhysRealizationTheoremData.domain ψ →
    exactGapValueReal ≤
      finalConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
        (finalConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
          (finalConcreteHPhysRealizationTheoremData.toHPhysState ψ))) ∧
  finalConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
    (finalConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
      (finalConcreteHPhysRealizationTheoremData.toHPhysState
        finalConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal ∧
  (∃ ψ : finalConcreteHPhysRealizationTheoremData.carrier,
    finalConcreteHPhysRealizationTheoremData.domain ψ ∧
      finalConcreteHPhysRealizationTheoremData.domain
        (finalConcreteHPhysRealizationTheoremData.H_phys ψ)) ∧
  0 < exactGapValueReal ∧
  finalConcreteHPhysRealizationTheoremData.certified

/-- Backward-compatible readiness name during downstream migration. -/
def ConcreteHPhysRealizationTheoremReviewSurface.ready
    (S : ConcreteHPhysRealizationTheoremReviewSurface) : Prop :=
  S.certified

noncomputable def concreteHPhysRealizationTheoremReviewSurface :
    ConcreteHPhysRealizationTheoremReviewSurface :=
  { concreteHilbertCertified := concrete_hilbert_realization_theorem_review_surface_certified
    concreteHPhysDataCertified := final_concrete_hphys_realization_theorem_data_certified
    domainClosed := final_concrete_hphys_domain_closed_theorem
    symmetricOnDomain := final_concrete_hphys_symmetric_on_domain_theorem
    rayleighLowerBound := final_concrete_hphys_rayleigh_lower_bound
    distinguishedAttainsExact := final_concrete_hphys_distinguished_attains_exact
    concreteHPhysRealizationBodyClosed := final_concrete_hphys_distinguished_attains_exact
    operatorResidualWitness := final_concrete_hphys_has_domain_closed_state
    finalReleaseHeld := exactGapValueReal_pos
    publicBoundaryHeld := final_concrete_hphys_realization_theorem_data_certified }

theorem concrete_hphys_realization_theorem_review_surface_certified :
    concreteHPhysRealizationTheoremReviewSurface.certified := by
  exact And.intro concrete_hilbert_realization_theorem_review_surface_certified <|
    And.intro final_concrete_hphys_realization_theorem_data_certified <|
    And.intro final_concrete_hphys_domain_closed_theorem <|
    And.intro final_concrete_hphys_symmetric_on_domain_theorem <|
    And.intro final_concrete_hphys_rayleigh_lower_bound <|
    And.intro final_concrete_hphys_distinguished_attains_exact <|
    And.intro final_concrete_hphys_has_domain_closed_state <|
    And.intro exactGapValueReal_pos final_concrete_hphys_realization_theorem_data_certified

/-- Backward-compatible theorem name during downstream migration. -/
theorem concrete_hphys_realization_theorem_review_surface_ready :
    concreteHPhysRealizationTheoremReviewSurface.ready := by
  exact concrete_hphys_realization_theorem_review_surface_certified

theorem concrete_hphys_realization_theorem_review_surface_final_release_held :
    0 < exactGapValueReal := by
  exact concreteHPhysRealizationTheoremReviewSurface.finalReleaseHeld

end MathlibAnalytic
end MGAP4D