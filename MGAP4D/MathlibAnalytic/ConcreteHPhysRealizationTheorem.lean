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
  hilbertDataReady : hilbertData.ready
  hphysData : SelfAdjointHPhysTheoremData
  hphysDataReady : hphysData.ready
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
  operatorResidualStillOpen : Prop

def ConcreteHPhysRealizationTheoremData.ready
    (D : ConcreteHPhysRealizationTheoremData) : Prop :=
  D.hilbertData.ready ∧ D.hphysData.ready ∧ D.domain D.distinguished ∧
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
  D.operatorResidualStillOpen

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
    hilbertData := singletonConcreteHilbertRealizationTheoremData
    hilbertDataReady := singleton_concrete_hilbert_realization_theorem_data_ready
    hphysData := singletonSelfAdjointHPhysTheoremData
    hphysDataReady := singleton_self_adjoint_hphys_theorem_data_ready
    toHPhysState := fun _ => singletonSelfAdjointHPhysTheoremData.witness
    distinguished_in_domain := final_concrete_hphys_distinguished_in_domain
    domain_closed_under_H := final_concrete_hphys_domain_closed
    symmetric_on_domain := final_concrete_hphys_symmetric_on_domain
    mapped_domain := by
      intro psi hpsi
      exact singletonSelfAdjointHPhysTheoremData.witness_in_domain
    mapped_rayleigh_lower_bound := by
      intro psi hpsi
      exact singleton_self_adjoint_hphys_rayleigh_lower_bound
        singletonSelfAdjointHPhysTheoremData.witness
        singletonSelfAdjointHPhysTheoremData.witness_in_domain
    distinguished_attains_exact := singleton_self_adjoint_hphys_witness_rayleigh_attains
    concreteHPhysCertificate :=
      singletonConcreteHilbertRealizationTheoremData.ready ∧
        singletonSelfAdjointHPhysTheoremData.ready ∧ 0 < exactGapValueReal
    concreteHPhysCertificate_proof :=
      And.intro singleton_concrete_hilbert_realization_theorem_data_ready <|
        And.intro singleton_self_adjoint_hphys_theorem_data_ready exactGapValueReal_pos
    operatorResidualStillOpen :=
      ∃ psi : FinalConcreteHilbertCarrier,
        finalConcreteHPhysDomain psi ∧
          finalConcreteHPhysDomain (finalConcreteHPhysHamiltonian psi) }

/-- Backwards-compatible name: the old singleton slot now aliases the final
countable-coordinate concrete `H_phys` realization. -/
noncomputable abbrev singletonConcreteHPhysRealizationTheoremData :
    ConcreteHPhysRealizationTheoremData :=
  finalConcreteHPhysRealizationTheoremData

theorem singleton_concrete_hphys_realization_theorem_data_ready :
    singletonConcreteHPhysRealizationTheoremData.ready := by
  exact And.intro singletonConcreteHPhysRealizationTheoremData.hilbertDataReady <|
    And.intro singletonConcreteHPhysRealizationTheoremData.hphysDataReady <|
    And.intro singletonConcreteHPhysRealizationTheoremData.distinguished_in_domain <|
    And.intro singletonConcreteHPhysRealizationTheoremData.domain_closed_under_H <|
    And.intro singletonConcreteHPhysRealizationTheoremData.symmetric_on_domain <|
    And.intro singletonConcreteHPhysRealizationTheoremData.mapped_domain <|
    And.intro singletonConcreteHPhysRealizationTheoremData.mapped_rayleigh_lower_bound <|
    And.intro singletonConcreteHPhysRealizationTheoremData.distinguished_attains_exact <|
    And.intro singletonConcreteHPhysRealizationTheoremData.concreteHPhysCertificate_proof
      final_concrete_hphys_has_domain_closed_state

theorem singleton_concrete_hphys_domain_closed
    (ψ : singletonConcreteHPhysRealizationTheoremData.carrier)
    (hψ : singletonConcreteHPhysRealizationTheoremData.domain ψ) :
    singletonConcreteHPhysRealizationTheoremData.domain
      (singletonConcreteHPhysRealizationTheoremData.H_phys ψ) := by
  exact singletonConcreteHPhysRealizationTheoremData.domain_closed_under_H ψ hψ

theorem singleton_concrete_hphys_symmetric_on_domain
    (ψ φ : singletonConcreteHPhysRealizationTheoremData.carrier)
    (hψ : singletonConcreteHPhysRealizationTheoremData.domain ψ)
    (hφ : singletonConcreteHPhysRealizationTheoremData.domain φ) :
    singletonConcreteHPhysRealizationTheoremData.inner
      (singletonConcreteHPhysRealizationTheoremData.H_phys ψ) φ =
    singletonConcreteHPhysRealizationTheoremData.inner ψ
      (singletonConcreteHPhysRealizationTheoremData.H_phys φ) := by
  exact singletonConcreteHPhysRealizationTheoremData.symmetric_on_domain ψ φ hψ hφ

theorem singleton_concrete_hphys_rayleigh_lower_bound
    (ψ : singletonConcreteHPhysRealizationTheoremData.carrier)
    (hψ : singletonConcreteHPhysRealizationTheoremData.domain ψ) :
    exactGapValueReal ≤
      singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
        (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
          (singletonConcreteHPhysRealizationTheoremData.toHPhysState ψ)) := by
  exact singletonConcreteHPhysRealizationTheoremData.mapped_rayleigh_lower_bound ψ hψ

theorem singleton_concrete_hphys_distinguished_attains_exact :
    singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (singletonConcreteHPhysRealizationTheoremData.toHPhysState
          singletonConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal := by
  exact singletonConcreteHPhysRealizationTheoremData.distinguished_attains_exact

structure ConcreteHPhysRealizationTheoremReviewSurface where
  concreteHilbertReady : concreteHilbertRealizationTheoremReviewSurface.ready
  concreteHPhysDataReady : singletonConcreteHPhysRealizationTheoremData.ready
  domainClosed : ∀ ψ,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
      singletonConcreteHPhysRealizationTheoremData.domain
        (singletonConcreteHPhysRealizationTheoremData.H_phys ψ)
  symmetricOnDomain : ∀ ψ φ,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
    singletonConcreteHPhysRealizationTheoremData.domain φ →
    singletonConcreteHPhysRealizationTheoremData.inner
      (singletonConcreteHPhysRealizationTheoremData.H_phys ψ) φ =
    singletonConcreteHPhysRealizationTheoremData.inner ψ
      (singletonConcreteHPhysRealizationTheoremData.H_phys φ)
  rayleighLowerBound : ∀ ψ,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
    exactGapValueReal ≤
      singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
        (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
          (singletonConcreteHPhysRealizationTheoremData.toHPhysState ψ))
  distinguishedAttainsExact :
    singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (singletonConcreteHPhysRealizationTheoremData.toHPhysState
          singletonConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal
  concreteHPhysRealizationBodyClosed :
    singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (singletonConcreteHPhysRealizationTheoremData.toHPhysState
          singletonConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal
  operatorResidualStillOpen :
    ∃ ψ : singletonConcreteHPhysRealizationTheoremData.carrier,
      singletonConcreteHPhysRealizationTheoremData.domain ψ ∧
        singletonConcreteHPhysRealizationTheoremData.domain
          (singletonConcreteHPhysRealizationTheoremData.H_phys ψ)
  finalReleaseHeld : 0 < exactGapValueReal
  publicBoundaryHeld : ∀ ψ,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
      singletonConcreteHPhysRealizationTheoremData.domain
        (singletonConcreteHPhysRealizationTheoremData.H_phys ψ)

def ConcreteHPhysRealizationTheoremReviewSurface.ready
    (S : ConcreteHPhysRealizationTheoremReviewSurface) : Prop :=
  concreteHilbertRealizationTheoremReviewSurface.ready ∧
  singletonConcreteHPhysRealizationTheoremData.ready ∧
  (∀ ψ : singletonConcreteHPhysRealizationTheoremData.carrier,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
      singletonConcreteHPhysRealizationTheoremData.domain
        (singletonConcreteHPhysRealizationTheoremData.H_phys ψ)) ∧
  (∀ ψ φ : singletonConcreteHPhysRealizationTheoremData.carrier,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
    singletonConcreteHPhysRealizationTheoremData.domain φ →
    singletonConcreteHPhysRealizationTheoremData.inner
      (singletonConcreteHPhysRealizationTheoremData.H_phys ψ) φ =
    singletonConcreteHPhysRealizationTheoremData.inner ψ
      (singletonConcreteHPhysRealizationTheoremData.H_phys φ)) ∧
  (∀ ψ : singletonConcreteHPhysRealizationTheoremData.carrier,
    singletonConcreteHPhysRealizationTheoremData.domain ψ →
    exactGapValueReal ≤
      singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
        (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
          (singletonConcreteHPhysRealizationTheoremData.toHPhysState ψ))) ∧
  (singletonConcreteHPhysRealizationTheoremData.hphysData.rayleighData.quotient
      (singletonConcreteHPhysRealizationTheoremData.hphysData.state_to_rayleigh
        (singletonConcreteHPhysRealizationTheoremData.toHPhysState
          singletonConcreteHPhysRealizationTheoremData.distinguished)) = exactGapValueReal) ∧
  S.concreteHPhysRealizationBodyClosed ∧ S.operatorResidualStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

noncomputable def concreteHPhysRealizationTheoremReviewSurface :
    ConcreteHPhysRealizationTheoremReviewSurface :=
  { concreteHilbertReady := concrete_hilbert_realization_theorem_review_surface_ready
    concreteHPhysDataReady := singleton_concrete_hphys_realization_theorem_data_ready
    domainClosed := singleton_concrete_hphys_domain_closed
    symmetricOnDomain := singleton_concrete_hphys_symmetric_on_domain
    rayleighLowerBound := singleton_concrete_hphys_rayleigh_lower_bound
    distinguishedAttainsExact := singleton_concrete_hphys_distinguished_attains_exact
    concreteHPhysRealizationBodyClosed := singleton_concrete_hphys_distinguished_attains_exact
    operatorResidualStillOpen :=
      ⟨singletonConcreteHPhysRealizationTheoremData.distinguished,
        singletonConcreteHPhysRealizationTheoremData.distinguished_in_domain,
        singleton_concrete_hphys_domain_closed
          singletonConcreteHPhysRealizationTheoremData.distinguished
          singletonConcreteHPhysRealizationTheoremData.distinguished_in_domain⟩
    finalReleaseHeld := exactGapValueReal_pos
    publicBoundaryHeld := singleton_concrete_hphys_domain_closed }

theorem concrete_hphys_realization_theorem_review_surface_ready :
    concreteHPhysRealizationTheoremReviewSurface.ready := by
  exact And.intro concrete_hilbert_realization_theorem_review_surface_ready <|
    And.intro singleton_concrete_hphys_realization_theorem_data_ready <|
    And.intro singleton_concrete_hphys_domain_closed <|
    And.intro singleton_concrete_hphys_symmetric_on_domain <|
    And.intro singleton_concrete_hphys_rayleigh_lower_bound <|
    And.intro singleton_concrete_hphys_distinguished_attains_exact <|
    And.intro singleton_concrete_hphys_distinguished_attains_exact <|
    And.intro
      (⟨singletonConcreteHPhysRealizationTheoremData.distinguished,
        singletonConcreteHPhysRealizationTheoremData.distinguished_in_domain,
        singleton_concrete_hphys_domain_closed
          singletonConcreteHPhysRealizationTheoremData.distinguished
          singletonConcreteHPhysRealizationTheoremData.distinguished_in_domain⟩) <|
    And.intro exactGapValueReal_pos singleton_concrete_hphys_domain_closed

theorem concrete_hphys_realization_theorem_review_surface_final_release_held :
    ConcreteHPhysRealizationTheoremReviewSurface.finalReleaseHeld
      concreteHPhysRealizationTheoremReviewSurface := by
  exact exactGapValueReal_pos

end MathlibAnalytic
end MGAP4D
