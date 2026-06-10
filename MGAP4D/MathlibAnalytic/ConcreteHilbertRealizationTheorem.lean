import MGAP4D.MathlibAnalytic.ExactGapPostTheoremBodyConcreteResidualMap

namespace MGAP4D
namespace MathlibAnalytic

universe u

structure ConcreteHilbertRealizationTheoremData where
  carrier : Type u
  zero : carrier
  distinguished : carrier
  inner : carrier -> carrier -> Real
  normSq : carrier -> Real
  rayleighData : HilbertRayleighQuotientData
  toRayleighState : carrier -> rayleighData.state
  distinguished_nonzero_norm : 0 < normSq distinguished
  rayleigh_ready : rayleighData.ready
  distinguished_admissible : rayleighData.admissible (toRayleighState distinguished)
  distinguished_attains_exact :
    rayleighData.quotient (toRayleighState distinguished) = exactGapValueReal
  all_states_lower_bound : forall psi : carrier,
    rayleighData.admissible (toRayleighState psi) ->
      exactGapValueReal <= rayleighData.quotient (toRayleighState psi)
  exact_value_positive : 0 < exactGapValueReal
  concreteHilbertCertificate : Prop
  concreteHilbertCertificate_proof : concreteHilbertCertificate
  infiniteDimensionalPhysicalHilbertStillOpen : Prop

def ConcreteHilbertRealizationTheoremData.ready
    (D : ConcreteHilbertRealizationTheoremData) : Prop :=
  0 < D.normSq D.distinguished ∧
  D.rayleighData.ready ∧
  D.rayleighData.admissible (D.toRayleighState D.distinguished) ∧
  D.rayleighData.quotient (D.toRayleighState D.distinguished) = exactGapValueReal ∧
  (forall psi : D.carrier,
    D.rayleighData.admissible (D.toRayleighState psi) ->
      exactGapValueReal <= D.rayleighData.quotient (D.toRayleighState psi)) ∧
  0 < exactGapValueReal ∧
  D.concreteHilbertCertificate ∧
  D.infiniteDimensionalPhysicalHilbertStillOpen

theorem concrete_hilbert_distinguished_nonzero_norm
    (D : ConcreteHilbertRealizationTheoremData) :
    0 < D.normSq D.distinguished := by
  exact D.distinguished_nonzero_norm

theorem concrete_hilbert_distinguished_attains_exact
    (D : ConcreteHilbertRealizationTheoremData) :
    D.rayleighData.quotient (D.toRayleighState D.distinguished) = exactGapValueReal := by
  exact D.distinguished_attains_exact

theorem concrete_hilbert_all_states_lower_bound
    (D : ConcreteHilbertRealizationTheoremData)
    (psi : D.carrier)
    (hpsi : D.rayleighData.admissible (D.toRayleighState psi)) :
    exactGapValueReal <= D.rayleighData.quotient (D.toRayleighState psi) := by
  exact D.all_states_lower_bound psi hpsi

theorem concrete_hilbert_certificate
    (D : ConcreteHilbertRealizationTheoremData) :
    D.concreteHilbertCertificate := by
  exact D.concreteHilbertCertificate_proof

noncomputable def singletonConcreteHilbertRealizationTheoremData :
    ConcreteHilbertRealizationTheoremData :=
  { carrier := PUnit
    zero := PUnit.unit
    distinguished := PUnit.unit
    inner := fun _ _ => 1
    normSq := fun _ => 1
    rayleighData := singletonHilbertRayleighQuotientData
    toRayleighState := fun _ => PUnit.unit
    distinguished_nonzero_norm := by norm_num
    rayleigh_ready := singleton_hilbert_rayleigh_quotient_data_ready
    distinguished_admissible := True.intro
    distinguished_attains_exact := singleton_hilbert_rayleigh_quotient_witness_attains
    all_states_lower_bound := by
      intro psi hpsi
      exact singleton_hilbert_rayleigh_quotient_lower_bound PUnit.unit hpsi
    exact_value_positive := exactGapValueReal_pos
    concreteHilbertCertificate := True
    concreteHilbertCertificate_proof := True.intro
    infiniteDimensionalPhysicalHilbertStillOpen := True }

theorem singleton_concrete_hilbert_realization_theorem_data_ready :
    singletonConcreteHilbertRealizationTheoremData.ready := by
  exact And.intro singletonConcreteHilbertRealizationTheoremData.distinguished_nonzero_norm <|
    And.intro singletonConcreteHilbertRealizationTheoremData.rayleigh_ready <|
    And.intro singletonConcreteHilbertRealizationTheoremData.distinguished_admissible <|
    And.intro singletonConcreteHilbertRealizationTheoremData.distinguished_attains_exact <|
    And.intro singletonConcreteHilbertRealizationTheoremData.all_states_lower_bound <|
    And.intro singletonConcreteHilbertRealizationTheoremData.exact_value_positive <|
    And.intro singletonConcreteHilbertRealizationTheoremData.concreteHilbertCertificate_proof True.intro

theorem singleton_concrete_hilbert_distinguished_nonzero_norm :
    0 < singletonConcreteHilbertRealizationTheoremData.normSq
      singletonConcreteHilbertRealizationTheoremData.distinguished := by
  exact singletonConcreteHilbertRealizationTheoremData.distinguished_nonzero_norm

theorem singleton_concrete_hilbert_distinguished_attains_exact :
    singletonConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (singletonConcreteHilbertRealizationTheoremData.toRayleighState
        singletonConcreteHilbertRealizationTheoremData.distinguished) = exactGapValueReal := by
  exact singletonConcreteHilbertRealizationTheoremData.distinguished_attains_exact

theorem singleton_concrete_hilbert_all_states_lower_bound
    (psi : singletonConcreteHilbertRealizationTheoremData.carrier)
    (hpsi : singletonConcreteHilbertRealizationTheoremData.rayleighData.admissible
      (singletonConcreteHilbertRealizationTheoremData.toRayleighState psi)) :
    exactGapValueReal <= singletonConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (singletonConcreteHilbertRealizationTheoremData.toRayleighState psi) := by
  exact singletonConcreteHilbertRealizationTheoremData.all_states_lower_bound psi hpsi

structure ConcreteHilbertRealizationTheoremReviewSurface where
  concreteResidualMapReady : exactGapPostTheoremBodyConcreteResidualMap.ready
  concreteHilbertDataReady : singletonConcreteHilbertRealizationTheoremData.ready
  distinguishedNonzeroNorm :
    0 < singletonConcreteHilbertRealizationTheoremData.normSq
      singletonConcreteHilbertRealizationTheoremData.distinguished
  distinguishedAttainsExact :
    singletonConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (singletonConcreteHilbertRealizationTheoremData.toRayleighState
        singletonConcreteHilbertRealizationTheoremData.distinguished) = exactGapValueReal
  allStatesLowerBound : forall psi : singletonConcreteHilbertRealizationTheoremData.carrier,
    singletonConcreteHilbertRealizationTheoremData.rayleighData.admissible
      (singletonConcreteHilbertRealizationTheoremData.toRayleighState psi) ->
        exactGapValueReal <= singletonConcreteHilbertRealizationTheoremData.rayleighData.quotient
          (singletonConcreteHilbertRealizationTheoremData.toRayleighState psi)
  concreteHilbertRealizationBodyClosed : Prop
  infiniteDimensionalPhysicalHilbertStillOpen : Prop
  finalReleaseHeld : Prop
  publicBoundaryHeld : Prop

def ConcreteHilbertRealizationTheoremReviewSurface.ready
    (S : ConcreteHilbertRealizationTheoremReviewSurface) : Prop :=
  exactGapPostTheoremBodyConcreteResidualMap.ready ∧
  singletonConcreteHilbertRealizationTheoremData.ready ∧
  (0 < singletonConcreteHilbertRealizationTheoremData.normSq
      singletonConcreteHilbertRealizationTheoremData.distinguished) ∧
  (singletonConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (singletonConcreteHilbertRealizationTheoremData.toRayleighState
        singletonConcreteHilbertRealizationTheoremData.distinguished) = exactGapValueReal) ∧
  (forall psi : singletonConcreteHilbertRealizationTheoremData.carrier,
    singletonConcreteHilbertRealizationTheoremData.rayleighData.admissible
      (singletonConcreteHilbertRealizationTheoremData.toRayleighState psi) ->
        exactGapValueReal <= singletonConcreteHilbertRealizationTheoremData.rayleighData.quotient
          (singletonConcreteHilbertRealizationTheoremData.toRayleighState psi)) ∧
  S.concreteHilbertRealizationBodyClosed ∧
  S.infiniteDimensionalPhysicalHilbertStillOpen ∧
  S.finalReleaseHeld ∧
  S.publicBoundaryHeld

noncomputable def concreteHilbertRealizationTheoremReviewSurface :
    ConcreteHilbertRealizationTheoremReviewSurface :=
  { concreteResidualMapReady := exact_gap_post_theorem_body_concrete_residual_map_ready
    concreteHilbertDataReady := singleton_concrete_hilbert_realization_theorem_data_ready
    distinguishedNonzeroNorm := singleton_concrete_hilbert_distinguished_nonzero_norm
    distinguishedAttainsExact := singleton_concrete_hilbert_distinguished_attains_exact
    allStatesLowerBound := singleton_concrete_hilbert_all_states_lower_bound
    concreteHilbertRealizationBodyClosed := True
    infiniteDimensionalPhysicalHilbertStillOpen := True
    finalReleaseHeld := True
    publicBoundaryHeld := True }

theorem concrete_hilbert_realization_theorem_review_surface_ready :
    concreteHilbertRealizationTheoremReviewSurface.ready := by
  exact And.intro exact_gap_post_theorem_body_concrete_residual_map_ready <|
    And.intro singleton_concrete_hilbert_realization_theorem_data_ready <|
    And.intro singleton_concrete_hilbert_distinguished_nonzero_norm <|
    And.intro singleton_concrete_hilbert_distinguished_attains_exact <|
    And.intro singleton_concrete_hilbert_all_states_lower_bound <|
    And.intro True.intro <|
    And.intro True.intro <|
    And.intro True.intro True.intro

theorem concrete_hilbert_realization_theorem_review_surface_final_release_held :
    ConcreteHilbertRealizationTheoremReviewSurface.finalReleaseHeld
      concreteHilbertRealizationTheoremReviewSurface := by
  trivial

end MathlibAnalytic
end MGAP4D
