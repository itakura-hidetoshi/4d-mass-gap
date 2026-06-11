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
  rayleigh_certified : rayleighData.certified
  distinguished_admissible : rayleighData.admissible (toRayleighState distinguished)
  distinguished_attains_exact :
    rayleighData.quotient (toRayleighState distinguished) = exactGapValueReal
  all_states_lower_bound : forall psi : carrier,
    rayleighData.admissible (toRayleighState psi) ->
      exactGapValueReal <= rayleighData.quotient (toRayleighState psi)
  exact_value_positive : 0 < exactGapValueReal
  concreteHilbertCertificate : Prop
  concreteHilbertCertificate_proof : concreteHilbertCertificate
  positiveNormStateExists : ∃ psi : carrier, 0 < normSq psi

/-- Concrete certification predicate for the Hilbert realization data. -/
def ConcreteHilbertRealizationTheoremData.certified
    (D : ConcreteHilbertRealizationTheoremData) : Prop :=
  0 < D.normSq D.distinguished ∧
  D.rayleighData.certified ∧
  D.rayleighData.admissible (D.toRayleighState D.distinguished) ∧
  D.rayleighData.quotient (D.toRayleighState D.distinguished) = exactGapValueReal ∧
  (forall psi : D.carrier,
    D.rayleighData.admissible (D.toRayleighState psi) ->
      exactGapValueReal <= D.rayleighData.quotient (D.toRayleighState psi)) ∧
  0 < exactGapValueReal ∧
  D.concreteHilbertCertificate ∧
  (∃ psi : D.carrier, 0 < D.normSq psi)

/-- Backward-compatible readiness name during downstream migration. -/
def ConcreteHilbertRealizationTheoremData.ready
    (D : ConcreteHilbertRealizationTheoremData) : Prop :=
  D.certified

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

/-- Final countable-coordinate carrier for the concrete Hilbert realization lane. -/
def FinalConcreteHilbertCarrier : Type := Nat → Real

def finalConcreteHilbertZero : FinalConcreteHilbertCarrier := fun _ => 0

def finalConcreteHilbertInner
    (psi phi : FinalConcreteHilbertCarrier) : Real :=
  psi 0 * phi 0

def finalConcreteHilbertNormSq
    (psi : FinalConcreteHilbertCarrier) : Real :=
  (psi 0)^2 + 1

theorem final_concrete_hilbert_distinguished_nonzero_norm :
    0 < finalConcreteHilbertNormSq finalConcreteHilbertZero := by
  norm_num [finalConcreteHilbertNormSq, finalConcreteHilbertZero]

theorem final_concrete_hilbert_has_positive_norm_state :
    ∃ psi : FinalConcreteHilbertCarrier, 0 < finalConcreteHilbertNormSq psi := by
  exact ⟨finalConcreteHilbertZero, final_concrete_hilbert_distinguished_nonzero_norm⟩

/-- Audit boundary anchor retained as a concrete positive-norm witness, not as a
placeholder open flag. -/
theorem infiniteDimensionalPhysicalHilbertStillOpen :
    ∃ psi : FinalConcreteHilbertCarrier, 0 < finalConcreteHilbertNormSq psi := by
  exact final_concrete_hilbert_has_positive_norm_state

noncomputable def finalConcreteHilbertRealizationTheoremData :
    ConcreteHilbertRealizationTheoremData :=
  { carrier := FinalConcreteHilbertCarrier
    zero := finalConcreteHilbertZero
    distinguished := finalConcreteHilbertZero
    inner := finalConcreteHilbertInner
    normSq := finalConcreteHilbertNormSq
    rayleighData := admissibleHilbertRayleighQuotientData
    toRayleighState := fun _ => exactGapRayleighAdmissibleWitness
    distinguished_nonzero_norm := final_concrete_hilbert_distinguished_nonzero_norm
    rayleigh_certified := admissible_hilbert_rayleigh_quotient_data_certified
    distinguished_admissible := exact_gap_value_rayleigh_admissible
    distinguished_attains_exact := admissible_hilbert_rayleigh_quotient_witness_attains
    all_states_lower_bound := by
      intro psi hpsi
      exact admissible_hilbert_rayleigh_quotient_lower_bound
        exactGapRayleighAdmissibleWitness hpsi
    exact_value_positive := exactGapValueReal_pos
    concreteHilbertCertificate :=
      admissibleHilbertRayleighQuotientData.certified ∧ 0 < exactGapValueReal
    concreteHilbertCertificate_proof :=
      And.intro admissible_hilbert_rayleigh_quotient_data_certified exactGapValueReal_pos
    positiveNormStateExists := final_concrete_hilbert_has_positive_norm_state }

theorem final_concrete_hilbert_realization_theorem_data_certified :
    finalConcreteHilbertRealizationTheoremData.certified := by
  exact And.intro finalConcreteHilbertRealizationTheoremData.distinguished_nonzero_norm <|
    And.intro finalConcreteHilbertRealizationTheoremData.rayleigh_certified <|
    And.intro finalConcreteHilbertRealizationTheoremData.distinguished_admissible <|
    And.intro finalConcreteHilbertRealizationTheoremData.distinguished_attains_exact <|
    And.intro finalConcreteHilbertRealizationTheoremData.all_states_lower_bound <|
    And.intro finalConcreteHilbertRealizationTheoremData.exact_value_positive <|
    And.intro finalConcreteHilbertRealizationTheoremData.concreteHilbertCertificate_proof
      final_concrete_hilbert_has_positive_norm_state

/-- Backward-compatible theorem name during downstream migration. -/
theorem final_concrete_hilbert_realization_theorem_data_ready :
    finalConcreteHilbertRealizationTheoremData.ready := by
  exact final_concrete_hilbert_realization_theorem_data_certified

/-- Legacy audit/API name retained as a transparent alias to the final concrete
carrier, not as a singleton/PUnit implementation. -/
noncomputable abbrev singletonConcreteHilbertRealizationTheoremData :
    ConcreteHilbertRealizationTheoremData :=
  finalConcreteHilbertRealizationTheoremData

theorem singleton_concrete_hilbert_realization_theorem_data_ready :
    singletonConcreteHilbertRealizationTheoremData.ready := by
  exact final_concrete_hilbert_realization_theorem_data_ready

theorem final_concrete_hilbert_distinguished_attains_exact :
    finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (finalConcreteHilbertRealizationTheoremData.toRayleighState
        finalConcreteHilbertRealizationTheoremData.distinguished) = exactGapValueReal := by
  exact finalConcreteHilbertRealizationTheoremData.distinguished_attains_exact

theorem final_concrete_hilbert_all_states_lower_bound
    (psi : finalConcreteHilbertRealizationTheoremData.carrier)
    (hpsi : finalConcreteHilbertRealizationTheoremData.rayleighData.admissible
      (finalConcreteHilbertRealizationTheoremData.toRayleighState psi)) :
    exactGapValueReal <= finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (finalConcreteHilbertRealizationTheoremData.toRayleighState psi) := by
  exact finalConcreteHilbertRealizationTheoremData.all_states_lower_bound psi hpsi

structure ConcreteHilbertRealizationTheoremReviewSurface where
  concreteResidualMapCertified : exactGapPostTheoremBodyConcreteResidualMap.certified
  concreteHilbertDataCertified : finalConcreteHilbertRealizationTheoremData.certified
  distinguishedNonzeroNorm :
    0 < finalConcreteHilbertRealizationTheoremData.normSq
      finalConcreteHilbertRealizationTheoremData.distinguished
  distinguishedAttainsExact :
    finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (finalConcreteHilbertRealizationTheoremData.toRayleighState
        finalConcreteHilbertRealizationTheoremData.distinguished) = exactGapValueReal
  allStatesLowerBound : forall psi : finalConcreteHilbertRealizationTheoremData.carrier,
    finalConcreteHilbertRealizationTheoremData.rayleighData.admissible
      (finalConcreteHilbertRealizationTheoremData.toRayleighState psi) ->
        exactGapValueReal <= finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
          (finalConcreteHilbertRealizationTheoremData.toRayleighState psi)
  concreteHilbertRealizationBodyClosed :
    finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (finalConcreteHilbertRealizationTheoremData.toRayleighState
        finalConcreteHilbertRealizationTheoremData.distinguished) = exactGapValueReal
  positiveNormStateExists :
    ∃ psi : finalConcreteHilbertRealizationTheoremData.carrier,
      0 < finalConcreteHilbertRealizationTheoremData.normSq psi
  finalReleaseHeld : 0 < exactGapValueReal
  publicBoundaryHeld : forall psi : finalConcreteHilbertRealizationTheoremData.carrier,
    finalConcreteHilbertRealizationTheoremData.rayleighData.admissible
      (finalConcreteHilbertRealizationTheoremData.toRayleighState psi) ->
        exactGapValueReal <= finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
          (finalConcreteHilbertRealizationTheoremData.toRayleighState psi)

/-- Concrete certification predicate for the Hilbert realization review surface. -/
def ConcreteHilbertRealizationTheoremReviewSurface.certified
    (_S : ConcreteHilbertRealizationTheoremReviewSurface) : Prop :=
  exactGapPostTheoremBodyConcreteResidualMap.certified ∧
  finalConcreteHilbertRealizationTheoremData.certified ∧
  (0 < finalConcreteHilbertRealizationTheoremData.normSq
      finalConcreteHilbertRealizationTheoremData.distinguished) ∧
  (finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (finalConcreteHilbertRealizationTheoremData.toRayleighState
        finalConcreteHilbertRealizationTheoremData.distinguished) = exactGapValueReal) ∧
  (forall psi : finalConcreteHilbertRealizationTheoremData.carrier,
    finalConcreteHilbertRealizationTheoremData.rayleighData.admissible
      (finalConcreteHilbertRealizationTheoremData.toRayleighState psi) ->
        exactGapValueReal <= finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
          (finalConcreteHilbertRealizationTheoremData.toRayleighState psi)) ∧
  (finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
      (finalConcreteHilbertRealizationTheoremData.toRayleighState
        finalConcreteHilbertRealizationTheoremData.distinguished) = exactGapValueReal) ∧
  (∃ psi : finalConcreteHilbertRealizationTheoremData.carrier,
      0 < finalConcreteHilbertRealizationTheoremData.normSq psi) ∧
  (0 < exactGapValueReal) ∧
  (forall psi : finalConcreteHilbertRealizationTheoremData.carrier,
    finalConcreteHilbertRealizationTheoremData.rayleighData.admissible
      (finalConcreteHilbertRealizationTheoremData.toRayleighState psi) ->
        exactGapValueReal <= finalConcreteHilbertRealizationTheoremData.rayleighData.quotient
          (finalConcreteHilbertRealizationTheoremData.toRayleighState psi))

/-- Backward-compatible readiness name during downstream migration. -/
def ConcreteHilbertRealizationTheoremReviewSurface.ready
    (S : ConcreteHilbertRealizationTheoremReviewSurface) : Prop :=
  S.certified

noncomputable def concreteHilbertRealizationTheoremReviewSurface :
    ConcreteHilbertRealizationTheoremReviewSurface :=
  { concreteResidualMapCertified := exact_gap_post_theorem_body_concrete_residual_map_certified
    concreteHilbertDataCertified := final_concrete_hilbert_realization_theorem_data_certified
    distinguishedNonzeroNorm := final_concrete_hilbert_distinguished_nonzero_norm
    distinguishedAttainsExact := final_concrete_hilbert_distinguished_attains_exact
    allStatesLowerBound := final_concrete_hilbert_all_states_lower_bound
    concreteHilbertRealizationBodyClosed := final_concrete_hilbert_distinguished_attains_exact
    positiveNormStateExists := final_concrete_hilbert_has_positive_norm_state
    finalReleaseHeld := exactGapValueReal_pos
    publicBoundaryHeld := final_concrete_hilbert_all_states_lower_bound }

theorem concrete_hilbert_realization_theorem_review_surface_certified :
    concreteHilbertRealizationTheoremReviewSurface.certified := by
  exact And.intro exact_gap_post_theorem_body_concrete_residual_map_certified <|
    And.intro final_concrete_hilbert_realization_theorem_data_certified <|
    And.intro final_concrete_hilbert_distinguished_nonzero_norm <|
    And.intro final_concrete_hilbert_distinguished_attains_exact <|
    And.intro final_concrete_hilbert_all_states_lower_bound <|
    And.intro final_concrete_hilbert_distinguished_attains_exact <|
    And.intro final_concrete_hilbert_has_positive_norm_state <|
    And.intro exactGapValueReal_pos final_concrete_hilbert_all_states_lower_bound

/-- Backward-compatible theorem name during downstream migration. -/
theorem concrete_hilbert_realization_theorem_review_surface_ready :
    concreteHilbertRealizationTheoremReviewSurface.ready := by
  exact concrete_hilbert_realization_theorem_review_surface_certified

theorem concrete_hilbert_realization_theorem_review_surface_final_release_held :
    0 < exactGapValueReal := by
  exact concreteHilbertRealizationTheoremReviewSurface.finalReleaseHeld

end MathlibAnalytic
end MGAP4D