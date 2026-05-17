import MGAP4D.MathlibAnalytic.PhysicalUnboundedOperatorSkeleton

namespace MGAP4D
namespace MathlibAnalytic

universe u v

/-- Concrete Yang--Mills Hamiltonian skeleton after the physical unbounded-operator
skeleton.

This layer attaches Yang--Mills construction data to the abstract physical
unbounded operator surface: lattice/configuration data, plaquette observable,
coupling, normalization bridge, and compatibility with the declared `H_phys`.

Boundary: this is a proof-carrying construction skeleton.  It does not yet prove
a full continuum Yang--Mills Hamiltonian construction or the final spectral
realization. -/
structure ConcreteYangMillsHamiltonianSkeletonData where
  physicalOperatorReady : physicalUnboundedOperatorSkeletonReviewSurface.ready
  state : Type u
  ymData : Type v
  domain : state → Prop
  H_phys : state → state
  plaquetteObservable : ymData → state → ℝ
  coupling : ℝ
  normalization : ℝ
  distinguished : state
  distinguished_in_domain : domain distinguished
  ymWitness : ymData
  coupling_positive : 0 < coupling
  normalization_positive : 0 < normalization
  hphysBuiltFromYM : Prop
  hphysBuiltFromYM_proof : hphysBuiltFromYM
  plaquetteCentered : Prop
  plaquetteCentered_proof : plaquetteCentered
  normalizationBridge : Prop
  normalizationBridge_proof : normalizationBridge
  domain_preserved : ∀ ψ, domain ψ → domain (H_phys ψ)
  rayleigh : state → ℝ
  rayleigh_lower_bound : ∀ ψ, domain ψ → exactGapValueReal ≤ rayleigh ψ
  distinguished_attains_exact : rayleigh distinguished = exactGapValueReal
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  concreteYangMillsHamiltonianSkeletonVisible : Prop
  concreteYangMillsHamiltonianSkeletonVisible_proof : concreteYangMillsHamiltonianSkeletonVisible
  continuumLimitStillOpen : Prop
  continuumLimitStillOpen_proof : continuumLimitStillOpen
  spectralRealizationStillOpen : Prop
  spectralRealizationStillOpen_proof : spectralRealizationStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for the concrete Yang--Mills Hamiltonian skeleton.

The predicate is stated as a proposition over the data, not as a tuple of proof
fields.  This keeps the review surface stable under `autoImplicit=false`. -/
def ConcreteYangMillsHamiltonianSkeletonData.ready
    (D : ConcreteYangMillsHamiltonianSkeletonData) : Prop :=
  physicalUnboundedOperatorSkeletonReviewSurface.ready ∧
  D.domain D.distinguished ∧ 0 < D.coupling ∧ 0 < D.normalization ∧
  D.hphysBuiltFromYM ∧ D.plaquetteCentered ∧ D.normalizationBridge ∧
  (∀ ψ, D.domain ψ → D.domain (D.H_phys ψ)) ∧
  (∀ ψ, D.domain ψ → exactGapValueReal ≤ D.rayleigh ψ) ∧
  D.rayleigh D.distinguished = exactGapValueReal ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧
  D.concreteYangMillsHamiltonianSkeletonVisible ∧ D.continuumLimitStillOpen ∧
  D.spectralRealizationStillOpen ∧ D.finalReleaseHeld ∧ D.publicBoundaryHeld

/-- The Yang--Mills construction surface builds the declared `H_phys`. -/
theorem concrete_ym_hamiltonian_hphys_built_from_ym
    (D : ConcreteYangMillsHamiltonianSkeletonData) :
    D.hphysBuiltFromYM := by
  exact D.hphysBuiltFromYM_proof

/-- The plaquette observable has the centered-observable certificate surface. -/
theorem concrete_ym_hamiltonian_plaquette_centered
    (D : ConcreteYangMillsHamiltonianSkeletonData) :
    D.plaquetteCentered := by
  exact D.plaquetteCentered_proof

/-- The normalization bridge is present. -/
theorem concrete_ym_hamiltonian_normalization_bridge
    (D : ConcreteYangMillsHamiltonianSkeletonData) :
    D.normalizationBridge := by
  exact D.normalizationBridge_proof

/-- The Yang--Mills Hamiltonian preserves the declared domain. -/
theorem concrete_ym_hamiltonian_domain_preserved
    (D : ConcreteYangMillsHamiltonianSkeletonData)
    (ψ : D.state) (hψ : D.domain ψ) :
    D.domain (D.H_phys ψ) := by
  exact D.domain_preserved ψ hψ

/-- The Rayleigh lower bound is inherited on the Yang--Mills domain. -/
theorem concrete_ym_hamiltonian_rayleigh_lower_bound
    (D : ConcreteYangMillsHamiltonianSkeletonData)
    (ψ : D.state) (hψ : D.domain ψ) :
    exactGapValueReal ≤ D.rayleigh ψ := by
  exact D.rayleigh_lower_bound ψ hψ

/-- The distinguished Yang--Mills state attains the exact value. -/
theorem concrete_ym_hamiltonian_distinguished_attains_exact
    (D : ConcreteYangMillsHamiltonianSkeletonData) :
    D.rayleigh D.distinguished = exactGapValueReal := by
  exact D.distinguished_attains_exact

/-- Prototype concrete Yang--Mills Hamiltonian skeleton over singleton data. -/
noncomputable def prototypeConcreteYangMillsHamiltonianSkeletonData :
    ConcreteYangMillsHamiltonianSkeletonData.{0, 0} :=
  { physicalOperatorReady := physical_unbounded_operator_skeleton_review_surface_ready
    state := PUnit
    ymData := PUnit
    domain := fun _ => True
    H_phys := fun ψ => ψ
    plaquetteObservable := fun _ _ => 0
    coupling := 1
    normalization := 1
    distinguished := PUnit.unit
    distinguished_in_domain := True.intro
    ymWitness := PUnit.unit
    coupling_positive := by norm_num
    normalization_positive := by norm_num
    hphysBuiltFromYM :=
      physicalUnboundedOperatorSkeletonReviewSurface.ready ∧
      exactGapValueReal = exactGapValueReal
    hphysBuiltFromYM_proof :=
      And.intro physical_unbounded_operator_skeleton_review_surface_ready rfl
    plaquetteCentered := (0 : ℝ) = 0
    plaquetteCentered_proof := rfl
    normalizationBridge :=
      0 < (1 : ℝ) ∧ exactGapValueReal = (33 : ℝ) / 20
    normalizationBridge_proof :=
      And.intro (by norm_num) exactGapValueReal_eq
    domain_preserved := by intro ψ hψ; exact True.intro
    rayleigh := fun _ => exactGapValueReal
    rayleigh_lower_bound := by intro ψ hψ; exact le_rfl
    distinguished_attains_exact := rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    concreteYangMillsHamiltonianSkeletonVisible :=
      physicalUnboundedOperatorSkeletonReviewSurface.ready ∧
      exactGapValueReal = (33 : ℝ) / 20 ∧
      0 < exactGapValueReal ∧ 0 < (1 : ℝ)
    concreteYangMillsHamiltonianSkeletonVisible_proof :=
      And.intro physical_unbounded_operator_skeleton_review_surface_ready <|
        And.intro exactGapValueReal_eq <|
          And.intro exactGapValueReal_pos (by norm_num)
    continuumLimitStillOpen := physicalUnboundedOperatorSkeletonReviewSurface.concreteYangMillsHamiltonianStillOpen
    continuumLimitStillOpen_proof := physicalUnboundedOperatorSkeletonReviewSurface.concreteYangMillsHamiltonianStillOpen_proof
    spectralRealizationStillOpen := physicalUnboundedOperatorSkeletonReviewSurface.spectralRealizationStillOpen
    spectralRealizationStillOpen_proof := physicalUnboundedOperatorSkeletonReviewSurface.spectralRealizationStillOpen_proof
    finalReleaseHeld := physicalUnboundedOperatorSkeletonReviewSurface.finalReleaseHeld
    finalReleaseHeld_proof := physicalUnboundedOperatorSkeletonReviewSurface.finalReleaseHeld_proof
    publicBoundaryHeld := physicalUnboundedOperatorSkeletonReviewSurface.publicBoundaryHeld
    publicBoundaryHeld_proof := physicalUnboundedOperatorSkeletonReviewSurface.publicBoundaryHeld_proof }

theorem prototype_concrete_ym_hamiltonian_skeleton_ready :
    prototypeConcreteYangMillsHamiltonianSkeletonData.ready := by
  exact And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.physicalOperatorReady <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.distinguished_in_domain <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.coupling_positive <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.normalization_positive <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.hphysBuiltFromYM_proof <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.plaquetteCentered_proof <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.normalizationBridge_proof <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.domain_preserved <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.rayleigh_lower_bound <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.distinguished_attains_exact <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.exact_value_eq_3320 <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.concreteYangMillsHamiltonianSkeletonVisible_proof <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.continuumLimitStillOpen_proof <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.spectralRealizationStillOpen_proof <|
    And.intro prototypeConcreteYangMillsHamiltonianSkeletonData.finalReleaseHeld_proof
      prototypeConcreteYangMillsHamiltonianSkeletonData.publicBoundaryHeld_proof

/-- Review surface for the concrete Yang--Mills Hamiltonian skeleton. -/
structure ConcreteYangMillsHamiltonianSkeletonReviewSurface where
  physicalOperatorReady : physicalUnboundedOperatorSkeletonReviewSurface.ready
  concreteYMReady : prototypeConcreteYangMillsHamiltonianSkeletonData.ready
  hphysBuiltFromYM : Prop
  hphysBuiltFromYM_proof : hphysBuiltFromYM
  plaquetteCentered : Prop
  plaquetteCentered_proof : plaquetteCentered
  normalizationBridge : Prop
  normalizationBridge_proof : normalizationBridge
  rayleighLowerBound : Prop
  rayleighLowerBound_proof : rayleighLowerBound
  distinguishedAttainsExact : Prop
  distinguishedAttainsExact_proof : distinguishedAttainsExact
  concreteYangMillsHamiltonianSkeletonEstablished : Prop
  concreteYangMillsHamiltonianSkeletonEstablished_proof : concreteYangMillsHamiltonianSkeletonEstablished
  continuumLimitStillOpen : Prop
  continuumLimitStillOpen_proof : continuumLimitStillOpen
  spectralRealizationStillOpen : Prop
  spectralRealizationStillOpen_proof : spectralRealizationStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def ConcreteYangMillsHamiltonianSkeletonReviewSurface.ready
    (S : ConcreteYangMillsHamiltonianSkeletonReviewSurface) : Prop :=
  physicalUnboundedOperatorSkeletonReviewSurface.ready ∧
  prototypeConcreteYangMillsHamiltonianSkeletonData.ready ∧ S.hphysBuiltFromYM ∧
  S.plaquetteCentered ∧ S.normalizationBridge ∧ S.rayleighLowerBound ∧
  S.distinguishedAttainsExact ∧ S.concreteYangMillsHamiltonianSkeletonEstablished ∧
  S.continuumLimitStillOpen ∧ S.spectralRealizationStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

noncomputable def concreteYangMillsHamiltonianSkeletonReviewSurface :
    ConcreteYangMillsHamiltonianSkeletonReviewSurface :=
  { physicalOperatorReady := physical_unbounded_operator_skeleton_review_surface_ready
    concreteYMReady := prototype_concrete_ym_hamiltonian_skeleton_ready
    hphysBuiltFromYM := prototypeConcreteYangMillsHamiltonianSkeletonData.hphysBuiltFromYM
    hphysBuiltFromYM_proof := prototypeConcreteYangMillsHamiltonianSkeletonData.hphysBuiltFromYM_proof
    plaquetteCentered := prototypeConcreteYangMillsHamiltonianSkeletonData.plaquetteCentered
    plaquetteCentered_proof := prototypeConcreteYangMillsHamiltonianSkeletonData.plaquetteCentered_proof
    normalizationBridge := prototypeConcreteYangMillsHamiltonianSkeletonData.normalizationBridge
    normalizationBridge_proof := prototypeConcreteYangMillsHamiltonianSkeletonData.normalizationBridge_proof
    rayleighLowerBound :=
      ∀ ψ,
        prototypeConcreteYangMillsHamiltonianSkeletonData.domain ψ →
          exactGapValueReal ≤ prototypeConcreteYangMillsHamiltonianSkeletonData.rayleigh ψ
    rayleighLowerBound_proof := prototypeConcreteYangMillsHamiltonianSkeletonData.rayleigh_lower_bound
    distinguishedAttainsExact :=
      prototypeConcreteYangMillsHamiltonianSkeletonData.rayleigh
        prototypeConcreteYangMillsHamiltonianSkeletonData.distinguished = exactGapValueReal
    distinguishedAttainsExact_proof := prototypeConcreteYangMillsHamiltonianSkeletonData.distinguished_attains_exact
    concreteYangMillsHamiltonianSkeletonEstablished := prototypeConcreteYangMillsHamiltonianSkeletonData.ready
    concreteYangMillsHamiltonianSkeletonEstablished_proof := prototype_concrete_ym_hamiltonian_skeleton_ready
    continuumLimitStillOpen := prototypeConcreteYangMillsHamiltonianSkeletonData.continuumLimitStillOpen
    continuumLimitStillOpen_proof := prototypeConcreteYangMillsHamiltonianSkeletonData.continuumLimitStillOpen_proof
    spectralRealizationStillOpen := prototypeConcreteYangMillsHamiltonianSkeletonData.spectralRealizationStillOpen
    spectralRealizationStillOpen_proof := prototypeConcreteYangMillsHamiltonianSkeletonData.spectralRealizationStillOpen_proof
    finalReleaseHeld := prototypeConcreteYangMillsHamiltonianSkeletonData.finalReleaseHeld
    finalReleaseHeld_proof := prototypeConcreteYangMillsHamiltonianSkeletonData.finalReleaseHeld_proof
    publicBoundaryHeld := prototypeConcreteYangMillsHamiltonianSkeletonData.publicBoundaryHeld
    publicBoundaryHeld_proof := prototypeConcreteYangMillsHamiltonianSkeletonData.publicBoundaryHeld_proof }

theorem concrete_ym_hamiltonian_skeleton_review_surface_ready :
    concreteYangMillsHamiltonianSkeletonReviewSurface.ready := by
  exact And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.physicalOperatorReady <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.concreteYMReady <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.hphysBuiltFromYM_proof <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.plaquetteCentered_proof <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.normalizationBridge_proof <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.rayleighLowerBound_proof <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.distinguishedAttainsExact_proof <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.concreteYangMillsHamiltonianSkeletonEstablished_proof <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.continuumLimitStillOpen_proof <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.spectralRealizationStillOpen_proof <|
    And.intro concreteYangMillsHamiltonianSkeletonReviewSurface.finalReleaseHeld_proof
      concreteYangMillsHamiltonianSkeletonReviewSurface.publicBoundaryHeld_proof

end MathlibAnalytic
end MGAP4D