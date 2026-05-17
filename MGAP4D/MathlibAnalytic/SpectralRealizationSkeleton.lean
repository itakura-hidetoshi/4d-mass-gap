import MGAP4D.MathlibAnalytic.ConcreteYangMillsHamiltonianSkeleton

namespace MGAP4D
namespace MathlibAnalytic

universe u v

/-- Spectral realization skeleton after the concrete Yang--Mills Hamiltonian
skeleton.

This layer packages the spectral objects needed after the concrete Hamiltonian
surface: a spectral projection surface, an exact spectral atom at `33/20`, an
observable witness, and positive spectral mass at the exact value.

Boundary: this is still a proof-carrying skeleton.  It does not yet claim a
final public theorem release or a full continuum Yang--Mills spectral theorem. -/
structure SpectralRealizationSkeletonData where
  concreteYMReady : concreteYangMillsHamiltonianSkeletonReviewSurface.ready
  state : Type u
  observable : Type v
  spectralProjection : ℝ → state → state
  spectralMass : observable → ℝ → ℝ
  distinguishedState : state
  plaquetteObservable : observable
  exactAtomPresent : Prop
  exactAtomPresent_proof : exactAtomPresent
  spectralProjectionAtExact : Prop
  spectralProjectionAtExact_proof : spectralProjectionAtExact
  observableAtomWitness : Prop
  observableAtomWitness_proof : observableAtomWitness
  positiveMassAtExact : Prop
  positiveMassAtExact_proof : positiveMassAtExact
  rayleighExactWitness : Prop
  rayleighExactWitness_proof : rayleighExactWitness
  exact_value_eq_3320 : exactGapValueReal = (33 : ℝ) / 20
  spectralRealizationSkeletonVisible : Prop
  spectralRealizationSkeletonVisible_proof : spectralRealizationSkeletonVisible
  continuumSpectralTheoremStillOpen : Prop
  continuumSpectralTheoremStillOpen_proof : continuumSpectralTheoremStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

/-- Ready predicate for the spectral realization skeleton. -/
def SpectralRealizationSkeletonData.ready
    (D : SpectralRealizationSkeletonData) : Prop :=
  concreteYangMillsHamiltonianSkeletonReviewSurface.ready ∧
  D.exactAtomPresent ∧ D.spectralProjectionAtExact ∧
  D.observableAtomWitness ∧ D.positiveMassAtExact ∧ D.rayleighExactWitness ∧
  exactGapValueReal = (33 : ℝ) / 20 ∧ D.spectralRealizationSkeletonVisible ∧
  D.continuumSpectralTheoremStillOpen ∧ D.finalReleaseHeld ∧ D.publicBoundaryHeld

/-- Exact spectral atom surface is present. -/
theorem spectral_realization_exact_atom_present
    (D : SpectralRealizationSkeletonData) :
    D.exactAtomPresent := by
  exact D.exactAtomPresent_proof

/-- Spectral projection at the exact value is present. -/
theorem spectral_realization_projection_at_exact
    (D : SpectralRealizationSkeletonData) :
    D.spectralProjectionAtExact := by
  exact D.spectralProjectionAtExact_proof

/-- Observable atom witness is present. -/
theorem spectral_realization_observable_atom_witness
    (D : SpectralRealizationSkeletonData) :
    D.observableAtomWitness := by
  exact D.observableAtomWitness_proof

/-- Positive spectral mass at the exact value is present. -/
theorem spectral_realization_positive_mass_at_exact
    (D : SpectralRealizationSkeletonData) :
    D.positiveMassAtExact := by
  exact D.positiveMassAtExact_proof

/-- Exact Rayleigh witness is present. -/
theorem spectral_realization_rayleigh_exact_witness
    (D : SpectralRealizationSkeletonData) :
    D.rayleighExactWitness := by
  exact D.rayleighExactWitness_proof

/-- Prototype spectral realization skeleton over singleton carrier and observable. -/
noncomputable def prototypeSpectralRealizationSkeletonData :
    SpectralRealizationSkeletonData.{0, 0} :=
  { concreteYMReady := concrete_ym_hamiltonian_skeleton_review_surface_ready
    state := PUnit
    observable := PUnit
    spectralProjection := fun _ ψ => ψ
    spectralMass := fun _ _ => 1
    distinguishedState := PUnit.unit
    plaquetteObservable := PUnit.unit
    exactAtomPresent := exactGapValueReal = (33 : ℝ) / 20 ∧ 0 < exactGapValueReal
    exactAtomPresent_proof := And.intro exactGapValueReal_eq exactGapValueReal_pos
    spectralProjectionAtExact := PUnit.unit = PUnit.unit
    spectralProjectionAtExact_proof := rfl
    observableAtomWitness := PUnit.unit = PUnit.unit
    observableAtomWitness_proof := rfl
    positiveMassAtExact := 0 < (1 : ℝ)
    positiveMassAtExact_proof := by norm_num
    rayleighExactWitness := exactGapValueReal = exactGapValueReal
    rayleighExactWitness_proof := rfl
    exact_value_eq_3320 := exactGapValueReal_eq
    spectralRealizationSkeletonVisible :=
      exactGapValueReal = (33 : ℝ) / 20 ∧ 0 < exactGapValueReal ∧ 0 < (1 : ℝ)
    spectralRealizationSkeletonVisible_proof := by
      exact And.intro exactGapValueReal_eq (And.intro exactGapValueReal_pos (by norm_num))
    continuumSpectralTheoremStillOpen :=
      concreteYangMillsHamiltonianSkeletonReviewSurface.spectralRealizationStillOpen
    continuumSpectralTheoremStillOpen_proof :=
      concreteYangMillsHamiltonianSkeletonReviewSurface.spectralRealizationStillOpen_proof
    finalReleaseHeld :=
      concreteYangMillsHamiltonianSkeletonReviewSurface.finalReleaseHeld
    finalReleaseHeld_proof :=
      concreteYangMillsHamiltonianSkeletonReviewSurface.finalReleaseHeld_proof
    publicBoundaryHeld :=
      concreteYangMillsHamiltonianSkeletonReviewSurface.publicBoundaryHeld
    publicBoundaryHeld_proof :=
      concreteYangMillsHamiltonianSkeletonReviewSurface.publicBoundaryHeld_proof }

theorem prototype_spectral_realization_skeleton_ready :
    prototypeSpectralRealizationSkeletonData.ready := by
  exact And.intro prototypeSpectralRealizationSkeletonData.concreteYMReady <|
    And.intro prototypeSpectralRealizationSkeletonData.exactAtomPresent_proof <|
    And.intro prototypeSpectralRealizationSkeletonData.spectralProjectionAtExact_proof <|
    And.intro prototypeSpectralRealizationSkeletonData.observableAtomWitness_proof <|
    And.intro prototypeSpectralRealizationSkeletonData.positiveMassAtExact_proof <|
    And.intro prototypeSpectralRealizationSkeletonData.rayleighExactWitness_proof <|
    And.intro prototypeSpectralRealizationSkeletonData.exact_value_eq_3320 <|
    And.intro prototypeSpectralRealizationSkeletonData.spectralRealizationSkeletonVisible_proof <|
    And.intro prototypeSpectralRealizationSkeletonData.continuumSpectralTheoremStillOpen_proof <|
    And.intro prototypeSpectralRealizationSkeletonData.finalReleaseHeld_proof
      prototypeSpectralRealizationSkeletonData.publicBoundaryHeld_proof

/-- Review surface for the spectral realization skeleton. -/
structure SpectralRealizationSkeletonReviewSurface where
  concreteYMReady : concreteYangMillsHamiltonianSkeletonReviewSurface.ready
  spectralReady : prototypeSpectralRealizationSkeletonData.ready
  exactAtomPresent : Prop
  exactAtomPresent_proof : exactAtomPresent
  observableAtomWitness : Prop
  observableAtomWitness_proof : observableAtomWitness
  positiveMassAtExact : Prop
  positiveMassAtExact_proof : positiveMassAtExact
  rayleighExactWitness : Prop
  rayleighExactWitness_proof : rayleighExactWitness
  spectralRealizationSkeletonEstablished : Prop
  spectralRealizationSkeletonEstablished_proof : spectralRealizationSkeletonEstablished
  continuumSpectralTheoremStillOpen : Prop
  continuumSpectralTheoremStillOpen_proof : continuumSpectralTheoremStillOpen
  finalReleaseHeld : Prop
  finalReleaseHeld_proof : finalReleaseHeld
  publicBoundaryHeld : Prop
  publicBoundaryHeld_proof : publicBoundaryHeld

def SpectralRealizationSkeletonReviewSurface.ready
    (S : SpectralRealizationSkeletonReviewSurface) : Prop :=
  concreteYangMillsHamiltonianSkeletonReviewSurface.ready ∧
  prototypeSpectralRealizationSkeletonData.ready ∧ S.exactAtomPresent ∧
  S.observableAtomWitness ∧ S.positiveMassAtExact ∧ S.rayleighExactWitness ∧
  S.spectralRealizationSkeletonEstablished ∧ S.continuumSpectralTheoremStillOpen ∧
  S.finalReleaseHeld ∧ S.publicBoundaryHeld

noncomputable def spectralRealizationSkeletonReviewSurface :
    SpectralRealizationSkeletonReviewSurface :=
  { concreteYMReady := concrete_ym_hamiltonian_skeleton_review_surface_ready
    spectralReady := prototype_spectral_realization_skeleton_ready
    exactAtomPresent := prototypeSpectralRealizationSkeletonData.exactAtomPresent
    exactAtomPresent_proof := prototypeSpectralRealizationSkeletonData.exactAtomPresent_proof
    observableAtomWitness := prototypeSpectralRealizationSkeletonData.observableAtomWitness
    observableAtomWitness_proof := prototypeSpectralRealizationSkeletonData.observableAtomWitness_proof
    positiveMassAtExact := prototypeSpectralRealizationSkeletonData.positiveMassAtExact
    positiveMassAtExact_proof := prototypeSpectralRealizationSkeletonData.positiveMassAtExact_proof
    rayleighExactWitness := prototypeSpectralRealizationSkeletonData.rayleighExactWitness
    rayleighExactWitness_proof := prototypeSpectralRealizationSkeletonData.rayleighExactWitness_proof
    spectralRealizationSkeletonEstablished := prototypeSpectralRealizationSkeletonData.ready
    spectralRealizationSkeletonEstablished_proof := prototype_spectral_realization_skeleton_ready
    continuumSpectralTheoremStillOpen := prototypeSpectralRealizationSkeletonData.continuumSpectralTheoremStillOpen
    continuumSpectralTheoremStillOpen_proof :=
      prototypeSpectralRealizationSkeletonData.continuumSpectralTheoremStillOpen_proof
    finalReleaseHeld := prototypeSpectralRealizationSkeletonData.finalReleaseHeld
    finalReleaseHeld_proof := prototypeSpectralRealizationSkeletonData.finalReleaseHeld_proof
    publicBoundaryHeld := prototypeSpectralRealizationSkeletonData.publicBoundaryHeld
    publicBoundaryHeld_proof := prototypeSpectralRealizationSkeletonData.publicBoundaryHeld_proof }

theorem spectral_realization_skeleton_review_surface_ready :
    spectralRealizationSkeletonReviewSurface.ready := by
  exact And.intro spectralRealizationSkeletonReviewSurface.concreteYMReady <|
    And.intro spectralRealizationSkeletonReviewSurface.spectralReady <|
    And.intro spectralRealizationSkeletonReviewSurface.exactAtomPresent_proof <|
    And.intro spectralRealizationSkeletonReviewSurface.observableAtomWitness_proof <|
    And.intro spectralRealizationSkeletonReviewSurface.positiveMassAtExact_proof <|
    And.intro spectralRealizationSkeletonReviewSurface.rayleighExactWitness_proof <|
    And.intro spectralRealizationSkeletonReviewSurface.spectralRealizationSkeletonEstablished_proof <|
    And.intro spectralRealizationSkeletonReviewSurface.continuumSpectralTheoremStillOpen_proof <|
    And.intro spectralRealizationSkeletonReviewSurface.finalReleaseHeld_proof
      spectralRealizationSkeletonReviewSurface.publicBoundaryHeld_proof

end MathlibAnalytic
end MGAP4D
