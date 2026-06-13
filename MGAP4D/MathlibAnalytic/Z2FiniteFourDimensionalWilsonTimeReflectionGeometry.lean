import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonPlaquetteSideClassification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Four-dimensional integer coordinates and the vertex support of every
plaquette.  Coordinate `0` is the Euclidean time coordinate; coordinates
`1,2,3` are spatial. -/
structure FiniteFourDimensionalWilsonGeometry
    (L : FiniteLatticeWilsonSystem) where
  coordinate : L.Vertex → Fin 4 → ℤ
  plaquetteVertices : L.Plaquette → List L.Vertex

/-- Euclidean time coordinate of a lattice vertex. -/
def FiniteFourDimensionalWilsonGeometry.timeCoordinate
    {L : FiniteLatticeWilsonSystem}
    (G : FiniteFourDimensionalWilsonGeometry L)
    (v : L.Vertex) : ℤ :=
  G.coordinate v 0

/-- A plaquette lies on the positive side when all of its vertices have
strictly positive time, on the negative side when all have strictly negative
time, and crosses the reflection plane otherwise. -/
def FiniteFourDimensionalWilsonGeometry.plaquetteSide
    {L : FiniteLatticeWilsonSystem}
    (G : FiniteFourDimensionalWilsonGeometry L)
    (p : L.Plaquette) : ReflectionPlaquetteSide := by
  classical
  exact
    if ∀ v ∈ G.plaquetteVertices p, 0 < G.timeCoordinate v then
      .positive
    else if ∀ v ∈ G.plaquetteVertices p, G.timeCoordinate v < 0 then
      .negative
    else
      .crossing

/-- Strictly positive vertex support is classified as a positive plaquette. -/
theorem FiniteFourDimensionalWilsonGeometry.plaquetteSide_eq_positive
    {L : FiniteLatticeWilsonSystem}
    (G : FiniteFourDimensionalWilsonGeometry L)
    (p : L.Plaquette)
    (h : ∀ v ∈ G.plaquetteVertices p, 0 < G.timeCoordinate v) :
    G.plaquetteSide p = .positive := by
  classical
  unfold FiniteFourDimensionalWilsonGeometry.plaquetteSide
  rw [if_pos h]

/-- Strictly negative support, after excluding the positive case, is classified
as a negative plaquette. -/
theorem FiniteFourDimensionalWilsonGeometry.plaquetteSide_eq_negative
    {L : FiniteLatticeWilsonSystem}
    (G : FiniteFourDimensionalWilsonGeometry L)
    (p : L.Plaquette)
    (hPositive : ¬ ∀ v ∈ G.plaquetteVertices p, 0 < G.timeCoordinate v)
    (hNegative : ∀ v ∈ G.plaquetteVertices p, G.timeCoordinate v < 0) :
    G.plaquetteSide p = .negative := by
  classical
  unfold FiniteFourDimensionalWilsonGeometry.plaquetteSide
  rw [if_neg hPositive, if_pos hNegative]

/-- Any support that is neither wholly positive nor wholly negative crosses the
reflection plane. -/
theorem FiniteFourDimensionalWilsonGeometry.plaquetteSide_eq_crossing
    {L : FiniteLatticeWilsonSystem}
    (G : FiniteFourDimensionalWilsonGeometry L)
    (p : L.Plaquette)
    (hPositive : ¬ ∀ v ∈ G.plaquetteVertices p, 0 < G.timeCoordinate v)
    (hNegative : ¬ ∀ v ∈ G.plaquetteVertices p, G.timeCoordinate v < 0) :
    G.plaquetteSide p = .crossing := by
  classical
  unfold FiniteFourDimensionalWilsonGeometry.plaquetteSide
  rw [if_neg hPositive, if_neg hNegative]

/-- Four-dimensional time-reflection data for a finite `Z₂` Wilson system.

The side classifier is no longer supplied independently: it is generated from
integer time coordinates of the vertices supporting each plaquette.  The three
energy identities are the remaining model-specific local calculations. -/
structure Z2FiniteFourDimensionalWilsonTimeReflectionGeometry
    (L : FiniteLatticeWilsonSystem) where
  geometry : FiniteFourDimensionalWilsonGeometry L
  PositiveConfiguration : Type
  [positiveFintype : Fintype PositiveConfiguration]
  [positiveInhabited : Inhabited PositiveConfiguration]
  assemble : PositiveConfiguration → PositiveConfiguration → L.Configuration
  reflection : L.Configuration → L.Configuration
  reflection_involutive : Function.Involutive reflection
  reflection_assemble :
    ∀ x y, reflection (assemble x y) = assemble y x
  energyIdentity : ℝ
  energyNontrivial : ℝ
  energy_order : energyIdentity ≤ energyNontrivial
  crossingVariables : List (PositiveConfiguration → Z2Gauge)
  positiveEnergyTerms : PositiveConfiguration → List ℝ
  positive_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        geometry.plaquetteSide p = .positive).map fun p =>
          L.plaquetteEnergy (L.plaquetteHolonomy (assemble x y) p)) =
        positiveEnergyTerms x
  crossing_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        geometry.plaquetteSide p = .crossing).map fun p =>
          L.plaquetteEnergy (L.plaquetteHolonomy (assemble x y) p)) =
        z2CrossingEnergyTerms crossingVariables
          energyIdentity energyNontrivial x y
  negative_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        geometry.plaquetteSide p = .negative).map fun p =>
          L.plaquetteEnergy (L.plaquetteHolonomy (assemble x y) p)) =
        positiveEnergyTerms y

attribute [instance]
  Z2FiniteFourDimensionalWilsonTimeReflectionGeometry.positiveFintype
  Z2FiniteFourDimensionalWilsonTimeReflectionGeometry.positiveInhabited

/-- Four-dimensional time geometry automatically supplies the abstract
plaquette-side classifier. -/
def Z2FiniteFourDimensionalWilsonTimeReflectionGeometry.toSideClassification
    {L : FiniteLatticeWilsonSystem}
    (G : Z2FiniteFourDimensionalWilsonTimeReflectionGeometry L) :
    Z2FiniteLatticeWilsonPlaquetteSideClassification L :=
  { PositiveConfiguration := G.PositiveConfiguration
    assemble := G.assemble
    reflection := G.reflection
    reflection_involutive := G.reflection_involutive
    reflection_assemble := G.reflection_assemble
    energyIdentity := G.energyIdentity
    energyNontrivial := G.energyNontrivial
    energy_order := G.energy_order
    crossingVariables := G.crossingVariables
    side := G.geometry.plaquetteSide
    positiveEnergyTerms := G.positiveEnergyTerms
    positive_terms_eq := G.positive_terms_eq
    crossing_terms_eq := G.crossing_terms_eq
    negative_terms_eq := G.negative_terms_eq }

/-- Four-dimensional time-reflection geometry yields finite-volume OS
reflection positivity. -/
theorem z2_finite_fourDimensional_wilson_reflectionPositive
    {L : FiniteLatticeWilsonSystem}
    (G : Z2FiniteFourDimensionalWilsonTimeReflectionGeometry L) :
    FiniteLatticeWilsonOSReflectionPositive
      (G.toSideClassification.toIndexPartition.toTermPartition
        .toActionDecomposition.toFactorization.toReflectionCertificate) :=
  z2_finite_lattice_wilson_reflectionPositive_of_sideClassification
    G.toSideClassification

/-- Audit-visible finite-volume OS certificate generated from four-dimensional
integer time geometry. -/
def z2FiniteFourDimensionalWilsonOSCertificate
    (L : FiniteLatticeWilsonSystem)
    (G : Z2FiniteFourDimensionalWilsonTimeReflectionGeometry L) :
    FiniteWilsonOSReflectionPositivityCertificate L :=
  z2FiniteLatticeWilsonOSCertificateOfSideClassification
    L G.toSideClassification

end

end MathlibAnalytic
end MGAP4D
