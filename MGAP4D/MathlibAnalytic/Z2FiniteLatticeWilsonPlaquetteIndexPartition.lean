import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonPlaquetteTermPartition

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A combinatorial reflection partition of the plaquette index set.

The full finite plaquette enumeration is partitioned, up to permutation, into
positive-side, crossing-plane, and negative-side plaquettes.  The three local
energy-identification fields are the only geometry-dependent obligations. -/
structure Z2FiniteLatticeWilsonPlaquetteIndexPartition
    (L : FiniteLatticeWilsonSystem) where
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
  positivePlaquettes : List L.Plaquette
  crossingPlaquettes : List L.Plaquette
  negativePlaquettes : List L.Plaquette
  plaquette_index_perm :
    List.Perm
      (Finset.univ.toList : List L.Plaquette)
      (positivePlaquettes ++ crossingPlaquettes ++ negativePlaquettes)
  positiveEnergyTerms : PositiveConfiguration → List ℝ
  positive_terms_eq :
    ∀ x y,
      (positivePlaquettes.map fun p =>
        L.plaquetteEnergy (L.plaquetteHolonomy (assemble x y) p)) =
        positiveEnergyTerms x
  crossing_terms_eq :
    ∀ x y,
      (crossingPlaquettes.map fun p =>
        L.plaquetteEnergy (L.plaquetteHolonomy (assemble x y) p)) =
        z2CrossingEnergyTerms crossingVariables
          energyIdentity energyNontrivial x y
  negative_terms_eq :
    ∀ x y,
      (negativePlaquettes.map fun p =>
        L.plaquetteEnergy (L.plaquetteHolonomy (assemble x y) p)) =
        positiveEnergyTerms y

attribute [instance]
  Z2FiniteLatticeWilsonPlaquetteIndexPartition.positiveFintype
  Z2FiniteLatticeWilsonPlaquetteIndexPartition.positiveInhabited

/-- Mapping the plaquette-index permutation through the local energy function
produces the complete plaquette-term partition required by the analytic OS
bridge. -/
def Z2FiniteLatticeWilsonPlaquetteIndexPartition.toTermPartition
    {L : FiniteLatticeWilsonSystem}
    (P : Z2FiniteLatticeWilsonPlaquetteIndexPartition L) :
    Z2FiniteLatticeWilsonPlaquetteTermPartition L :=
  { PositiveConfiguration := P.PositiveConfiguration
    assemble := P.assemble
    reflection := P.reflection
    reflection_involutive := P.reflection_involutive
    reflection_assemble := P.reflection_assemble
    energyIdentity := P.energyIdentity
    energyNontrivial := P.energyNontrivial
    energy_order := P.energy_order
    crossingVariables := P.crossingVariables
    positiveEnergyTerms := P.positiveEnergyTerms
    plaquette_terms_perm := by
      intro x y
      have h := P.plaquette_index_perm.map
        (fun p => L.plaquetteEnergy
          (L.plaquetteHolonomy (P.assemble x y) p))
      rw [List.map_append, List.map_append,
        P.positive_terms_eq x y,
        P.crossing_terms_eq x y,
        P.negative_terms_eq x y] at h
      simpa [finiteWilsonPlaquetteEnergyTerms] using h }

/-- A combinatorial plaquette-index partition yields finite-volume OS
reflection positivity. -/
theorem z2_finite_lattice_wilson_reflectionPositive_of_plaquetteIndexPartition
    {L : FiniteLatticeWilsonSystem}
    (P : Z2FiniteLatticeWilsonPlaquetteIndexPartition L) :
    FiniteLatticeWilsonOSReflectionPositive
      P.toTermPartition.toActionDecomposition.toFactorization.toReflectionCertificate :=
  z2_finite_lattice_wilson_reflectionPositive_of_plaquetteTermPartition
    P.toTermPartition

/-- Audit-visible finite-volume OS certificate generated from the explicit
plaquette-index partition. -/
def z2FiniteLatticeWilsonOSCertificateOfPlaquetteIndexPartition
    (L : FiniteLatticeWilsonSystem)
    (P : Z2FiniteLatticeWilsonPlaquetteIndexPartition L) :
    FiniteWilsonOSReflectionPositivityCertificate L :=
  z2FiniteLatticeWilsonOSCertificateOfPlaquetteTermPartition
    L P.toTermPartition

end

end MathlibAnalytic
end MGAP4D
