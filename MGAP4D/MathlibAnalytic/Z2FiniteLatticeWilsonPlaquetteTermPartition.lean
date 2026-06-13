import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonActionReflectionDecomposition

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite list of plaquette-energy terms whose sum is the Wilson action. -/
def finiteWilsonPlaquetteEnergyTerms
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) : List ℝ :=
  (Finset.univ.toList.map fun p : L.Plaquette =>
    L.plaquetteEnergy (L.plaquetteHolonomy A p))

/-- Summing the enumerated plaquette-energy terms recovers the Wilson action. -/
theorem finiteWilsonPlaquetteEnergyTerms_sum
    (L : FiniteLatticeWilsonSystem)
    (A : L.Configuration) :
    (finiteWilsonPlaquetteEnergyTerms L A).sum = L.wilsonAction A := by
  classical
  simp [finiteWilsonPlaquetteEnergyTerms,
    FiniteLatticeWilsonSystem.wilsonAction]

/-- The list of local crossing-plane energies determined by the boundary
variables on the positive half lattice. -/
def z2CrossingEnergyTerms
    {α : Type} [Fintype α]
    (crossingVariables : List (α → Z2Gauge))
    (energyIdentity energyNontrivial : ℝ)
    (x y : α) : List ℝ :=
  crossingVariables.map fun q =>
    if (q x)⁻¹ * q y = 1 then energyIdentity else energyNontrivial

@[simp]
theorem z2CrossingEnergyTerms_sum
    {α : Type} [Fintype α]
    (crossingVariables : List (α → Z2Gauge))
    (energyIdentity energyNontrivial : ℝ)
    (x y : α) :
    (z2CrossingEnergyTerms crossingVariables
      energyIdentity energyNontrivial x y).sum =
      z2CrossingAction crossingVariables
        energyIdentity energyNontrivial x y :=
  rfl

/-- Plaquette-level reflection partition certificate.

Rather than postulating an equality between two real-valued actions, this
certificate states that the complete finite list of plaquette-energy terms is a
permutation of three explicit lists: positive-half terms, crossing terms, and
the reflected negative-half terms.  Hence every plaquette is accounted for
exactly once. -/
structure Z2FiniteLatticeWilsonPlaquetteTermPartition
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
  positiveEnergyTerms : PositiveConfiguration → List ℝ
  plaquette_terms_perm :
    ∀ x y,
      finiteWilsonPlaquetteEnergyTerms L (assemble x y) ~
        positiveEnergyTerms x ++
          z2CrossingEnergyTerms crossingVariables
            energyIdentity energyNontrivial x y ++
          positiveEnergyTerms y

attribute [instance]
  Z2FiniteLatticeWilsonPlaquetteTermPartition.positiveFintype
  Z2FiniteLatticeWilsonPlaquetteTermPartition.positiveInhabited

/-- The same-side Wilson action is the sum of the positive-half plaquette
energy terms. -/
def Z2FiniteLatticeWilsonPlaquetteTermPartition.halfAction
    {L : FiniteLatticeWilsonSystem}
    (P : Z2FiniteLatticeWilsonPlaquetteTermPartition L)
    (x : P.PositiveConfiguration) : ℝ :=
  (P.positiveEnergyTerms x).sum

/-- A term-level plaquette partition automatically yields the additive Wilson
reflection decomposition. -/
def Z2FiniteLatticeWilsonPlaquetteTermPartition.toActionDecomposition
    {L : FiniteLatticeWilsonSystem}
    (P : Z2FiniteLatticeWilsonPlaquetteTermPartition L) :
    Z2FiniteLatticeWilsonActionReflectionDecomposition L :=
  { PositiveConfiguration := P.PositiveConfiguration
    assemble := P.assemble
    reflection := P.reflection
    reflection_involutive := P.reflection_involutive
    reflection_assemble := P.reflection_assemble
    energyIdentity := P.energyIdentity
    energyNontrivial := P.energyNontrivial
    energy_order := P.energy_order
    crossingVariables := P.crossingVariables
    halfAction := P.halfAction
    wilsonAction_decomposition := by
      intro x y
      have hsum := (P.plaquette_terms_perm x y).sum_eq
      rw [finiteWilsonPlaquetteEnergyTerms_sum] at hsum
      simpa [Z2FiniteLatticeWilsonPlaquetteTermPartition.halfAction,
        List.sum_append] using hsum }

/-- A plaquette-term partition produces the full finite-volume OS reflection
positivity theorem. -/
theorem z2_finite_lattice_wilson_reflectionPositive_of_plaquetteTermPartition
    {L : FiniteLatticeWilsonSystem}
    (P : Z2FiniteLatticeWilsonPlaquetteTermPartition L) :
    FiniteLatticeWilsonOSReflectionPositive
      P.toActionDecomposition.toFactorization.toReflectionCertificate :=
  z2_finite_lattice_wilson_reflectionPositive_of_actionDecomposition
    P.toActionDecomposition

/-- Audit-visible OS certificate generated from the plaquette-level term
partition. -/
def z2FiniteLatticeWilsonOSCertificateOfPlaquetteTermPartition
    (L : FiniteLatticeWilsonSystem)
    (P : Z2FiniteLatticeWilsonPlaquetteTermPartition L) :
    FiniteWilsonOSReflectionPositivityCertificate L :=
  z2FiniteLatticeWilsonOSCertificateOfActionDecomposition
    L P.toActionDecomposition

end

end MathlibAnalytic
end MGAP4D
