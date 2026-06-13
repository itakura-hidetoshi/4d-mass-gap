import MGAP4D.MathlibAnalytic.Z2FiniteInvolutiveEdgeOrbitAssembly
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonPlaquetteIndexPartition
import Mathlib.Data.Fintype.EquivFin

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Reflection-orbit data that connects a finite `Z₂` edge assembly to an
explicit plaquette-index partition.  The remaining fields are exactly the
local geometric/energy identifications needed to enter the existing OS proof
chain. -/
structure Z2FiniteLatticeWilsonPlaquetteOrbitBridge
    (L : FiniteLatticeWilsonSystem) where
  configurationEquiv : L.Configuration ≃ (L.Edge → Z2Gauge)
  edgeOrbit : FiniteInvolutiveEdgeOrbitPartition L.Edge
  plaquetteReflection : L.Plaquette → L.Plaquette
  plaquetteReflection_involutive :
    Function.Involutive plaquetteReflection
  plaquetteRank : L.Plaquette ≃ Fin (Fintype.card L.Plaquette)
  energyIdentity : ℝ
  energyNontrivial : ℝ
  energy_order : energyIdentity ≤ energyNontrivial
  positivePlaquettes : List L.Plaquette
  crossingPlaquettes : List L.Plaquette
  negativePlaquettes : List L.Plaquette
  plaquette_index_perm :
    List.Perm
      (Finset.univ.toList : List L.Plaquette)
      (positivePlaquettes ++ crossingPlaquettes ++ negativePlaquettes)
  crossingVariables :
    List (edgeOrbit.PositiveConfiguration → Z2Gauge)
  positiveEnergyTerms :
    edgeOrbit.PositiveConfiguration → List ℝ
  positive_terms_eq :
    ∀ x y,
      (positivePlaquettes.map fun p =>
        L.plaquetteEnergy
          (L.plaquetteHolonomy
            (configurationEquiv.symm (edgeOrbit.assemble x y)) p)) =
        positiveEnergyTerms x
  crossing_terms_eq :
    ∀ x y,
      (crossingPlaquettes.map fun p =>
        L.plaquetteEnergy
          (L.plaquetteHolonomy
            (configurationEquiv.symm (edgeOrbit.assemble x y)) p)) =
        z2CrossingEnergyTerms crossingVariables
          energyIdentity energyNontrivial x y
  negative_terms_eq :
    ∀ x y,
      (negativePlaquettes.map fun p =>
        L.plaquetteEnergy
          (L.plaquetteHolonomy
            (configurationEquiv.symm (edgeOrbit.assemble x y)) p)) =
        positiveEnergyTerms y

/-- Full finite-lattice configuration assembled from two positive-half inputs. -/
def Z2FiniteLatticeWilsonPlaquetteOrbitBridge.assemble
    {L : FiniteLatticeWilsonSystem}
    (B : Z2FiniteLatticeWilsonPlaquetteOrbitBridge L)
    (x y : B.edgeOrbit.PositiveConfiguration) : L.Configuration :=
  B.configurationEquiv.symm (B.edgeOrbit.assemble x y)

/-- Configuration reflection transported through the `Z₂` configuration
equivalence. -/
def Z2FiniteLatticeWilsonPlaquetteOrbitBridge.reflection
    {L : FiniteLatticeWilsonSystem}
    (B : Z2FiniteLatticeWilsonPlaquetteOrbitBridge L)
    (A : L.Configuration) : L.Configuration :=
  B.configurationEquiv.symm
    (B.edgeOrbit.configurationReflection (B.configurationEquiv A))

/-- The transported configuration reflection is involutive. -/
theorem Z2FiniteLatticeWilsonPlaquetteOrbitBridge.reflection_involutive
    {L : FiniteLatticeWilsonSystem}
    (B : Z2FiniteLatticeWilsonPlaquetteOrbitBridge L) :
    Function.Involutive B.reflection := by
  intro A
  apply B.configurationEquiv.injective
  simp [Z2FiniteLatticeWilsonPlaquetteOrbitBridge.reflection,
    B.edgeOrbit.configurationReflection_involutive]

/-- Reflection exchanges the two assembled positive-half inputs. -/
theorem Z2FiniteLatticeWilsonPlaquetteOrbitBridge.reflection_assemble
    {L : FiniteLatticeWilsonSystem}
    (B : Z2FiniteLatticeWilsonPlaquetteOrbitBridge L)
    (x y : B.edgeOrbit.PositiveConfiguration) :
    B.reflection (B.assemble x y) = B.assemble y x := by
  apply B.configurationEquiv.injective
  simpa [Z2FiniteLatticeWilsonPlaquetteOrbitBridge.reflection,
    Z2FiniteLatticeWilsonPlaquetteOrbitBridge.assemble] using
      B.edgeOrbit.reflection_assemble x y

/-- Convert orbit-level geometry and local energy identities into the existing
plaquette-index partition consumed by the finite-volume OS theorem chain. -/
def Z2FiniteLatticeWilsonPlaquetteOrbitBridge.toIndexPartition
    {L : FiniteLatticeWilsonSystem}
    (B : Z2FiniteLatticeWilsonPlaquetteOrbitBridge L) :
    Z2FiniteLatticeWilsonPlaquetteIndexPartition L :=
  { PositiveConfiguration := B.edgeOrbit.PositiveConfiguration
    assemble := B.assemble
    reflection := B.reflection
    reflection_involutive := B.reflection_involutive
    reflection_assemble := B.reflection_assemble
    energyIdentity := B.energyIdentity
    energyNontrivial := B.energyNontrivial
    energy_order := B.energy_order
    crossingVariables := B.crossingVariables
    positivePlaquettes := B.positivePlaquettes
    crossingPlaquettes := B.crossingPlaquettes
    negativePlaquettes := B.negativePlaquettes
    plaquette_index_perm := B.plaquette_index_perm
    positiveEnergyTerms := B.positiveEnergyTerms
    positive_terms_eq := by
      intro x y
      exact B.positive_terms_eq x y
    crossing_terms_eq := by
      intro x y
      exact B.crossing_terms_eq x y
    negative_terms_eq := by
      intro x y
      exact B.negative_terms_eq x y }

/-- Orbit-level reflection geometry plus the three local energy identities
already implies finite-volume OS reflection positivity. -/
theorem z2_finite_lattice_wilson_reflectionPositive_of_plaquetteOrbitBridge
    {L : FiniteLatticeWilsonSystem}
    (B : Z2FiniteLatticeWilsonPlaquetteOrbitBridge L) :
    FiniteLatticeWilsonOSReflectionPositive
      B.toIndexPartition.toTermPartition.toActionDecomposition.toFactorization.toReflectionCertificate :=
  z2_finite_lattice_wilson_reflectionPositive_of_plaquetteIndexPartition
    B.toIndexPartition

/-- Audit-visible finite-volume OS certificate generated from reflection-orbit
geometry. -/
def z2FiniteLatticeWilsonOSCertificateOfPlaquetteOrbitBridge
    (L : FiniteLatticeWilsonSystem)
    (B : Z2FiniteLatticeWilsonPlaquetteOrbitBridge L) :
    FiniteWilsonOSReflectionPositivityCertificate L :=
  z2FiniteLatticeWilsonOSCertificateOfPlaquetteIndexPartition
    L B.toIndexPartition

end

end MathlibAnalytic
end MGAP4D
