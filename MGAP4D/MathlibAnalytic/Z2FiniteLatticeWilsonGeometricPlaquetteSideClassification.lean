import MGAP4D.MathlibAnalytic.Z2FiniteInvolutivePlaquetteGeometricSidePartition
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonPlaquetteSideClassification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Wilson reflection data whose plaquette classifier retains a prescribed
reflection-invariant geometric crossing sector.  The positive and negative
plaquette lists are generated from the geometric side classifier, while the
three local energy identities remain the analytic input needed by the finite
OS theorem. -/
structure Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification
    (L : FiniteLatticeWilsonSystem) where
  configurationEquiv : L.Configuration ≃ (L.Edge → Z2Gauge)
  edgeOrbit : FiniteInvolutiveEdgeOrbitPartition L.Edge
  [positiveFintype : Fintype edgeOrbit.PositiveConfiguration]
  [positiveInhabited : Inhabited edgeOrbit.PositiveConfiguration]
  plaquetteGeometry :
    FiniteInvolutivePlaquetteGeometricSidePartition L.Plaquette
  energyIdentity : ℝ
  energyNontrivial : ℝ
  energy_order : energyIdentity ≤ energyNontrivial
  crossingVariables :
    List (edgeOrbit.PositiveConfiguration → Z2Gauge)
  positiveEnergyTerms :
    edgeOrbit.PositiveConfiguration → List ℝ
  positive_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        plaquetteGeometry.side p = .positive).map fun p =>
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (configurationEquiv.symm (edgeOrbit.assemble x y)) p)) =
        positiveEnergyTerms x
  crossing_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        plaquetteGeometry.side p = .crossing).map fun p =>
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (configurationEquiv.symm (edgeOrbit.assemble x y)) p)) =
        z2CrossingEnergyTerms crossingVariables
          energyIdentity energyNontrivial x y
  negative_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        plaquetteGeometry.side p = .negative).map fun p =>
          L.plaquetteEnergy
            (L.plaquetteHolonomy
              (configurationEquiv.symm (edgeOrbit.assemble x y)) p)) =
        positiveEnergyTerms y

attribute [instance]
  Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.positiveFintype
  Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.positiveInhabited

/-- Assemble two positive-half edge configurations into the Wilson
configuration carrier. -/
def Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.assemble
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification L)
    (x y : C.edgeOrbit.PositiveConfiguration) : L.Configuration :=
  C.configurationEquiv.symm (C.edgeOrbit.assemble x y)

/-- Transport the edge-orbit reflection to the Wilson configuration carrier. -/
def Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.reflection
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification L)
    (A : L.Configuration) : L.Configuration :=
  C.configurationEquiv.symm
    (C.edgeOrbit.configurationReflection (C.configurationEquiv A))

/-- The transported configuration reflection is involutive. -/
theorem Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.reflection_involutive
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification L) :
    Function.Involutive C.reflection := by
  intro A
  apply C.configurationEquiv.injective
  simpa only
      [Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.reflection,
        Equiv.apply_symm_apply] using
    C.edgeOrbit.configurationReflection_involutive
      (C.configurationEquiv A)

/-- Reflection exchanges the two assembled positive-half inputs. -/
theorem Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.reflection_assemble
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification L)
    (x y : C.edgeOrbit.PositiveConfiguration) :
    C.reflection (C.assemble x y) = C.assemble y x := by
  apply C.configurationEquiv.injective
  simpa
      [Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.reflection,
        Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.assemble] using
    C.edgeOrbit.reflection_assemble x y

/-- Forget only the geometric construction mechanism and expose the existing
side-classification interface consumed by the finite-volume OS theorem.  The
actual side function is unchanged. -/
def Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.toSideClassification
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification L) :
    Z2FiniteLatticeWilsonPlaquetteSideClassification L :=
  { PositiveConfiguration := C.edgeOrbit.PositiveConfiguration
    assemble := C.assemble
    reflection := C.reflection
    reflection_involutive := C.reflection_involutive
    reflection_assemble := C.reflection_assemble
    energyIdentity := C.energyIdentity
    energyNontrivial := C.energyNontrivial
    energy_order := C.energy_order
    crossingVariables := C.crossingVariables
    side := C.plaquetteGeometry.side
    positiveEnergyTerms := C.positiveEnergyTerms
    positive_terms_eq := C.positive_terms_eq
    crossing_terms_eq := C.crossing_terms_eq
    negative_terms_eq := C.negative_terms_eq }

/-- The geometric plaquette classifier inherits the reflection side-exchange
law used to organize the Wilson action. -/
@[simp]
theorem Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification.plaquette_side_reflection
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification L)
    (p : L.Plaquette) :
    C.plaquetteGeometry.side (C.plaquetteGeometry.reflection p) =
      match C.plaquetteGeometry.side p with
      | .positive => .negative
      | .crossing => .crossing
      | .negative => .positive := by
  exact C.plaquetteGeometry.side_reflection p

/-- Geometric plaquette-side data together with the three local energy
identities imply the complete finite-volume Wilson OS reflection-positivity
theorem. -/
theorem z2_finite_lattice_wilson_reflectionPositive_of_geometricPlaquetteSideClassification
    {L : FiniteLatticeWilsonSystem}
    (C : Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification L) :
    FiniteLatticeWilsonOSReflectionPositive
      C.toSideClassification.toIndexPartition.toTermPartition
        .toActionDecomposition.toFactorization.toReflectionCertificate :=
  z2_finite_lattice_wilson_reflectionPositive_of_sideClassification
    C.toSideClassification

/-- Audit-visible finite-volume OS certificate generated from the geometric
plaquette classifier. -/
def z2FiniteLatticeWilsonOSCertificateOfGeometricPlaquetteSideClassification
    (L : FiniteLatticeWilsonSystem)
    (C : Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification L) :
    FiniteWilsonOSReflectionPositivityCertificate L :=
  z2FiniteLatticeWilsonOSCertificateOfSideClassification
    L C.toSideClassification

end

end MathlibAnalytic
end MGAP4D
