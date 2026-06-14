import MGAP4D.MathlibAnalytic.Z2FiniteFourDimensionalTorusLattice
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPlaquetteSupportCompatibility
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The concrete `Z₂` Wilson system on the even four-torus with side parameter
`2 * H + 1`, hence coordinate modulus `2 * H + 2`. -/
def finiteEvenFourTorusZ2WilsonSystem
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergyIdentity : 0 ≤ energyIdentity)
    (hEnergyNontrivial : 0 ≤ energyNontrivial) :
    FiniteLatticeWilsonSystem :=
  finiteFourTorusZ2WilsonSystem
    (2 * H + 1) β energyIdentity energyNontrivial
    hβ hEnergyIdentity hEnergyNontrivial

/-- The positive-half configuration carrier is a finite function space on the
finite even-torus edge set.  This named instance prevents dependent record
elaboration from having to unfold `PositiveConfiguration` on its own. -/
instance finiteEvenFourTorusPositiveConfigurationFintype
    (H : ℕ) :
    Fintype ((finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration) :=
  inferInstanceAs (Fintype (FiniteEvenFourTorusEdge H → Z2Gauge))

/-- The identity edge assignment inhabits the positive-half configuration
carrier. -/
instance finiteEvenFourTorusPositiveConfigurationInhabited
    (H : ℕ) :
    Inhabited ((finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration) :=
  ⟨fun _ => 1⟩

/-- The remaining local analytic input for the concrete even-torus geometric
classifier.  All carrier, involution, support, crossing-sector, and assembly
data are already fixed by the preceding geometric construction; only the
three Wilson energy identities remain to be supplied. -/
structure FiniteEvenFourTorusWilsonGeometricEnergyData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergyIdentity : 0 ≤ energyIdentity)
    (hEnergyNontrivial : 0 ≤ energyNontrivial) where
  energy_order : energyIdentity ≤ energyNontrivial
  crossingVariables :
    List ((finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration → Z2Gauge)
  positiveEnergyTerms :
    (finiteEvenFourTorusEdgeOrbitPartition H).PositiveConfiguration → List ℝ
  positive_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        (finiteEvenFourTorusConcreteGeometricPlaquetteSidePartition H).side p =
          .positive).map fun p =>
            (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
              hβ hEnergyIdentity hEnergyNontrivial).plaquetteEnergy
              ((finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
                hβ hEnergyIdentity hEnergyNontrivial).plaquetteHolonomy
                (finiteEvenFourTorusAssemble H x y) p)) =
        positiveEnergyTerms x
  crossing_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        (finiteEvenFourTorusConcreteGeometricPlaquetteSidePartition H).side p =
          .crossing).map fun p =>
            (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
              hβ hEnergyIdentity hEnergyNontrivial).plaquetteEnergy
              ((finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
                hβ hEnergyIdentity hEnergyNontrivial).plaquetteHolonomy
                (finiteEvenFourTorusAssemble H x y) p)) =
        z2CrossingEnergyTerms crossingVariables
          energyIdentity energyNontrivial x y
  negative_terms_eq :
    ∀ x y,
      ((Finset.univ.toList.filter fun p =>
        (finiteEvenFourTorusConcreteGeometricPlaquetteSidePartition H).side p =
          .negative).map fun p =>
            (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
              hβ hEnergyIdentity hEnergyNontrivial).plaquetteEnergy
              ((finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
                hβ hEnergyIdentity hEnergyNontrivial).plaquetteHolonomy
                (finiteEvenFourTorusAssemble H x y) p)) =
        positiveEnergyTerms y

/-- Package the concrete even-torus geometry and local energy identities into
the generic geometric Wilson side-classification interface. -/
def finiteEvenFourTorusWilsonGeometricPlaquetteSideClassification
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergyIdentity : 0 ≤ energyIdentity)
    (hEnergyNontrivial : 0 ≤ energyNontrivial)
    (D : FiniteEvenFourTorusWilsonGeometricEnergyData H β energyIdentity
      energyNontrivial hβ hEnergyIdentity hEnergyNontrivial) :
    Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification
      (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
        hβ hEnergyIdentity hEnergyNontrivial) :=
  { configurationEquiv := Equiv.refl _
    edgeOrbit := finiteEvenFourTorusEdgeOrbitPartition H
    positiveFintype := finiteEvenFourTorusPositiveConfigurationFintype H
    positiveInhabited := finiteEvenFourTorusPositiveConfigurationInhabited H
    plaquetteGeometry :=
      finiteEvenFourTorusConcreteGeometricPlaquetteSidePartition H
    energyIdentity := energyIdentity
    energyNontrivial := energyNontrivial
    energy_order := D.energy_order
    crossingVariables := D.crossingVariables
    positiveEnergyTerms := D.positiveEnergyTerms
    positive_terms_eq := D.positive_terms_eq
    crossing_terms_eq := D.crossing_terms_eq
    negative_terms_eq := D.negative_terms_eq }

/-- Once the three concrete local energy identities are discharged, the even
four-torus Wilson model satisfies finite-volume OS reflection positivity. -/
theorem finiteEvenFourTorusZ2Wilson_reflectionPositive_of_geometricEnergyData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergyIdentity : 0 ≤ energyIdentity)
    (hEnergyNontrivial : 0 ≤ energyNontrivial)
    (D : FiniteEvenFourTorusWilsonGeometricEnergyData H β energyIdentity
      energyNontrivial hβ hEnergyIdentity hEnergyNontrivial) :
    FiniteLatticeWilsonOSReflectionPositive
      (Z2FiniteLatticeWilsonReflectionFactorization.toReflectionCertificate
        (Z2FiniteLatticeWilsonActionReflectionDecomposition.toFactorization
          (Z2FiniteLatticeWilsonPlaquetteTermPartition.toActionDecomposition
            (Z2FiniteLatticeWilsonPlaquetteIndexPartition.toTermPartition
              (Z2FiniteLatticeWilsonPlaquetteSideClassification.toIndexPartition
                (finiteEvenFourTorusWilsonGeometricPlaquetteSideClassification
                  H β energyIdentity energyNontrivial hβ hEnergyIdentity
                    hEnergyNontrivial D).toSideClassification))))) :=
  z2_finite_lattice_wilson_reflectionPositive_of_geometricPlaquetteSideClassification
    (finiteEvenFourTorusWilsonGeometricPlaquetteSideClassification
      H β energyIdentity energyNontrivial hβ hEnergyIdentity
        hEnergyNontrivial D)

/-- Audit-visible reflection-positivity certificate for the concrete even
four-torus Wilson system, conditional only on the explicit local energy data. -/
def finiteEvenFourTorusZ2WilsonOSCertificateOfGeometricEnergyData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergyIdentity : 0 ≤ energyIdentity)
    (hEnergyNontrivial : 0 ≤ energyNontrivial)
    (D : FiniteEvenFourTorusWilsonGeometricEnergyData H β energyIdentity
      energyNontrivial hβ hEnergyIdentity hEnergyNontrivial) :
    FiniteWilsonOSReflectionPositivityCertificate
      (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
        hβ hEnergyIdentity hEnergyNontrivial) :=
  z2FiniteLatticeWilsonOSCertificateOfGeometricPlaquetteSideClassification
    (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
      hβ hEnergyIdentity hEnergyNontrivial)
    (finiteEvenFourTorusWilsonGeometricPlaquetteSideClassification
      H β energyIdentity energyNontrivial hβ hEnergyIdentity
        hEnergyNontrivial D)

end

end MathlibAnalytic
end MGAP4D
