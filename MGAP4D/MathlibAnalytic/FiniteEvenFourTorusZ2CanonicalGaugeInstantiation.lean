import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsExplicitCanonicalGaugeCoerciveSpine
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusWilsonGeometricClassification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Instantiate the explicit canonical gauge construction on a concrete family of
finite even four-dimensional `Z₂` tori.
-/

/-- The reflection certificate generated from the concrete even-four-torus
geometric energy classification. -/
noncomputable def finiteEvenFourTorusZ2WilsonReflectionCertificate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergyIdentity : 0 ≤ energyIdentity)
    (hEnergyNontrivial : 0 ≤ energyNontrivial)
    (D : FiniteEvenFourTorusWilsonGeometricEnergyData H β energyIdentity
      energyNontrivial hβ hEnergyIdentity hEnergyNontrivial) :
    FiniteLatticeWilsonOSReflectionCertificate
      (finiteEvenFourTorusZ2WilsonSystem H β energyIdentity energyNontrivial
        hβ hEnergyIdentity hEnergyNontrivial) :=
  Z2FiniteLatticeWilsonReflectionFactorization.toReflectionCertificate
    (Z2FiniteLatticeWilsonActionReflectionDecomposition.toFactorization
      (Z2FiniteLatticeWilsonPlaquetteTermPartition.toActionDecomposition
        (Z2FiniteLatticeWilsonPlaquetteIndexPartition.toTermPartition
          (Z2FiniteLatticeWilsonPlaquetteSideClassification.toIndexPartition
            (finiteEvenFourTorusWilsonGeometricPlaquetteSideClassification
              H β energyIdentity energyNontrivial hβ hEnergyIdentity
                hEnergyNontrivial D).toSideClassification))))

section ConcreteFamily

variable
  (H : ℕ → ℕ)
  (β energyIdentity energyNontrivial latticeSpacing volumeScale : ℕ → ℝ)
  (hβ : ∀ n, 0 ≤ β n)
  (hEnergyIdentity : ∀ n, 0 ≤ energyIdentity n)
  (hEnergyNontrivial : ∀ n, 0 ≤ energyNontrivial n)
  (geometricEnergy : ∀ n,
    FiniteEvenFourTorusWilsonGeometricEnergyData
      (H n) (β n) (energyIdentity n) (energyNontrivial n)
      (hβ n) (hEnergyIdentity n) (hEnergyNontrivial n))
  (finiteVolumeEuclideanCovariant : Prop)
  (finiteVolumeEuclideanCovariant_proof : finiteVolumeEuclideanCovariant)

/-- A concrete automatic Wilson approximation family whose scale `n` is the
`Z₂` Wilson model on the even four-torus of half-height `H n`.

The OS reflection certificate at every scale is generated from the geometric
energy classification rather than supplied as a separate abstract certificate. -/
noncomputable def finiteEvenFourTorusZ2AutomaticApproximationFamily :
    FiniteWilsonOSAutomaticApproximationFamily where
  index := ℕ
  system := fun n =>
    finiteEvenFourTorusZ2WilsonSystem
      (H n) (β n) (energyIdentity n) (energyNontrivial n)
      (hβ n) (hEnergyIdentity n) (hEnergyNontrivial n)
  reflectionData := fun n =>
    finiteEvenFourTorusZ2WilsonReflectionCertificate
      (H n) (β n) (energyIdentity n) (energyNontrivial n)
      (hβ n) (hEnergyIdentity n) (hEnergyNontrivial n)
      (geometricEnergy n)
  latticeSpacing := latticeSpacing
  volumeScale := volumeScale
  finiteVolumeEuclideanCovariant := finiteVolumeEuclideanCovariant
  finiteVolumeEuclideanCovariant_proof :=
    finiteVolumeEuclideanCovariant_proof

@[simp]
theorem finiteEvenFourTorusZ2AutomaticApproximationFamily_system
    (n : ℕ) :
    (finiteEvenFourTorusZ2AutomaticApproximationFamily
      H β energyIdentity energyNontrivial latticeSpacing volumeScale
      hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
      finiteVolumeEuclideanCovariant
      finiteVolumeEuclideanCovariant_proof).system n =
      finiteEvenFourTorusZ2WilsonSystem
        (H n) (β n) (energyIdentity n) (energyNontrivial n)
        (hβ n) (hEnergyIdentity n) (hEnergyNontrivial n) :=
  rfl

/-- The concrete even-four-torus edge carrier has an explicit link witness at
every scale. -/
def finiteEvenFourTorusZ2AutomaticApproximationFamilyEdgeWitness
    (n : ℕ) :
    (finiteEvenFourTorusZ2AutomaticApproximationFamily
      H β energyIdentity energyNontrivial latticeSpacing volumeScale
      hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
      finiteVolumeEuclideanCovariant
      finiteVolumeEuclideanCovariant_proof).system n |>.Edge :=
  ((fun _ => 0), (fun _ => 0))

/-- Consequently the geometric `Nonempty Edge` condition required by the
canonical interaction construction is theorem-generated for every scale. -/
theorem finiteEvenFourTorusZ2AutomaticApproximationFamily_edge_nonempty
    (n : ℕ) :
    Nonempty
      ((finiteEvenFourTorusZ2AutomaticApproximationFamily
        H β energyIdentity energyNontrivial latticeSpacing volumeScale
        hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
        finiteVolumeEuclideanCovariant
        finiteVolumeEuclideanCovariant_proof).system n).Edge :=
  ⟨finiteEvenFourTorusZ2AutomaticApproximationFamilyEdgeWitness
    H β energyIdentity energyNontrivial latticeSpacing volumeScale
    hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
    finiteVolumeEuclideanCovariant
    finiteVolumeEuclideanCovariant_proof n⟩

/-- The explicit canonical gauge realization of the concrete even-four-torus
family at scale `n`. -/
noncomputable def finiteEvenFourTorusZ2CanonicalGaugeRealization
    (n : ℕ) :
    FiniteWilsonGibbsSingleSourceProjectiveRealization
      (finiteEvenFourTorusZ2AutomaticApproximationFamily
        H β energyIdentity energyNontrivial latticeSpacing volumeScale
        hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
        finiteVolumeEuclideanCovariant
        finiteVolumeEuclideanCovariant_proof) :=
  finiteWilsonExplicitCanonicalGaugeRealization
    (finiteEvenFourTorusZ2AutomaticApproximationFamily
      H β energyIdentity energyNontrivial latticeSpacing volumeScale
      hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
      finiteVolumeEuclideanCovariant
      finiteVolumeEuclideanCovariant_proof) n

/-- A nondegenerate finite-cylinder interaction witness for the concrete
`Z₂` even-four-torus realization, with no external edge witness. -/
noncomputable def finiteEvenFourTorusZ2CanonicalGaugeInteractionWitness
    (n : ℕ) :
    FiniteWilsonGibbsCylinderInteractionWitness
      (finiteEvenFourTorusZ2CanonicalGaugeRealization
        H β energyIdentity energyNontrivial latticeSpacing volumeScale
        hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
        finiteVolumeEuclideanCovariant
        finiteVolumeEuclideanCovariant_proof n) := by
  letI : Nonempty
      ((finiteEvenFourTorusZ2AutomaticApproximationFamily
        H β energyIdentity energyNontrivial latticeSpacing volumeScale
        hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
        finiteVolumeEuclideanCovariant
        finiteVolumeEuclideanCovariant_proof).system n).Edge :=
    finiteEvenFourTorusZ2AutomaticApproximationFamily_edge_nonempty
      H β energyIdentity energyNontrivial latticeSpacing volumeScale
      hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
      finiteVolumeEuclideanCovariant
      finiteVolumeEuclideanCovariant_proof n
  exact finiteWilsonExplicitCanonicalGaugeInteractionWitness
    (finiteEvenFourTorusZ2AutomaticApproximationFamily
      H β energyIdentity energyNontrivial latticeSpacing volumeScale
      hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
      finiteVolumeEuclideanCovariant
      finiteVolumeEuclideanCovariant_proof) n

/-- Existing coercive transfer-orbit data now constructs the reduced exact-gap
continuum spine for the concrete `Z₂` even-four-torus family.  The lattice edge
nonemptiness condition is discharged internally by the explicit link witness. -/
noncomputable def finiteEvenFourTorusZ2CanonicalGaugeCoerciveExactGapConstructionSpine
    (n : ℕ)
    (D : FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData
      (finiteEvenFourTorusZ2CanonicalGaugeRealization
        H β energyIdentity energyNontrivial latticeSpacing volumeScale
        hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
        finiteVolumeEuclideanCovariant
        finiteVolumeEuclideanCovariant_proof n))
    (measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge)
    (measureBridge_identified :
      measureBridge.measure =
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction
          (finiteEvenFourTorusZ2AutomaticApproximationFamily
            H β energyIdentity energyNontrivial latticeSpacing volumeScale
            hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
            finiteVolumeEuclideanCovariant
            finiteVolumeEuclideanCovariant_proof)
          n D).toMeasurePackage)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms = measureBridge.axioms) :
    EuclideanYangMillsContinuumMeasureExactGapConstructionSpine := by
  letI : Nonempty
      ((finiteEvenFourTorusZ2AutomaticApproximationFamily
        H β energyIdentity energyNontrivial latticeSpacing volumeScale
        hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
        finiteVolumeEuclideanCovariant
        finiteVolumeEuclideanCovariant_proof).system n).Edge :=
    finiteEvenFourTorusZ2AutomaticApproximationFamily_edge_nonempty
      H β energyIdentity energyNontrivial latticeSpacing volumeScale
      hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
      finiteVolumeEuclideanCovariant
      finiteVolumeEuclideanCovariant_proof n
  exact finiteWilsonExplicitCanonicalGaugeCoerciveExactGapConstructionSpine
    (finiteEvenFourTorusZ2AutomaticApproximationFamily
      H β energyIdentity energyNontrivial latticeSpacing volumeScale
      hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
      finiteVolumeEuclideanCovariant
      finiteVolumeEuclideanCovariant_proof)
    n D measureBridge measureBridge_identified definitionBridge
    definitionBridge_uses_measure_axioms

/-- The concrete `Z₂` even-four-torus coercive construction reaches the existing
Hamiltonian mass-gap theorem and exact non-vacuum spectral threshold. -/
theorem finiteEvenFourTorusZ2CanonicalGauge_coercive_mass_gap
    (n : ℕ)
    (D : FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData
      (finiteEvenFourTorusZ2CanonicalGaugeRealization
        H β energyIdentity energyNontrivial latticeSpacing volumeScale
        hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
        finiteVolumeEuclideanCovariant
        finiteVolumeEuclideanCovariant_proof n))
    (measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge)
    (measureBridge_identified :
      measureBridge.measure =
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction
          (finiteEvenFourTorusZ2AutomaticApproximationFamily
            H β energyIdentity energyNontrivial latticeSpacing volumeScale
            hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
            finiteVolumeEuclideanCovariant
            finiteVolumeEuclideanCovariant_proof)
          n D).toMeasurePackage)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms = measureBridge.axioms) :
    let C :=
      (finiteEvenFourTorusZ2CanonicalGaugeCoerciveExactGapConstructionSpine
        H β energyIdentity energyNontrivial latticeSpacing volumeScale
        hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
        finiteVolumeEuclideanCovariant
        finiteVolumeEuclideanCovariant_proof n D measureBridge
        measureBridge_identified definitionBridge
        definitionBridge_uses_measure_axioms).toConstructionSpine.toUnconditionalTarget
    C.toPipeline.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal = sInf C.toPipeline.nonVacuumHamiltonianSpectrum := by
  letI : Nonempty
      ((finiteEvenFourTorusZ2AutomaticApproximationFamily
        H β energyIdentity energyNontrivial latticeSpacing volumeScale
        hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
        finiteVolumeEuclideanCovariant
        finiteVolumeEuclideanCovariant_proof).system n).Edge :=
    finiteEvenFourTorusZ2AutomaticApproximationFamily_edge_nonempty
      H β energyIdentity energyNontrivial latticeSpacing volumeScale
      hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
      finiteVolumeEuclideanCovariant
      finiteVolumeEuclideanCovariant_proof n
  exact finite_wilson_explicit_canonical_gauge_coercive_mass_gap
    (finiteEvenFourTorusZ2AutomaticApproximationFamily
      H β energyIdentity energyNontrivial latticeSpacing volumeScale
      hβ hEnergyIdentity hEnergyNontrivial geometricEnergy
      finiteVolumeEuclideanCovariant
      finiteVolumeEuclideanCovariant_proof)
    n D measureBridge measureBridge_identified definitionBridge
    definitionBridge_uses_measure_axioms

end ConcreteFamily

end

end MathlibAnalytic
end MGAP4D