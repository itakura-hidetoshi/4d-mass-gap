import MGAP4D.MathlibAnalytic.FiniteWilsonOSReflectionPositivity
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonPlaquetteOrbitSideClassification
import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonGeometricPlaquetteSideClassification
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusWilsonGeometricClassification
import MGAP4D.MathlibAnalytic.Z2FiniteFourDimensionalTimeSupportReflection
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPlaquetteSupportReflection
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPlaquetteReflection
import MGAP4D.MathlibAnalytic.Z2FiniteInvolutivePlaquetteGeometricSidePartition
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPlaquetteSupportCompatibility

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A finite-volume Wilson approximation family carrying an actual
Osterwalder--Schrader reflection decomposition at every lattice scale. -/
structure FiniteWilsonOSApproximationFamily where
  index : Type
  system : index → FiniteLatticeWilsonSystem
  reflectionData :
    ∀ i, FiniteLatticeWilsonOSReflectionCertificate (system i)
  gramBridge :
    ∀ i, FiniteLatticeWilsonOSGramBridge (reflectionData i)
  latticeSpacing : index → ℝ
  volumeScale : index → ℝ
  finiteVolumeEuclideanCovariant : Prop
  finiteVolumeEuclideanCovariant_proof : finiteVolumeEuclideanCovariant

/-- Actual finite-volume reflection positivity at all lattice scales. -/
def FiniteWilsonOSApproximationFamily.ActualReflectionPositive
    (F : FiniteWilsonOSApproximationFamily) : Prop :=
  ∀ i, FiniteLatticeWilsonOSReflectionPositive (F.reflectionData i)

/-- The Gram/character bridge proves actual OS positivity at every scale. -/
theorem finite_wilson_os_family_actualReflectionPositive
    (F : FiniteWilsonOSApproximationFamily) :
    F.ActualReflectionPositive := by
  intro i
  exact finite_lattice_wilson_os_gram_bridge_closes_reflectionPositivity
    (F.reflectionData i) (F.gramBridge i)

/-- Actual gauge invariance of all singleton probabilities in the finite-group
Wilson family. -/
def FiniteWilsonOSApproximationFamily.ActualGaugeInvariant
    (F : FiniteWilsonOSApproximationFamily) : Prop :=
  ∀ i (γ : (F.system i).GaugeTransformation)
    (A : (F.system i).Configuration),
    (F.system i).gibbsMeasure
        ({(F.system i).gaugeTransform γ A} : Set (F.system i).Configuration) =
      (F.system i).gibbsMeasure ({A} : Set (F.system i).Configuration)

/-- Finite-group Wilson Gibbs measures are gauge invariant at every scale. -/
theorem finite_wilson_os_family_actualGaugeInvariant
    (F : FiniteWilsonOSApproximationFamily) :
    F.ActualGaugeInvariant := by
  intro i γ A
  exact finite_lattice_gibbsMeasure_singleton_gaugeInvariant
    (F.system i) γ A

/-- The OS-enhanced finite Wilson family induces the repository's finite-volume
Euclidean Yang--Mills approximation surface.  Gauge invariance and reflection
positivity are now theorem-generated rather than supplied as opaque readiness
markers. -/
def FiniteWilsonOSApproximationFamily.toFiniteVolumeApproximation
    (F : FiniteWilsonOSApproximationFamily) :
    EuclideanYangMillsFiniteVolumeApproximation :=
  { index := F.index
    finiteVolumeConfiguration := fun i => (F.system i).Configuration
    finiteVolumeMeasurableSpace := fun _i => inferInstance
    finiteVolumeMeasure := fun i => (F.system i).gibbsMeasure
    latticeSpacing := F.latticeSpacing
    volumeScale := F.volumeScale
    gaugeInvariantFiniteVolume := F.ActualGaugeInvariant
    gaugeInvariantFiniteVolume_proof :=
      finite_wilson_os_family_actualGaugeInvariant F
    finiteVolumeReflectionPositive := F.ActualReflectionPositive
    finiteVolumeReflectionPositive_proof :=
      finite_wilson_os_family_actualReflectionPositive F
    finiteVolumeEuclideanCovariant := F.finiteVolumeEuclideanCovariant
    finiteVolumeEuclideanCovariant_proof :=
      F.finiteVolumeEuclideanCovariant_proof
    finiteVolumeSchwingerData := fun _n => ℝ }

/-- Every finite-volume measure in the OS-enhanced Wilson family is a genuine
probability measure. -/
theorem finite_wilson_os_family_probability_measure
    (F : FiniteWilsonOSApproximationFamily) (i : F.index) :
    MeasureTheory.IsProbabilityMeasure
      (F.toFiniteVolumeApproximation.finiteVolumeMeasure
        (show F.toFiniteVolumeApproximation.index from i)) := by
  change MeasureTheory.IsProbabilityMeasure (F.system i).gibbsMeasure
  infer_instance

/-- A compact certificate exposing the concrete finite-volume achievements. -/
structure FiniteWilsonOSMeasureCertificate
    (F : FiniteWilsonOSApproximationFamily) where
  probabilityMeasure :
    ∀ i : F.index, MeasureTheory.IsProbabilityMeasure
      (F.toFiniteVolumeApproximation.finiteVolumeMeasure
        (show F.toFiniteVolumeApproximation.index from i))
  gaugeInvariant : F.ActualGaugeInvariant
  reflectionPositive : F.ActualReflectionPositive
  euclideanCovariant : F.finiteVolumeEuclideanCovariant

/-- Construct the finite-volume measure/OS certificate from the Wilson family. -/
def finiteWilsonOSMeasureCertificate
    (F : FiniteWilsonOSApproximationFamily) :
    FiniteWilsonOSMeasureCertificate F :=
  { probabilityMeasure := finite_wilson_os_family_probability_measure F
    gaugeInvariant := finite_wilson_os_family_actualGaugeInvariant F
    reflectionPositive := finite_wilson_os_family_actualReflectionPositive F
    euclideanCovariant := F.finiteVolumeEuclideanCovariant_proof }

end

end MathlibAnalytic
end MGAP4D
