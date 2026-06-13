import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticGramBridge
import MGAP4D.MathlibAnalytic.FiniteWilsonOSApproximationFamily

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A reduced finite-volume Wilson approximation family.

Unlike `FiniteWilsonOSApproximationFamily`, this structure does not ask for a
separate Gram bridge at every scale.  The bridge is generated canonically from
the half-configuration equivalence and kernel agreement already contained in
each reflection certificate. -/
structure FiniteWilsonOSAutomaticApproximationFamily where
  index : Type
  system : index → FiniteLatticeWilsonSystem
  reflectionData :
    ∀ i, FiniteLatticeWilsonOSReflectionCertificate (system i)
  latticeSpacing : index → ℝ
  volumeScale : index → ℝ
  finiteVolumeEuclideanCovariant : Prop
  finiteVolumeEuclideanCovariant_proof : finiteVolumeEuclideanCovariant

/-- Forgetful projection to the previous family, filling each Gram bridge by the
canonical finite-sum transport construction. -/
def FiniteWilsonOSAutomaticApproximationFamily.toLegacyFamily
    (F : FiniteWilsonOSAutomaticApproximationFamily) :
    FiniteWilsonOSApproximationFamily :=
  { index := F.index
    system := F.system
    reflectionData := F.reflectionData
    gramBridge := fun i => (F.reflectionData i).automaticGramBridge
    latticeSpacing := F.latticeSpacing
    volumeScale := F.volumeScale
    finiteVolumeEuclideanCovariant := F.finiteVolumeEuclideanCovariant
    finiteVolumeEuclideanCovariant_proof :=
      F.finiteVolumeEuclideanCovariant_proof }

/-- Actual OS reflection positivity follows automatically at every lattice
scale. -/
def FiniteWilsonOSAutomaticApproximationFamily.ActualReflectionPositive
    (F : FiniteWilsonOSAutomaticApproximationFamily) : Prop :=
  ∀ i, FiniteLatticeWilsonOSReflectionPositive (F.reflectionData i)

/-- Reflection positivity of the reduced family. -/
theorem finite_wilson_os_automatic_family_actualReflectionPositive
    (F : FiniteWilsonOSAutomaticApproximationFamily) :
    F.ActualReflectionPositive := by
  intro i
  exact finite_lattice_wilson_os_reflection_positive_of_certificate
    (F.reflectionData i)

/-- Actual finite-group gauge invariance of singleton probabilities at every
lattice scale. -/
def FiniteWilsonOSAutomaticApproximationFamily.ActualGaugeInvariant
    (F : FiniteWilsonOSAutomaticApproximationFamily) : Prop :=
  ∀ i (γ : (F.system i).GaugeTransformation)
    (A : (F.system i).Configuration),
    (F.system i).gibbsMeasure
        ({(F.system i).gaugeTransform γ A} : Set (F.system i).Configuration) =
      (F.system i).gibbsMeasure ({A} : Set (F.system i).Configuration)

/-- Gauge invariance of the reduced family. -/
theorem finite_wilson_os_automatic_family_actualGaugeInvariant
    (F : FiniteWilsonOSAutomaticApproximationFamily) :
    F.ActualGaugeInvariant := by
  intro i γ A
  exact finite_lattice_gibbsMeasure_singleton_gaugeInvariant
    (F.system i) γ A

/-- Direct projection to the repository's finite-volume Euclidean Yang--Mills
construction spine. -/
def FiniteWilsonOSAutomaticApproximationFamily.toFiniteVolumeApproximation
    (F : FiniteWilsonOSAutomaticApproximationFamily) :
    EuclideanYangMillsFiniteVolumeApproximation :=
  F.toLegacyFamily.toFiniteVolumeApproximation

/-- Every induced finite-volume Wilson measure is a probability measure. -/
theorem finite_wilson_os_automatic_family_probability_measure
    (F : FiniteWilsonOSAutomaticApproximationFamily) (i : F.index) :
    MeasureTheory.IsProbabilityMeasure
      (F.toFiniteVolumeApproximation.finiteVolumeMeasure
        (show F.toFiniteVolumeApproximation.index from i)) := by
  change MeasureTheory.IsProbabilityMeasure (F.system i).gibbsMeasure
  infer_instance

/-- Audit-visible certificate for the reduced finite-volume family. -/
structure FiniteWilsonOSAutomaticMeasureCertificate
    (F : FiniteWilsonOSAutomaticApproximationFamily) where
  probabilityMeasure :
    ∀ i : F.index, MeasureTheory.IsProbabilityMeasure
      (F.toFiniteVolumeApproximation.finiteVolumeMeasure
        (show F.toFiniteVolumeApproximation.index from i))
  gaugeInvariant : F.ActualGaugeInvariant
  reflectionPositive : F.ActualReflectionPositive
  euclideanCovariant : F.finiteVolumeEuclideanCovariant

/-- Construct the reduced finite-volume probability/gauge/OS certificate. -/
def finiteWilsonOSAutomaticMeasureCertificate
    (F : FiniteWilsonOSAutomaticApproximationFamily) :
    FiniteWilsonOSAutomaticMeasureCertificate F :=
  { probabilityMeasure :=
      finite_wilson_os_automatic_family_probability_measure F
    gaugeInvariant :=
      finite_wilson_os_automatic_family_actualGaugeInvariant F
    reflectionPositive :=
      finite_wilson_os_automatic_family_actualReflectionPositive F
    euclideanCovariant := F.finiteVolumeEuclideanCovariant_proof }

end

end MathlibAnalytic
end MGAP4D
