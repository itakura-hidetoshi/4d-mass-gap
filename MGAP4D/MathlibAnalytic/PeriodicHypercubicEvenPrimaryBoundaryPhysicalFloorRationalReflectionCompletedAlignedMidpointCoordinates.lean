import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalReflectionTranslationConjugacy
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalAlignedReadoutCovariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalPathReflectionCompletion
import Mathlib.Tactic

/-!
# Aligned midpoint coordinates on the reflection-completed primary path

For the OS quadratic form one does not need a global time-translation law for the whole
reflection-completed rational path.  It is enough to control the two symmetric coordinates that
occur after translating a positive-time cylinder.

At a finite Wilson scale, let the nonnegative rational shift `t` be exactly aligned with `k`
natural lattice steps.  Translating the source backwards by `k` sends the two relevant completed
path coordinates as follows:

`q + t     ↦ q + t + t`,
`-(q + t) ↦ -q`,

for every `q ≥ 0`.  The positive coordinate is the existing one-sided aligned readout covariance.
The negative coordinate additionally uses the already-canonical finite reflection--translation
conjugacy `θ T_{-k} = T_k θ`.

No whole-path covariance, measure statement, continuum premise, OS contraction, null-space
preservation, semigroup, Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- On the positive member of an OS-reflected pair, backward source translation by the aligned
lattice step advances the original completed path from `q+t` to `q+t+t`. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_add_aligned_negConfigurationTranslation
    {Gauge : Type} [Group Gauge] [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (q t : ℚ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (k : ℕ)
    (halign : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ))
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A) (q + t) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n A ((q + t) + t) := by
  have hqt : 0 ≤ q + t := add_nonneg hq ht
  have hqtt : 0 ≤ (q + t) + t := add_nonneg hqt ht
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
      H latticeSpacing n _ (q + t) hqt,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
      H latticeSpacing n A ((q + t) + t) hqtt]
  exact
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_add_aligned
      H latticeSpacing latticeSpacing_pos n (q + t) t hqt k halign A).symm

/-- On the reflected member of the same OS pair, backward source translation by the aligned step
moves `-(q+t)` exactly to `-q`.  This uses only source reflection covariance, the existing finite
reflection--translation conjugacy, and the one-sided forward aligned covariance. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_neg_add_aligned_negConfigurationTranslation
    {Gauge : Type} [Group Gauge] [MeasurableSpace Gauge]
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ)
    (q t : ℚ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (k : ℕ)
    (halign : PhysicalTemporalFloorRationalTimeAligned latticeSpacing n t (k : ℤ))
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A) (-(q + t)) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n A (-q) := by
  have hqt : 0 ≤ q + t := add_nonneg hq ht
  let B : PeriodicHypercubicEvenEdge H → Gauge :=
    periodicHypercubicIntegerTemporalConfigurationTranslation
      (PeriodicHypercubicEvenSideLength H) (-(k : ℤ)) A
  calc
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n B (-(q + t)) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n (periodicHypercubicEvenConfigurationReflection H B) (q + t) := by
      have href := congrFun
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_configurationReflection
          H latticeSpacing n B) (q + t)
      simpa [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection] using href.symm
    _ = periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n
        (periodicHypercubicIntegerTemporalConfigurationTranslation
          (PeriodicHypercubicEvenSideLength H) (k : ℤ)
          (periodicHypercubicEvenConfigurationReflection H A)) (q + t) := by
      have hconj :=
        periodicHypercubicEvenConfigurationReflection_integerTemporalTranslation
          H (-(k : ℤ)) A
      simp only [Int.neg_neg] at hconj
      rw [show periodicHypercubicEvenConfigurationReflection H B =
          periodicHypercubicIntegerTemporalConfigurationTranslation
            (PeriodicHypercubicEvenSideLength H) (k : ℤ)
            (periodicHypercubicEvenConfigurationReflection H A) by
        simpa [B] using hconj]
    _ = periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n (periodicHypercubicEvenConfigurationReflection H A) q := by
      rw [
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
          H latticeSpacing n _ (q + t) hqt,
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
          H latticeSpacing n _ q hq]
      exact
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReadout_add_aligned_configurationTranslation
          H latticeSpacing latticeSpacing_pos n q t hq k halign
          (periodicHypercubicEvenConfigurationReflection H A)
    _ = periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
        H latticeSpacing n A (-q) := by
      have href := congrFun
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_configurationReflection
          H latticeSpacing n A) q
      simpa [periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalPathReflection] using href

end

end MathlibAnalytic
end MGAP4D
