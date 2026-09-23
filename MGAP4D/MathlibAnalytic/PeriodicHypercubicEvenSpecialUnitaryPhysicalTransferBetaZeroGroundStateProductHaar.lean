import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroCanonicalVacuum
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
# Exact beta-zero ground-state laws are Haar product laws

At beta = 0 the canonical nonnegative physical vacuum is exactly the constant
Gauss-law unit vector and the one-slab kernel is identically one.  Therefore:

* the vacuum density is equal to one almost everywhere with respect to spatial
  Haar measure;
* the normalized ground-state joint density is equal to one almost everywhere
  with respect to pair Haar;
* the physical vacuum measure is exactly spatial Haar;
* the genuine ground-state one-slab joint measure is exactly pair Haar.

The proof deliberately works through almost-everywhere representative
identities.  It does not identify arbitrary L2 representatives pointwise.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance betaZeroGroundStateProductHaarTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance betaZeroGroundStateProductHaarCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance betaZeroGroundStateProductHaarSecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance betaZeroGroundStateProductHaarMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance betaZeroGroundStateProductHaarBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance betaZeroGroundStateProductHaarSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The canonical nonnegative beta-zero physical vacuum has the constant-one
Haar representative almost everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_zero_coeFn_ae_eq_one
    (H N : ℕ)
    (hN : 0 < N) :
    (fun A =>
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H N hN 0 (by norm_num)).1 A) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      (fun _ => (1 : ℝ)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hVac :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_zero
      H N hN
  have hVacLp :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN 0 (by norm_num)).1 =
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N := by
    calc
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN 0 (by norm_num)).1 =
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).1 :=
        congrArg Subtype.val hVac
      _ = periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N := by
        rfl
  have hOne :
      (fun A =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2 H N A) =ᵐ[μ]
        (fun _ => (1 : ℝ)) := by
    simpa [μ,
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarOneL2] using
      (Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ)))
  simpa [μ, hVacLp] using hOne

/-- The beta-zero vacuum Radon-Nikodym weight is one almost everywhere. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight_zero_ae_eq_one
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
        H N hN 0 (by norm_num) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N]
      (fun _ => (1 : ℝ)) := by
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_zero_coeFn_ae_eq_one
      H N hN] with A hA
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
  rw [hA]
  norm_num

/-- The beta-zero normalized ground-state joint density is one almost
everywhere with respect to pair Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_zero_ae_eq_one
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN 0 (by norm_num) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      (fun _ => (1 : ℝ)) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  have hOne :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_zero_coeFn_ae_eq_one
      H N hN
  have hFst :
      (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN 0 (by norm_num)).1 z.1) =ᵐ[μ.prod μ]
        (fun _ => (1 : ℝ)) :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hOne
  have hSnd :
      (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H N hN 0 (by norm_num)).1 z.2) =ᵐ[μ.prod μ]
        (fun _ => (1 : ℝ)) :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hOne
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
        H N hN 0 (by norm_num) =ᵐ[μ.prod μ]
      (fun _ => (1 : ℝ))
  filter_upwards [hFst, hSnd] with z hleft hright
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointWeight
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm
      H N hN,
    inv_one,
    hleft,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_zero,
    hright]
  norm_num

/-- At beta = 0 the physical vacuum boundary measure is exactly spatial Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_zero_eq_Haar
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN 0 (by norm_num) =
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  change
    μ.withDensity
        (fun A => ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight
            H N hN 0 (by norm_num) A)) =
      μ
  rw [← MeasureTheory.withDensity_one]
  apply withDensity_congr_ae
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumWeight_zero_ae_eq_one
      H N hN] with A hA
  rw [hA]
  norm_num

/-- At beta = 0 the genuine one-slab ground-state joint measure is exactly the
product of the two spatial Haar laws. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_zero_eq_pairHaar
    (H N : ℕ)
    (hN : 0 < N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN 0 (by norm_num) =
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N := by
  let μ :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  change
    μ.withDensity
        (fun z => ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN 0 (by norm_num) z)) =
      μ
  rw [← MeasureTheory.withDensity_one]
  apply withDensity_congr_ae
  filter_upwards [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_zero_ae_eq_one
      H N hN] with z hz
  rw [hz]
  norm_num

end

end MGAP4D.MathlibAnalytic
