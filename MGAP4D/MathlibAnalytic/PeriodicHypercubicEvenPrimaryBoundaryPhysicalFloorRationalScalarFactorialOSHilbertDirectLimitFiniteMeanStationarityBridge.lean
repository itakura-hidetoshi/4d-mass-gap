import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitCenteredReflectionFormBridge
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialFiniteLawStationarity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathTimeTranslationGeometry
import Mathlib.Tactic

/-!
# Eventual finite mean stationarity on the factorial Wilson tail

The previous same-root bridge identifies

`Q_n(τ_h F) - (E_n F)^2`

with a sequence converging to the centered OS Hilbert correlation.  Its subtraction was deliberately
kept conservative because no finite temporal stationarity was used there.

The finite factorial Wilson route already contains the missing receipt: every fixed nonnegative
rational shift is exactly a natural lattice translation at all sufficiently large selected scales,
and the actual finite scalar path law is then exactly stationary on every fixed finite nonnegative
slot set.

This file pushes that existing eventual law equality through bounded-continuous literal cylinder
observables.  It proves that, on the selected factorial tail, the finite mean of the canonically
translated cylinder is exactly the original finite mean.  Consequently the mean-subtracted
reflection form from the preceding bridge can equivalently be written using the translated
cylinder's own actual finite Wilson mean.

No whole-path finite stationarity, reflection-side centering identity, variance floor, quantitative
decay, positive mass, spectral gap, or old-carrier identification is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Eventual finite expectation stationarity for every bounded-continuous scalar cylinder on a
fixed finite nonnegative slot set, along the actual selected factorial Wilson scales. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_finiteRestriction_expectation_eventually_stationary
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∫ x,
          F
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
              J t x)
        ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
          (H (L.subsequence n)) N hN
          (beta (L.subsequence n)) (hbeta (L.subsequence n))
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence n)) =
        ∫ x,
          F
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap
              J x)
          ∂periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence n) := by
  filter_upwards [
    L.factorial_finiteRestriction_law_eventually_stationary
      H N hN beta hbeta J hJ t ht] with n hn
  let μ : Measure (ℚ → ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      (L.subsequence n)
  let τ : C(ℚ → ℝ, ∀ q : J, ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap
      J t
  let ρ : C(ℚ → ℝ, ∀ q : J, ℝ) :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteRestrictionContinuousMap J
  have hLaw : Measure.map τ μ = Measure.map ρ μ := by
    simpa [μ, τ, ρ] using hn
  change (∫ x, F (τ x) ∂μ) = ∫ x, F (ρ x) ∂μ
  calc
    (∫ x, F (τ x) ∂μ) = ∫ v, F v ∂Measure.map τ μ := by
      symm
      exact
        MeasureTheory.integral_map
          τ.measurable.aemeasurable F.continuous.aestronglyMeasurable
    _ = ∫ v, F v ∂Measure.map ρ μ := by rw [hLaw]
    _ = ∫ x, F (ρ x) ∂μ := by
      exact
        MeasureTheory.integral_map
          ρ.measurable.aemeasurable F.continuous.aestronglyMeasurable

/-- The same eventual stationarity, rewritten on the reindexed probability measures used by the
same-root weak-limit / Hilbert bridge. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_fixedSlotObservableTimeTranslate_finiteExpectation_reindexed_eventually_eq
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (t : ℚ) (ht : 0 ≤ t)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    ∀ᶠ n : ℕ in atTop,
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            (fun k =>
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence k))
            n)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFiniteSlotTimeTranslate
              t J)
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableTimeTranslate
              J t F)) =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            (fun k =>
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence k))
            n)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
            J F) := by
  filter_upwards [
    L.factorial_finiteRestriction_expectation_eventually_stationary
      H N hN beta hbeta J hJ t ht F] with n hn
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply]
  rw [←
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_spacing_reindex
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      L.subsequence n]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure_toMeasure]
  simpa only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_timeTranslate,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathTimeTranslate_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarShiftedFiniteRestrictionContinuousMap_apply]
    using hn

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- On the actual selected factorial Wilson tail, the finite mean of the canonically translated
literal cylinder is exactly its original finite mean. -/
theorem fixedSlotCarrierFiniteMean_timeTranslate_eventually_eq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (F : P.FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      (P.fixedSlotTimeTranslateData t ht).fixedSlotCarrierFiniteMean
          (P.fixedSlotCarrierTimeTranslate t ht F) n =
        P.fixedSlotCarrierFiniteMean F n := by
  have h :=
    L.factorial_fixedSlotObservableTimeTranslate_finiteExpectation_reindexed_eventually_eq
      H N hN beta hbeta P.slots (fun q => P.slots_nonneg q.1 q.2) t ht F.observable
  simpa [fixedSlotCarrierFiniteMean,
    fixedSlotTimeTranslateData_slots,
    fixedSlotCarrierTimeTranslate_observable] using h

/-- Indexed form used directly by the literal-cylinder Hilbert/reflection bridge. -/
theorem fixedSlotCarrierFiniteMean_indexedTimeTranslate_eventually_eq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (t : ℚ) (ht : 0 ≤ t)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      (P.fixedSlotDataOfIndex
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).fixedSlotCarrierFiniteMean
          ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate t ht F) n =
        (P.fixedSlotDataOfIndex J).fixedSlotCarrierFiniteMean F n := by
  simpa [fixedSlotTimeTranslateData] using
    (P.fixedSlotDataOfIndex J).fixedSlotCarrierFiniteMean_timeTranslate_eventually_eq
      t ht F

/-- Therefore the finite mean-subtracted reflection form from the centered weak-limit bridge can,
on the factorial tail, subtract the translated literal cylinder's own actual finite Wilson mean. -/
theorem fixedSlotCarrierFiniteMeanSubtractedReflectionForm_eventually_eq_translatedMeanSubtracted
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteMeanSubtractedReflectionForm J h hh F n =
        ((P.fixedSlotDataOfIndex
            (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)).fixedSlotCarrierPositiveCylinder
          ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F)).realReflectionForm
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
              (H (L.subsequence n)) N hN
              (beta (L.subsequence n)) (hbeta (L.subsequence n))
              (fun k =>
                periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                  (L.subsequence k))
              n : Measure (ℚ → ℝ)) -
          ((P.fixedSlotDataOfIndex
              (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)).fixedSlotCarrierFiniteMean
            ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F) n) ^ 2 := by
  filter_upwards [
    P.fixedSlotCarrierFiniteMean_indexedTimeTranslate_eventually_eq J h hh F] with n hn
  rw [fixedSlotCarrierFiniteMeanSubtractedReflectionForm, hn]

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
