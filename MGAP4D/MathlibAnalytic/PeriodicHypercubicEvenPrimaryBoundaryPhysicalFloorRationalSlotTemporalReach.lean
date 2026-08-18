import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathWeakLimitOS
import Mathlib.Tactic

/-!
# Primary rational-slot admissibility from explicit temporal reach

The one-sided primary finite OS theorem requires the local finite-scale condition

`Int.toNat (⌊q / a_n⌋) ≤ H_n`

for every rational cylinder slot.  This file derives that condition from the
actual temporal quantity that controls it: the primary half-lattice reach
`H_n * a_n`.

No relation to a separately named physical volume is asserted.  In particular,
this file does not identify `physicalVolume` with `H_n * a_n` and does not infer
half-extent growth from a volume limit.  Instead, divergence of the explicit
primary temporal reach is a transparent scaling hypothesis.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- Physical temporal reach of the one-sided primary half lattice at scale `n`.
This is only the product of the available integer half extent and the lattice
spacing; it is not identified with any separately defined physical volume. -/
def periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
    (H : ℕ → ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) : ℝ :=
  (H n : ℝ) * latticeSpacing n

/-- A nonnegative target time below the explicit primary temporal reach has its
canonical floor-selected natural time index inside the primary half extent. -/
theorem physicalTemporalFloorStep_toNat_le_of_le_primaryTemporalReach
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (n : ℕ)
    (ht_reach : t ≤ (H : ℝ) * latticeSpacing n) :
    Int.toNat (physicalTemporalFloorStep latticeSpacing t n) ≤ H := by
  have hdiv_nonneg : 0 ≤ t / latticeSpacing n :=
    div_nonneg ht_nonneg (latticeSpacing_pos n).le
  have hdiv_le : t / latticeSpacing n ≤ (H : ℝ) := by
    exact (div_le_iff₀ (latticeSpacing_pos n)).2 ht_reach
  have hfloor_nonneg :
      0 ≤ physicalTemporalFloorStep latticeSpacing t n := by
    unfold physicalTemporalFloorStep
    exact Int.floor_nonneg.2 hdiv_nonneg
  have hfloor_le :
      physicalTemporalFloorStep latticeSpacing t n ≤ (H : ℤ) := by
    unfold physicalTemporalFloorStep
    have hmono := Int.floor_le_floor hdiv_le
    simpa using hmono
  omega

/-- If the explicit primary temporal reach tends to infinity, then every fixed
finite nonnegative rational cylinder is eventually admissible for the one-sided
primary physical-floor readout.

The proof uses a single finite upper bound (the sum of absolute slot times), so
no cross-scale identification of edge carriers is involved. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_eventually_admissible_of_temporalReach
    (H : ℕ → ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder) :
    Filter.Eventually
      (fun n : ℕ =>
        PeriodicHypercubicEvenPrimarySpatialPositiveRationalSlotsAdmissible
          (H n) latticeSpacing n Cyl.slots)
      atTop := by
  let T : ℝ :=
    Finset.sum Cyl.slots (fun q => |((q : ℚ) : ℝ)|)
  have hreach_event :
      Filter.Eventually
        (fun n : ℕ =>
          T ≤ periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing n)
        atTop :=
    (tendsto_atTop.1 hreach T)
  filter_upwards [hreach_event] with n hn
  constructor
  · intro q
    exact Cyl.slots_nonneg q.1 q.2
  · intro q
    have hq_nonneg_rat : (0 : ℚ) ≤ q.1 :=
      Cyl.slots_nonneg q.1 q.2
    have hq_nonneg_real : (0 : ℝ) ≤ ((q.1 : ℚ) : ℝ) := by
      exact_mod_cast hq_nonneg_rat
    have hq_le_T : ((q.1 : ℚ) : ℝ) ≤ T := by
      calc
        ((q.1 : ℚ) : ℝ) ≤ |((q.1 : ℚ) : ℝ)| := le_abs_self _
        _ ≤ T := by
          dsimp [T]
          exact Finset.single_le_sum
            (fun r _ => abs_nonneg (((r : ℚ) : ℝ))) q.2
    have hq_reach :
        ((q.1 : ℚ) : ℝ) ≤ (H n : ℝ) * latticeSpacing n := by
      exact hq_le_T.trans hn
    exact
      physicalTemporalFloorStep_toNat_le_of_le_primaryTemporalReach
        (H n) latticeSpacing latticeSpacing_pos ((q.1 : ℚ) : ℝ)
        hq_nonneg_real n hq_reach

/-- Weak-limit OS positivity with the eventual-admissibility premise discharged
by explicit divergence of the primary temporal reach.

Weak convergence of the new same-root scalar path laws remains a separate input;
this theorem removes only the finite-slot geometric side condition. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_weakLimit_reflectionForm_nonneg_of_temporalReach
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (μlim : ProbabilityMeasure (ℚ → ℝ))
    (hweak :
      Tendsto
        (fun n =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H n) N hN (beta n) (hbeta n) latticeSpacing n)
        atTop
        (nhds μlim))
    (Cyl : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder) :
    0 ≤ Cyl.realReflectionForm (μlim : Measure (ℚ → ℝ)) := by
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_weakLimit_reflectionForm_nonneg
      H N hN beta hbeta latticeSpacing μlim hweak Cyl
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPositiveCylinder_eventually_admissible_of_temporalReach
        H latticeSpacing latticeSpacing_pos hreach Cyl)

end

end MathlibAnalytic
end MGAP4D
