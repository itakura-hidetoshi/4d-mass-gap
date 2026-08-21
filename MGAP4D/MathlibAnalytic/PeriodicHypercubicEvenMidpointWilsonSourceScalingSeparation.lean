import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenMidpointWilsonSourceInteriorMarginSeparation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalSlotTemporalReach
import Mathlib.Tactic

/-!
# Scaling discharge for midpoint Wilson-source support separation

The previous layer rewrites the actual plaquette-local support-distance lower
bound into three finite-scale floor inequalities.  This file discharges those
inequalities from the same scaling data already used by the primary scalar OS
construction:

* positive lattice spacing `a_n`;
* `a_n -> 0`;
* divergent primary temporal reach `H_n * a_n -> +infinity`;
* one strictly positive rational midpoint offset `r`.

For every fixed natural distance `D`, vanishing spacing makes the translated
right floor index eventually at least `D`, while divergent temporal reach leaves
an eventual `D`-step interior margin on both sides.  Hence the literal supports
of the actual compact `SU(N)` midpoint Wilson covariance are eventually
separated by at least `D` actual Wilson-plaquette-local steps.

The strict positivity of `r` is essential for this statement.  At `r = 0` with
a zero slot, no positive direct-arc lower bound follows from scaling alone.

This file proves only geometric separation.  It proves no covariance decay
rate, assumes no factorial high-temperature Dobrushin inequality, identifies no
stochastic update time with Euclidean time, and claims no positive mass or
Hamiltonian gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- If a nonnegative physical time is at least `D` lattice spacings away from
zero, its canonical floor index is at least `D`. -/
theorem physicalTemporalFloorStep_toNat_ge_of_nat_mul_spacing_le
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (n D : ℕ)
    (hD : (D : ℝ) * latticeSpacing n ≤ t) :
    D ≤ Int.toNat (physicalTemporalFloorStep latticeSpacing t n) := by
  have hdiv : (D : ℝ) ≤ t / latticeSpacing n := by
    exact (le_div_iff₀ (latticeSpacing_pos n)).2 hD
  have hfloor :
      (D : ℤ) ≤ physicalTemporalFloorStep latticeSpacing t n := by
    unfold physicalTemporalFloorStep
    have hmono := Int.floor_le_floor hdiv
    simpa using hmono
  omega

/-- If a nonnegative physical time together with `D` further lattice spacings
fits inside the primary temporal reach, then its floor index has a `D`-step
interior margin. -/
theorem physicalTemporalFloorStep_toNat_add_le_of_add_nat_mul_spacing_le_primaryTemporalReach
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (n D : ℕ)
    (ht_reach :
      t + (D : ℝ) * latticeSpacing n ≤ (H : ℝ) * latticeSpacing n) :
    Int.toNat (physicalTemporalFloorStep latticeSpacing t n) + D ≤ H := by
  have hdiv_nonneg : 0 ≤ t / latticeSpacing n :=
    div_nonneg ht_nonneg (latticeSpacing_pos n).le
  have hfloor_nonneg :
      0 ≤ physicalTemporalFloorStep latticeSpacing t n := by
    unfold physicalTemporalFloorStep
    exact Int.floor_nonneg.2 hdiv_nonneg
  have hdivD :
      t / latticeSpacing n + (D : ℝ) ≤ (H : ℝ) := by
    have h :=
      (div_le_iff₀ (latticeSpacing_pos n)).2 ht_reach
    calc
      t / latticeSpacing n + (D : ℝ) =
          (t + (D : ℝ) * latticeSpacing n) / latticeSpacing n := by
            field_simp [ne_of_gt (latticeSpacing_pos n)]
      _ ≤ (H : ℝ) := h
  have hfloor_le_div :
      ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) ≤
        t / latticeSpacing n := by
    unfold physicalTemporalFloorStep
    exact Int.floor_le _
  have hreal :
      ((physicalTemporalFloorStep latticeSpacing t n : ℤ) : ℝ) + (D : ℝ) ≤
        (H : ℝ) := by
    linarith [hfloor_le_div, hdivD]
  have hint :
      physicalTemporalFloorStep latticeSpacing t n + (D : ℤ) ≤ (H : ℤ) := by
    exact_mod_cast hreal
  omega

/-- A strictly positive midpoint offset and vanishing lattice spacing make the
translated-right floor index eventually dominate every fixed natural `D`.
Consequently the sum of the left and right floor indices also dominates `D`,
uniformly over the finite slot set. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_eventually_floor_sum_ge_of_spacing_tendsto_zero
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 < r)
    (D : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ qLeft : ℚ, qLeft ∈ J → ∀ qRight : ℚ, qRight ∈ J →
        D ≤
          Int.toNat
              (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
            Int.toNat
              (physicalTemporalFloorStep latticeSpacing
                ((((qRight + r) + r : ℚ) : ℝ)) n) := by
  have hDzero :
      Tendsto (fun n => (D : ℝ) * latticeSpacing n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul latticeSpacing_tendsto_zero)
  have hr_real : 0 < ((r : ℚ) : ℝ) := by
    exact_mod_cast hr
  have htwo_r_pos : 0 < 2 * ((r : ℚ) : ℝ) := by
    positivity
  have hDsmall :
      ∀ᶠ n : ℕ in atTop,
        (D : ℝ) * latticeSpacing n < 2 * ((r : ℚ) : ℝ) :=
    (tendsto_order.1 hDzero).2 _ htwo_r_pos
  filter_upwards [hDsmall] with n hn
  intro _qLeft _hqLeft qRight hqRight
  have hqRight_nonneg : 0 ≤ qRight := hJ qRight hqRight
  have htime_rat : 0 ≤ (qRight + r) + r := by
    linarith [hr.le]
  have htime_real :
      0 ≤ ((((qRight + r) + r : ℚ) : ℝ)) := by
    exact_mod_cast htime_rat
  have htwo_r_le_rat : 2 * r ≤ (qRight + r) + r := by
    linarith
  have htwo_r_le_real :
      2 * ((r : ℚ) : ℝ) ≤ ((((qRight + r) + r : ℚ) : ℝ)) := by
    exact_mod_cast htwo_r_le_rat
  have hDtime :
      (D : ℝ) * latticeSpacing n ≤
        ((((qRight + r) + r : ℚ) : ℝ)) :=
    hn.le.trans htwo_r_le_real
  have hright :
      D ≤
        Int.toNat
          (physicalTemporalFloorStep latticeSpacing
            ((((qRight + r) + r : ℚ) : ℝ)) n) :=
    physicalTemporalFloorStep_toNat_ge_of_nat_mul_spacing_le
      latticeSpacing latticeSpacing_pos
      ((((qRight + r) + r : ℚ) : ℝ)) htime_real n D hDtime
  omega

/-- Vanishing spacing and divergent primary temporal reach leave every fixed
finite slot set an eventual `D`-step interior margin, both before reflection and
on the translated-right midpoint side. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_eventually_interior_margins_of_scaling
    (H : ℕ → ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (D : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (∀ q : ℚ, q ∈ J →
        Int.toNat
            (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) + D ≤ H n) ∧
      (∀ q : ℚ, q ∈ J →
        Int.toNat
            (physicalTemporalFloorStep latticeSpacing
              ((((q + r) + r : ℚ) : ℝ)) n) + D ≤ H n) := by
  let T : ℝ :=
    Finset.sum J (fun q =>
      |((q : ℚ) : ℝ)| + |((((q + r) + r : ℚ) : ℝ))|)
  have hreach_event :
      ∀ᶠ n : ℕ in atTop,
        T + 1 ≤
          periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
            H latticeSpacing n :=
    tendsto_atTop.1 hreach (T + 1)
  have hDzero :
      Tendsto (fun n => (D : ℝ) * latticeSpacing n) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul latticeSpacing_tendsto_zero)
  have hDsmall :
      ∀ᶠ n : ℕ in atTop, (D : ℝ) * latticeSpacing n < 1 :=
    (tendsto_order.1 hDzero).2 _ zero_lt_one
  filter_upwards [hreach_event, hDsmall] with n hnReach hnD
  constructor
  · intro q hq
    have hq_nonneg_rat : 0 ≤ q := hJ q hq
    have hq_nonneg_real : 0 ≤ ((q : ℚ) : ℝ) := by
      exact_mod_cast hq_nonneg_rat
    have hterm_le_T :
        |((q : ℚ) : ℝ)| + |((((q + r) + r : ℚ) : ℝ))| ≤ T := by
      dsimp [T]
      exact
        Finset.single_le_sum
          (fun p _ =>
            add_nonneg
              (abs_nonneg (((p : ℚ) : ℝ)))
              (abs_nonneg ((((p + r) + r : ℚ) : ℝ))))
          hq
    have hq_le_T : ((q : ℚ) : ℝ) ≤ T := by
      calc
        ((q : ℚ) : ℝ) ≤ |((q : ℚ) : ℝ)| := le_abs_self _
        _ ≤ |((q : ℚ) : ℝ)| + |((((q + r) + r : ℚ) : ℝ))| :=
          le_add_of_nonneg_right (abs_nonneg _)
        _ ≤ T := hterm_le_T
    have haug :
        ((q : ℚ) : ℝ) + (D : ℝ) * latticeSpacing n ≤
          periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
            H latticeSpacing n := by
      have hqD :
          ((q : ℚ) : ℝ) + (D : ℝ) * latticeSpacing n ≤ T + 1 := by
        linarith [hnD]
      exact hqD.trans hnReach
    exact
      physicalTemporalFloorStep_toNat_add_le_of_add_nat_mul_spacing_le_primaryTemporalReach
        (H n) latticeSpacing latticeSpacing_pos ((q : ℚ) : ℝ)
        hq_nonneg_real n D (by
          simpa [periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach] using haug)
  · intro q hq
    have hq_nonneg_rat : 0 ≤ q := hJ q hq
    have htime_rat : 0 ≤ (q + r) + r := by
      linarith
    have htime_real :
        0 ≤ ((((q + r) + r : ℚ) : ℝ)) := by
      exact_mod_cast htime_rat
    have hterm_le_T :
        |((q : ℚ) : ℝ)| + |((((q + r) + r : ℚ) : ℝ))| ≤ T := by
      dsimp [T]
      exact
        Finset.single_le_sum
          (fun p _ =>
            add_nonneg
              (abs_nonneg (((p : ℚ) : ℝ)))
              (abs_nonneg ((((p + r) + r : ℚ) : ℝ))))
          hq
    have htime_le_T :
        ((((q + r) + r : ℚ) : ℝ)) ≤ T := by
      calc
        ((((q + r) + r : ℚ) : ℝ)) ≤
            |((((q + r) + r : ℚ) : ℝ))| := le_abs_self _
        _ ≤ |((q : ℚ) : ℝ)| + |((((q + r) + r : ℚ) : ℝ))| :=
          le_add_of_nonneg_left (abs_nonneg _)
        _ ≤ T := hterm_le_T
    have haug :
        ((((q + r) + r : ℚ) : ℝ)) + (D : ℝ) * latticeSpacing n ≤
          periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
            H latticeSpacing n := by
      have hqD :
          ((((q + r) + r : ℚ) : ℝ)) + (D : ℝ) * latticeSpacing n ≤ T + 1 := by
        linarith [hnD]
      exact hqD.trans hnReach
    exact
      physicalTemporalFloorStep_toNat_add_le_of_add_nat_mul_spacing_le_primaryTemporalReach
        (H n) latticeSpacing latticeSpacing_pos
        ((((q + r) + r : ℚ) : ℝ)) htime_real n D (by
          simpa [periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach] using haug)

/-- Under the same scaling assumptions, every fixed positive midpoint offset and
fixed natural `D` eventually give actual `D`-step Wilson-plaquette-local
separation of the reflected-left and translated-right literal supports. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_eventually_plaquetteLocalSeparatedBy_of_scaling
    (H : ℕ → ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 < r)
    (D : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy (H n) D
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          (H n) latticeSpacing n J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          (H n) latticeSpacing n J r) := by
  have hsum :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_eventually_floor_sum_ge_of_spacing_tendsto_zero
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero J hJ r hr D
  have hmargins :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_eventually_interior_margins_of_scaling
      H latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero hreach
      J hJ r hr.le D
  filter_upwards [hsum, hmargins] with n hsum_n hmargins_n
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_plaquetteLocalSeparatedBy_of_sum_ge_of_interior_margin
      (H n) latticeSpacing n J r D hsum_n hmargins_n.1 hmargins_n.2

/-- The same scaling discharge applies directly to the actual compact `SU(N)`
midpoint Wilson covariance factors: eventually they depend only on their literal
left/right physical-link supports and those supports are separated by at least
`D` actual Wilson-plaquette-local steps. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_eventually_support_receipt_of_scaling
    (H : ℕ → ℕ)
    (N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach H latticeSpacing)
        atTop atTop)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 < r)
    (D : ℕ)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ) :
    ∀ᶠ n : ℕ in atTop,
      (∀ A B : PeriodicHypercubicEvenEdge (H n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ,
        (∀ e,
          e ∈
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
              (H n) latticeSpacing n J →
          A e = B e) →
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
            (H n) N latticeSpacing n J F A =
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftWilsonSourceObservable
            (H n) N latticeSpacing n J F B) ∧
      (∀ A B : PeriodicHypercubicEvenEdge (H n) →
          Matrix.specialUnitaryGroup (Fin N) ℂ,
        (∀ e,
          e ∈
            periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
              (H n) latticeSpacing n J r →
          A e = B e) →
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
            (H n) N latticeSpacing n J r F A =
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightWilsonSourceObservable
            (H n) N latticeSpacing n J r F B) ∧
      periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy (H n) D
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          (H n) latticeSpacing n J)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          (H n) latticeSpacing n J r) := by
  have hsum :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_eventually_floor_sum_ge_of_spacing_tendsto_zero
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero J hJ r hr D
  have hmargins :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_eventually_interior_margins_of_scaling
      H latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero hreach
      J hJ r hr.le D
  filter_upwards [hsum, hmargins] with n hsum_n hmargins_n
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointWilsonSourceCovariance_support_receipt_of_sum_ge_of_interior_margin
      (H n) N latticeSpacing n J hJ r hr.le D hsum_n
      hmargins_n.1 hmargins_n.2 F

end

end MathlibAnalytic
end MGAP4D
