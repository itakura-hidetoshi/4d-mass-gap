import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTrueHaarMidpointSignBudgetV5_PZ37AHE
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHF — original 24-center sign obstruction and required refinement

AHE supplied sound rational sign checkers, but no accepting physical data.
This leaf examines their LITERAL original AGP 24-center instantiation.
Write p for the original plaquette count, delta=1-floor.lower and
M=p*delta/4 for the unchanged AGN transfer radius. The original AGP
source-adapted slope is at least 6*delta, independently of both orders.

* If every supplied original cell radius is >= p/24, EVERY cell interval
  straddles zero, hence both original AHE sign checkers return false.
* If every radius is >= p/12, EVERY clipped AGP cell interval is exactly
  [-M,M]. Normalization of the TRUE Haar masses implies that the raw AGP
  table spans [-M,M], and intersection with AGN returns exactly [-M,M].
* In the actual three-dimensional spatial slice, p equals the number of
  original positive links. Thus the literal original24 radius is 4*p/5,
  larger than both thresholds for EVERY H. No boundary or Taylor/coupling
  order can make its AHE checker accept. Even independently improved
  sound Haar mass intervals on those SAME cells do not repair this.
* An accepting original AGP table must have SOME certified radius < p/24;
  an accepting uniform AGU precision table must have R < p/24.

This is a proved obstruction of this enclosure, NOT a proof that the
original physical transfer is zero. It does not rule out finer original
cells or sharper original-source estimates. No source, Wilson action,
kernel, floor, measure, old certificate, root or pin is replaced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHF_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHF_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHF_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHF_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHF_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AGN_countRational H
local notation "t" => decomposableOneSliceTransferIntegral H 2
  p4Q2PZ37ADC_fixedCoupling (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AHF_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHF_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Both actual spatial carriers have three choices at each vertex:
three directions and three increasing direction pairs. No volume or
nondegeneracy assumption is introduced. -/
theorem p4Q2PZ37AHF_count_eq_links :
    pH = (Fintype.card Link : ℚ) := by
  have hDirs : Fintype.card PeriodicHypercubicEvenSpatialDirectionPair =
      Fintype.card PeriodicHypercubicEvenSpatialDirection := by decide
  let e : PeriodicHypercubicEvenSpatialSlicePlaquette H ≃ Link :=
    Equiv.prodCongr (Equiv.refl (PeriodicHypercubicEvenSpatialSliceVertex H))
      (Fintype.equivOfCardEq hDirs)
  have hCard := Nat.card_congr e
  unfold p4Q2PZ37AGN_countRational periodicHypercubicEvenSpatialSlicePlaquetteList
  simp only [Finset.length_toList, Finset.card_univ, Fintype.card_eq_nat_card]
  exact_mod_cast hCard

/-- The genuine rational floor lower endpoint cannot exceed one. -/
theorem p4Q2PZ37AHF_floorDeficit_nonneg
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ 1 - (p4Q2PZ37AGN_originalFloorInterval H m n hn).lower := by
  have hReal : ((p4Q2PZ37AGN_originalFloorInterval H m n hn).lower : ℝ) ≤ 1 :=
    (p4Q2PZ37AGN_originalFloorInterval H m n hn).hLower.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_one
        H p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le)
  have hRat : (p4Q2PZ37AGN_originalFloorInterval H m n hn).lower ≤ (1 : ℚ) := by
    exact_mod_cast hReal
  exact sub_nonneg.mpr hRat

/-- Source adaptation cannot remove the original 6*(1-floor.lower)
part of the actual AGP slope. -/
theorem p4Q2PZ37AHF_rationalCenterSlope_ge_floor
    (C : Cfg) (c : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (C e))
    (m n : ℕ) (hn : 0 < n) :
    6 * (1 - (p4Q2PZ37AGN_originalFloorInterval H m n hn).lower) ≤
      p4Q2PZ37AGP_rationalCenterSlope H C c m n hn := by
  have hbReal : (0 : ℝ) ≤ (p4Q2PZ37AGK_upper m : ℝ) :=
    p4Q2PZ37ADC_fixedCoupling_pos.le.trans (p4Q2PZ37AGK_originalCoupling_bounds m).2
  have hb : (0 : ℚ) ≤ p4Q2PZ37AGK_upper m := by exact_mod_cast hbReal
  have hTerm : 0 ≤ 13 * p4Q2PZ37AGK_upper m *
      |p4Q2PZ37AGN_centeredSourceRational H C c| :=
    mul_nonneg (mul_nonneg (by norm_num) hb) (abs_nonneg _)
  unfold p4Q2PZ37AGP_rationalCenterSlope p4Q2PZ37AGP_coefficient
  linarith only [hTerm]

/-- Radius >= k*p/24 forces the ORIGINAL cell budget >= k*M.
This works also when the floor deficit is zero; no division by it occurs. -/
theorem p4Q2PZ37AHF_cellBudget_ge_multipleRadius
    (d : p4Q2PZ37AGP_gridData H) (m n : ℕ) (hn : 0 < n)
    (i : Fin d.grid.n) (k : ℚ)
    (hRadius : k * pH / 24 ≤ d.radii.radius i) :
    k * p4Q2PZ37AGN_transferRadius H m n hn ≤
      p4Q2PZ37AGP_cellBudget H d m n hn i := by
  have hDeficit := p4Q2PZ37AHF_floorDeficit_nonneg H m n hn
  have hSlope := p4Q2PZ37AHF_rationalCenterSlope_ge_floor H
    (d.grid.center i) (d.centerCoordinates i) m n hn
  have hProduct := mul_le_mul_of_nonneg_right hSlope (d.radii.nonneg i)
  have hMesh := mul_le_mul_of_nonneg_left hRadius
    (mul_nonneg (by norm_num : (0 : ℚ) ≤ 6) hDeficit)
  unfold p4Q2PZ37AGN_transferRadius p4Q2PZ37AGP_cellBudget
  nlinarith only [hProduct, hMesh]

/-- Sound center endpoints obey the original global pointwise range.
Only the two directions needed for the obstruction are asserted. -/
theorem p4Q2PZ37AHF_originalCenter_partial_bounds
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.grid.n) :
    (p4Q2PZ37AGN_originalIntegrandInterval H (d.grid.center i) B
      (d.centerCoordinates i) b m n hn).lower ≤ p4Q2PZ37AGN_transferRadius H m n hn ∧
    -p4Q2PZ37AGN_transferRadius H m n hn ≤
      (p4Q2PZ37AGN_originalIntegrandInterval H (d.grid.center i) B
        (d.centerCoordinates i) b m n hn).upper := by
  let c := p4Q2PZ37AGN_originalIntegrandInterval H (d.grid.center i) B
    (d.centerCoordinates i) b m n hn
  have hPoint := abs_le.mp
    (p4Q2PZ37AGO_originalIntegrand_abs_le_radius H B (d.grid.center i) m n hn)
  constructor
  · have h : (c.lower : ℝ) ≤ (p4Q2PZ37AGN_transferRadius H m n hn : ℝ) :=
      c.hLower.trans hPoint.2
    exact_mod_cast h
  · have h : (-(p4Q2PZ37AGN_transferRadius H m n hn : ℝ)) ≤ (c.upper : ℝ) :=
      hPoint.1.trans c.hUpper
    exact_mod_cast h

/-- The p/24 threshold already destroys both strict signs on each
original cell, without asserting that its physical integrand is zero. -/
theorem p4Q2PZ37AHF_originalCell_contains_zero
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.grid.n)
    (hRadius : pH / 24 ≤ d.radii.radius i) :
    p4Q2PZ37AGP_cellLower H d B b m n hn i ≤ 0 ∧
      0 ≤ p4Q2PZ37AGP_cellUpper H d B b m n hn i := by
  have hM := p4Q2PZ37AGV_transferRadius_nonneg H m n hn
  have hBudget := p4Q2PZ37AHF_cellBudget_ge_multipleRadius H d m n hn i 1
    (by simpa only [one_mul] using hRadius)
  simp only [one_mul] at hBudget
  have hCenter := p4Q2PZ37AHF_originalCenter_partial_bounds H d B b m n hn i
  constructor
  · unfold p4Q2PZ37AGP_cellLower
    apply max_le
    · exact neg_nonpos.mpr hM
    · linarith only [hCenter.1, hBudget]
  · unfold p4Q2PZ37AGP_cellUpper
    apply le_min
    · exact hM
    · linarith only [hCenter.2, hBudget]

/-- All actual Haar upper mass endpoints are nonnegative, even when
lower endpoints are negative. -/
theorem p4Q2PZ37AHF_originalMassUpper_nonneg
    (d : p4Q2PZ37AGP_gridData H) (i : Fin d.grid.n) :
    0 ≤ d.masses.upper i := by
  have hReal : (0 : ℝ) ≤ (d.masses.upper i : ℝ) :=
    (measureReal_nonneg : 0 ≤ Measure.real muH (d.grid.cell i)).trans
      (d.masses.hUpper i)
  exact_mod_cast hReal

/-- Every coarse original cell straddles zero, so the exact signed
min/max AGP table also straddles zero, on ANY sound original Haar data. -/
theorem p4Q2PZ37AHF_originalTable_straddles
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hRadius : ∀ i, pH / 24 ≤ d.radii.radius i) :
    (p4Q2PZ37AGP_originalTable H d B b m n hn).lower ≤ 0 ∧
      0 ≤ (p4Q2PZ37AGP_originalTable H d B b m n hn).upper := by
  let tbl := p4Q2PZ37AGP_originalTable H d B b m n hn
  have hCell (i : Fin d.grid.n) : tbl.cellLower i ≤ 0 ∧ 0 ≤ tbl.cellUpper i := by
    simpa only [tbl, p4Q2PZ37AGP_originalTable, p4Q2PZ37AGN_massIntervals.toTable,
      p4Q2PZ37AGI_rationalTable.cellLower, p4Q2PZ37AGI_rationalTable.cellUpper,
      sub_zero, add_zero] using
      p4Q2PZ37AHF_originalCell_contains_zero H d B b m n hn i (hRadius i)
  have hMass (i : Fin d.grid.n) : 0 ≤ tbl.massUpper i :=
    p4Q2PZ37AHF_originalMassUpper_nonneg H d i
  change tbl.lower ≤ 0 ∧ 0 ≤ tbl.upper
  constructor
  · unfold p4Q2PZ37AGI_rationalTable.lower
    apply Finset.sum_nonpos
    intro i _hi
    exact (min_le_right _ _).trans
      (mul_nonpos_of_nonpos_of_nonneg (hCell i).1 (hMass i))
  · unfold p4Q2PZ37AGI_rationalTable.upper
    apply Finset.sum_nonneg
    intro i _hi
    exact (mul_nonneg (hCell i).2 (hMass i)).trans (le_max_right _ _)

/-- Both literal AHE Boolean checkers must reject all-radius>=p/24 data. -/
theorem p4Q2PZ37AHF_originalChecks_reject
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hRadius : ∀ i, pH / 24 ≤ d.radii.radius i) :
    p4Q2PZ37AHE_originalPositiveCheck H d B b m n hn = false ∧
      p4Q2PZ37AHE_originalNegativeCheck H d B b m n hn = false := by
  have hZero := p4Q2PZ37AHF_originalTable_straddles H d B b m n hn hRadius
  have hMass := p4Q2PZ37AHE_originalTable_massOrdered H d B b m n hn
  constructor
  · cases hc : p4Q2PZ37AHE_originalPositiveCheck H d B b m n hn with
    | false => rfl
    | true =>
      have hp := (p4Q2PZ37AHE_positiveCheck_iff _ hMass).mp hc
      exact ((not_lt_of_ge hZero.1) hp).elim
  · cases hc : p4Q2PZ37AHE_originalNegativeCheck H d B b m n hn with
    | false => rfl
    | true =>
      have hn' := (p4Q2PZ37AHE_negativeCheck_iff _ hMass).mp hc
      exact ((not_lt_of_ge hZero.2) hn').elim

/-- A necessary, NOT sufficient, geometric condition for an actual
accepting signed physical certificate. -/
theorem p4Q2PZ37AHF_accepting_requires_small_cell
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hAccept : p4Q2PZ37AHE_originalPositiveCheck H d B b m n hn = true ∨
      p4Q2PZ37AHE_originalNegativeCheck H d B b m n hn = true) :
    ∃ i : Fin d.grid.n, d.radii.radius i < pH / 24 := by
  by_contra hNo
  have hRadius : ∀ i, pH / 24 ≤ d.radii.radius i := by
    intro i
    exact le_of_not_gt (fun hi => hNo ⟨i, hi⟩)
  obtain ⟨hp, hn'⟩ := p4Q2PZ37AHF_originalChecks_reject H d B b m n hn hRadius
  rcases hAccept with h | h
  · rw [hp] at h
    cases h
  · rw [hn'] at h
    cases h

/-- In the original AGU indexed uniform geometry, strict acceptance
requires R<p/24, independently of the Haar mass precision eps. -/
theorem p4Q2PZ37AHF_precision_accepting_radius_lt
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hAccept : p4Q2PZ37AHE_originalPositiveCheck H d.data B b m n hn = true ∨
      p4Q2PZ37AHE_originalNegativeCheck H d.data B b m n hn = true) :
    R < pH / 24 := by
  obtain ⟨i, hi⟩ := p4Q2PZ37AHF_accepting_requires_small_cell H d.data B b m n hn hAccept
  rw [d.hCellRadius i] at hi
  exact hi

/-- At the larger p/12 threshold the actual clipped cell interval is
EXACTLY the full original global interval, not merely zero-straddling. -/
theorem p4Q2PZ37AHF_originalCell_saturates
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.grid.n)
    (hRadius : pH / 12 ≤ d.radii.radius i) :
    p4Q2PZ37AGP_cellLower H d B b m n hn i = -p4Q2PZ37AGN_transferRadius H m n hn ∧
      p4Q2PZ37AGP_cellUpper H d B b m n hn i = p4Q2PZ37AGN_transferRadius H m n hn := by
  have hBudget := p4Q2PZ37AHF_cellBudget_ge_multipleRadius H d m n hn i 2
    (by linarith only [hRadius])
  have hCenter := p4Q2PZ37AHF_originalCenter_partial_bounds H d B b m n hn i
  constructor
  · unfold p4Q2PZ37AGP_cellLower
    apply max_eq_left
    linarith only [hCenter.1, hBudget]
  · unfold p4Q2PZ37AGP_cellUpper
    apply min_eq_left
    linarith only [hCenter.2, hBudget]

/-- True Haar normalization supplies sum upper>=1 on ANY original grid;
the rational endpoint vector is not artificially normalized. -/
theorem p4Q2PZ37AHF_originalMassUpper_total_ge_one
    (d : p4Q2PZ37AGP_gridData H) :
    (1 : ℚ) ≤ ∑ i : Fin d.grid.n, d.masses.upper i := by
  have hReal : (1 : ℝ) ≤ ∑ i : Fin d.grid.n, (d.masses.upper i : ℝ) := by
    calc
      (1 : ℝ) = ∑ i : Fin d.grid.n, Measure.real muH (d.grid.cell i) :=
        d.masses.total_mass.symm
      _ ≤ ∑ i : Fin d.grid.n, (d.masses.upper i : ℝ) := by
        exact Finset.sum_le_sum (fun i _hi => d.masses.hUpper i)
  exact_mod_cast hReal

/-- Saturated original cells force the SAME original raw AGP table to
span the full independently certified symmetric global range. -/
theorem p4Q2PZ37AHF_originalTable_spans_global
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hRadius : ∀ i, pH / 12 ≤ d.radii.radius i) :
    (p4Q2PZ37AGP_originalTable H d B b m n hn).lower ≤ -p4Q2PZ37AGN_transferRadius H m n hn ∧
      p4Q2PZ37AGN_transferRadius H m n hn ≤
        (p4Q2PZ37AGP_originalTable H d B b m n hn).upper := by
  let M := p4Q2PZ37AGN_transferRadius H m n hn
  let tbl := p4Q2PZ37AGP_originalTable H d B b m n hn
  have hM : 0 ≤ M := p4Q2PZ37AGV_transferRadius_nonneg H m n hn
  have hCell (i : Fin d.grid.n) : tbl.cellLower i = -M ∧ tbl.cellUpper i = M := by
    simpa only [tbl, p4Q2PZ37AGP_originalTable, p4Q2PZ37AGN_massIntervals.toTable,
      p4Q2PZ37AGI_rationalTable.cellLower, p4Q2PZ37AGI_rationalTable.cellUpper,
      sub_zero, add_zero] using
      p4Q2PZ37AHF_originalCell_saturates H d B b m n hn i (hRadius i)
  have hSum : (1 : ℚ) ≤ ∑ i : Fin d.grid.n, tbl.massUpper i :=
    p4Q2PZ37AHF_originalMassUpper_total_ge_one H d
  have hLo : tbl.lower ≤ ∑ i : Fin d.grid.n, (-M) * tbl.massUpper i := by
    unfold p4Q2PZ37AGI_rationalTable.lower
    apply Finset.sum_le_sum
    intro i _hi
    rw [(hCell i).1]
    exact min_le_right _ _
  have hHi : (∑ i : Fin d.grid.n, M * tbl.massUpper i) ≤ tbl.upper := by
    unfold p4Q2PZ37AGI_rationalTable.upper
    apply Finset.sum_le_sum
    intro i _hi
    rw [(hCell i).2]
    exact le_max_right _ _
  constructor
  · calc
      tbl.lower ≤ ∑ i : Fin d.grid.n, (-M) * tbl.massUpper i := hLo
      _ = (-M) * (∑ i : Fin d.grid.n, tbl.massUpper i) := by rw [Finset.mul_sum]
      _ ≤ (-M) * 1 := mul_le_mul_of_nonpos_left hSum (neg_nonpos.mpr hM)
      _ = -M := by ring
  · calc
      M = M * 1 := by ring
      _ ≤ M * (∑ i : Fin d.grid.n, tbl.massUpper i) := mul_le_mul_of_nonneg_left hSum hM
      _ = ∑ i : Fin d.grid.n, M * tbl.massUpper i := by rw [Finset.mul_sum]
      _ ≤ tbl.upper := hHi

/-- Intersecting this original raw table with AGN's symmetric global
interval returns exactly that global interval. -/
theorem p4Q2PZ37AHF_originalInterval_collapses
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hRadius : ∀ i, pH / 12 ≤ d.radii.radius i) :
    (p4Q2PZ37AGP_originalTightenedInterval H d B b m n hn
      (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)).lower =
        -p4Q2PZ37AGN_transferRadius H m n hn ∧
    (p4Q2PZ37AGP_originalTightenedInterval H d B b m n hn
      (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)).upper =
        p4Q2PZ37AGN_transferRadius H m n hn := by
  have hRaw := p4Q2PZ37AHF_originalTable_spans_global H d B b m n hn hRadius
  exact p4Q2PZ37AGO_intersection_collapses
    (p4Q2PZ37AGP_originalRawInterval H d B b m n hn)
    (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)
    (p4Q2PZ37AGN_transferRadius H m n hn) ⟨rfl, rfl⟩ hRaw.1 hRaw.2

/-- The actual existing original24 radius is 4*p/5, not a chosen
replacement geometry or an external numerical assumption. -/
theorem p4Q2PZ37AHF_original24_cellRadius_exact
    (i : Fin (p4Q2PZ37AGP_original24Data H).grid.n) :
    (p4Q2PZ37AGP_original24Data H).radii.radius i = (4 / 5 : ℚ) * pH := by
  change (4 / 5 : ℚ) * Fintype.card Link = (4 / 5 : ℚ) * pH
  rw [p4Q2PZ37AHF_count_eq_links H]

/-- The original24 geometry unconditionally exceeds the saturation
threshold at EVERY finite volume. -/
theorem p4Q2PZ37AHF_original24_radius_ge_threshold
    (i : Fin (p4Q2PZ37AGP_original24Data H).grid.n) :
    pH / 12 ≤ (p4Q2PZ37AGP_original24Data H).radii.radius i := by
  rw [p4Q2PZ37AHF_original24_cellRadius_exact H i]
  have hp : (0 : ℚ) ≤ pH := by unfold p4Q2PZ37AGN_countRational; positivity
  linarith only [hp]

/-- Concrete negative result for AHE's literal original24 checkers:
BOTH return false for ALL original rational boundaries and ALL orders. -/
theorem p4Q2PZ37AHF_original24_checks_reject
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AHE_original24PositiveCheck H B b m n hn = false ∧
      p4Q2PZ37AHE_original24NegativeCheck H B b m n hn = false := by
  apply p4Q2PZ37AHF_originalChecks_reject H (p4Q2PZ37AGP_original24Data H) B b m n hn
  intro i
  have hi := p4Q2PZ37AHF_original24_radius_ge_threshold H i
  have hp : (0 : ℚ) ≤ pH := by unfold p4Q2PZ37AGN_countRational; positivity
  linarith only [hi, hp]

/-- The actual source-adapted original24 enclosure, not merely the
older AGN uniform-slope table, collapses to its symmetric global bound. -/
theorem p4Q2PZ37AHF_original24_interval_collapses
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGP_originalTightenedInterval H (p4Q2PZ37AGP_original24Data H) B b m n hn
      (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)).lower =
        -p4Q2PZ37AGN_transferRadius H m n hn ∧
    (p4Q2PZ37AGP_originalTightenedInterval H (p4Q2PZ37AGP_original24Data H) B b m n hn
      (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)).upper =
        p4Q2PZ37AGN_transferRadius H m n hn :=
  p4Q2PZ37AHF_originalInterval_collapses H (p4Q2PZ37AGP_original24Data H) B b m n hn
    (p4Q2PZ37AHF_original24_radius_ge_threshold H)

/-- Better TRUE Haar masses on the SAME original cells and radii cannot
repair the obstruction. This does not change the Haar law or its cells. -/
theorem p4Q2PZ37AHF_original24_refinedMasses_checks_reject
    (mass : p4Q2PZ37AGN_massIntervals (p4Q2PZ37AGN_original24Grid H))
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    let d : p4Q2PZ37AGP_gridData H := { p4Q2PZ37AGP_original24Data H with masses := mass }
    p4Q2PZ37AHE_originalPositiveCheck H d B b m n hn = false ∧
      p4Q2PZ37AHE_originalNegativeCheck H d B b m n hn = false := by
  dsimp only
  apply p4Q2PZ37AHF_originalChecks_reject
  intro i
  change pH / 24 ≤ (p4Q2PZ37AGP_original24Data H).radii.radius i
  have hi := p4Q2PZ37AHF_original24_radius_ge_threshold H i
  have hp : (0 : ℚ) ≤ pH := by unfold p4Q2PZ37AGN_countRational; positivity
  linarith only [hi, hp]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_count_eq_links
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_floorDeficit_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_rationalCenterSlope_ge_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_cellBudget_ge_multipleRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_originalCenter_partial_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_originalCell_contains_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_originalMassUpper_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_originalTable_straddles
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_originalChecks_reject
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_accepting_requires_small_cell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_precision_accepting_radius_lt
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_originalCell_saturates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_originalMassUpper_total_ge_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_originalTable_spans_global
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_originalInterval_collapses
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_original24_cellRadius_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_original24_radius_ge_threshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_original24_checks_reject
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_original24_interval_collapses
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHF_original24_refinedMasses_checks_reject
