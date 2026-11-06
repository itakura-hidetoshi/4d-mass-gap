import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixed24SignedGeometryObstructionV5_PZ37AGO
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGP — original source-adapted cellwise signed certificates

Retain the ORIGINAL continuous centered source f, Wilson kernel K,
spatial Haar and signed transfer. The true center-dependent slope is

  |g_B(A)-g_B(C)| <= (6*(1-k_H)+13*beta0*|f(C)|)*D_H(A,C).

Exact AGN centering bounds |f(C)| by p_H/2, improving AGG's uniform
source term. At rational-coordinate centers the source is evaluated
exactly; AGK coupling and AGN floor intervals give rational local slopes.

Each genuine cell may have its own certified rational radius. Expand
the actual center interval by that cell's local budget, then intersect
with the independently proved original global range BEFORE integrating.
AGN's generic signed Haar integration theorem applies with geometry zero
because the data already bounds every point of each actual cell. The old
AGI certifiedTable is neither changed nor weakened.

Fine rational-coordinate grids and accurate true Haar mass intervals
remain explicit proof-carrying inputs. This module does not claim to have
computed those inputs or to have separated an actual physical sign. It
does not contradict AGO's obstruction for the OLD fixed-24 evaluator.
No two-threshold shell, volume-uniform coercivity or continuum gap claim.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Rational source-sensitive slope; the supplied floor/coupling endpoints
will be certified against the original model below. -/
def p4Q2PZ37AGP_coefficient (floor beta source : ℚ) : ℚ :=
  6 * (1 - floor) + 13 * beta * |source|

/-- Synthetic arithmetic regression, NOT a physical sample. -/
theorem p4Q2PZ37AGP_coefficient_regression :
    p4Q2PZ37AGP_coefficient (1 / 2) (1 / 100) 0 = 3 ∧
      p4Q2PZ37AGP_coefficient 0 (1 / 100) (-12) = 189 / 25 := by
  norm_num [p4Q2PZ37AGP_coefficient]

/-- A finite rational radius sufficient for an arbitrary positive
geometric tolerance; no numerical density choice is involved. -/
theorem p4Q2PZ37AGP_radiusBudget (L U eps : ℚ)
    (hL : 0 ≤ L) (hLU : L ≤ U) (heps : 0 < eps) :
    0 < eps / (U + 1) ∧ L * (eps / (U + 1)) ≤ eps := by
  have hU : 0 ≤ U := hL.trans hLU
  have hden : 0 < U + 1 := by linarith only [hU]
  constructor
  · exact div_pos heps hden
  · calc
      L * (eps / (U + 1)) ≤ U * (eps / (U + 1)) :=
        mul_le_mul_of_nonneg_right hLU (div_nonneg heps.le hden.le)
      _ = (U * eps) / (U + 1) := by ring
      _ ≤ eps := (div_le_iff₀ hden).mpr (by nlinarith only [heps])

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGP_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGP_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGP_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGP_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGP_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "gCont" => p4Q2PZ37AGE_originalContinuousIntegrand H
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "kFloor" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0
  (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AGP_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGP_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

def p4Q2PZ37AGP_originalCenterSlope (C : Cfg) : ℝ :=
  6 * (1 - kFloor) + 13 * b0 * |fCont C|

/-- The source amplitude at the ACTUAL center replaces the old global
source envelope. The center need not lie inside its first-center cell. -/
theorem p4Q2PZ37AGP_originalCenterSlope_bound (B A C : Cfg) :
    |gCont B A - gCont B C| ≤
      p4Q2PZ37AGP_originalCenterSlope H C * Dsp A C := by
  let D := Dsp A C
  let r := (1 - kFloor) / 2
  have hd : 0 ≤ D := p4Q2PZ37AGG_originalSpatialChordalDistance_nonneg H A C
  have hs : |fCont A - fCont C| ≤ 12 * D :=
    p4Q2PZ37AGG_originalCenteredSource_allLinkChordalSlope H A C
  have hk : |K A B - K C B| ≤ (13 * b0) * D :=
    p4Q2PZ37AGG_originalKernel_leftAllLinkChordalSlope H B A C
  have hm : |K A B - (1 + kFloor) / 2| ≤ r :=
    p4Q2PZ37AGB_originalKernel_centeredMidpointBound H A B
  have h0 : 0 ≤ 12 * D := mul_nonneg (by norm_num) hd
  change |fCont A * (K A B - (1 + kFloor) / 2) -
    fCont C * (K C B - (1 + kFloor) / 2)| ≤
      (6 * (1 - kFloor) + 13 * b0 * |fCont C|) * D
  calc
    |fCont A * (K A B - (1 + kFloor) / 2) -
        fCont C * (K C B - (1 + kFloor) / 2)| =
      |(fCont A - fCont C) * (K A B - (1 + kFloor) / 2) +
        fCont C * (K A B - K C B)| := by congr 1; ring
    _ ≤ |fCont A - fCont C| * |K A B - (1 + kFloor) / 2| +
        |fCont C| * |K A B - K C B| := by
      simpa only [abs_mul] using
        (abs_add_le ((fCont A - fCont C) * (K A B - (1 + kFloor) / 2))
          (fCont C * (K A B - K C B)))
    _ ≤ (12 * D) * r + |fCont C| * ((13 * b0) * D) :=
      add_le_add (mul_le_mul hs hm (abs_nonneg _) h0)
        (mul_le_mul_of_nonneg_left hk (abs_nonneg _))
    _ = (6 * (1 - kFloor) + 13 * b0 * |fCont C|) * D := by
      dsimp [r]
      ring

/-- Exact centering halves the old worst-case source term. -/
theorem p4Q2PZ37AGP_originalCenterSlope_le_halfCount (C : Cfg) :
    p4Q2PZ37AGP_originalCenterSlope H C ≤
      6 * (1 - kFloor) + 13 * b0 * (pH / 2) := by
  have h := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H C)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) p4Q2PZ37ADC_fixedCoupling_pos.le)
  exact add_le_add (le_refl (6 * (1 - kFloor))) h

/-- The improved uniform analytic slope never exceeds the previous AGG slope. -/
theorem p4Q2PZ37AGP_halfCountSlope_le_AGG :
    6 * (1 - kFloor) + 13 * b0 * (pH / 2) ≤
      p4Q2PZ37AGG_originalSpatialSlope H := by
  have h := mul_nonneg (p4Q2PZ37AGF_plaquetteCount_nonneg H)
    p4Q2PZ37ADC_fixedCoupling_pos.le
  unfold p4Q2PZ37AGG_originalSpatialSlope
  nlinarith only [h]

/-- Exact source-center evaluation, refined genuine coupling and genuine
floor give a rational local slope with no unknown source-value oracle. -/
def p4Q2PZ37AGP_rationalCenterSlope (C : Cfg)
    (c : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (C e))
    (m n : ℕ) (hn : 0 < n) : ℚ :=
  p4Q2PZ37AGP_coefficient
    (p4Q2PZ37AGN_originalFloorInterval H m n hn).lower
    (p4Q2PZ37AGK_upper m) (p4Q2PZ37AGN_centeredSourceRational H C c)

theorem p4Q2PZ37AGP_rationalCenterSlope_nonneg (C : Cfg)
    (c : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (C e))
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AGP_rationalCenterSlope H C c m n hn := by
  have hfReal : ((p4Q2PZ37AGN_originalFloorInterval H m n hn).lower : ℝ) ≤ 1 :=
    (p4Q2PZ37AGN_originalFloorInterval H m n hn).hLower.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_one
        H b0 p4Q2PZ37ADC_fixedCoupling_pos.le)
  have hf : (p4Q2PZ37AGN_originalFloorInterval H m n hn).lower ≤ (1 : ℚ) := by
    exact_mod_cast hfReal
  have hbReal : (0 : ℝ) ≤ (p4Q2PZ37AGK_upper m : ℝ) :=
    p4Q2PZ37ADC_fixedCoupling_pos.le.trans (p4Q2PZ37AGK_originalCoupling_bounds m).2
  have hb : (0 : ℚ) ≤ p4Q2PZ37AGK_upper m := by exact_mod_cast hbReal
  unfold p4Q2PZ37AGP_rationalCenterSlope p4Q2PZ37AGP_coefficient
  exact add_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hf))
    (mul_nonneg (mul_nonneg (by norm_num) hb) (abs_nonneg _))

theorem p4Q2PZ37AGP_originalCenterSlope_le_rational (C : Cfg)
    (c : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (C e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGP_originalCenterSlope H C ≤
      (p4Q2PZ37AGP_rationalCenterSlope H C c m n hn : ℝ) := by
  have hf := (p4Q2PZ37AGN_originalFloorInterval H m n hn).hLower
  have hb := mul_le_mul_of_nonneg_right
    (p4Q2PZ37AGK_originalCoupling_bounds m).2 (abs_nonneg (fCont C))
  have hs := p4Q2PZ37AGN_centeredSourceRational_exact H C c
  unfold p4Q2PZ37AGP_originalCenterSlope p4Q2PZ37AGP_rationalCenterSlope
    p4Q2PZ37AGP_coefficient
  push_cast
  rw [← hs]
  nlinarith only [hf, hb]

/-- A B-independent rational cap for every rational center, useful for
choosing a small radius before enumerating its genuine cells. -/
theorem p4Q2PZ37AGP_rationalCenterSlope_le_uniform (C : Cfg)
    (c : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (C e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGP_rationalCenterSlope H C c m n hn ≤
      6 + 13 * p4Q2PZ37AGK_upper m * (p4Q2PZ37AGN_countRational H / 2) := by
  have hf : (0 : ℚ) ≤ (p4Q2PZ37AGN_originalFloorInterval H m n hn).lower :=
    le_max_right _ _
  have hbReal : (0 : ℝ) ≤ (p4Q2PZ37AGK_upper m : ℝ) :=
    p4Q2PZ37ADC_fixedCoupling_pos.le.trans (p4Q2PZ37AGK_originalCoupling_bounds m).2
  have hb : (0 : ℚ) ≤ p4Q2PZ37AGK_upper m := by exact_mod_cast hbReal
  have hsReal := p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H C
  rw [p4Q2PZ37AGN_centeredSourceRational_exact H C c,
    ← p4Q2PZ37AGN_countRational_exact H] at hsReal
  have hs : |p4Q2PZ37AGN_centeredSourceRational H C c| ≤
      p4Q2PZ37AGN_countRational H / 2 := by exact_mod_cast hsReal
  have hmul := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (by norm_num : (0 : ℚ) ≤ 13) hb)
  unfold p4Q2PZ37AGP_rationalCenterSlope p4Q2PZ37AGP_coefficient
  linarith only [hf, hmul]

/-- Genuine cell geometry supplies the only radius premise in this local
estimate. Neither an independent oscillation oracle nor a global source
amplitude is required. -/
theorem p4Q2PZ37AGP_originalLocalOscillation (B A C : Cfg)
    (c : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (C e))
    (m n : ℕ) (hn : 0 < n) (r : ℚ) (hr : Dsp A C ≤ (r : ℝ)) :
    |gCont B A - gCont B C| ≤
      ((p4Q2PZ37AGP_rationalCenterSlope H C c m n hn * r : ℚ) : ℝ) := by
  have hnonneg : (0 : ℝ) ≤
      (p4Q2PZ37AGP_rationalCenterSlope H C c m n hn : ℝ) := by
    exact_mod_cast p4Q2PZ37AGP_rationalCenterSlope_nonneg H C c m n hn
  have h := mul_le_mul
    (p4Q2PZ37AGP_originalCenterSlope_le_rational H C c m n hn) hr
    (p4Q2PZ37AGG_originalSpatialChordalDistance_nonneg H A C) hnonneg
  have hh := (p4Q2PZ37AGP_originalCenterSlope_bound H B A C).trans h
  simpa only [Rat.cast_mul] using hh

/-- A radius for each genuine cell, allowing nonuniform refinement.
No requirement that a designated center belongs to its own cell. -/
structure p4Q2PZ37AGP_cellRadii (H : ℕ)
    (grid : p4Q2PZ37AGH_originalSpatialGrid H) where
  radius : Fin grid.n → ℚ
  nonneg : ∀ i, 0 ≤ radius i
  hRadius : ∀ i A, A ∈ grid.cell i →
    p4Q2PZ37AGG_originalSpatialChordalDistance H A (grid.center i) ≤ (radius i : ℝ)

def p4Q2PZ37AGP_cellRadii_ofUniform
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (r : ℚ) (hr : 0 ≤ r) (hCover : grid.radius ≤ (r : ℝ)) :
    p4Q2PZ37AGP_cellRadii H grid where
  radius := fun _ => r
  nonneg := fun _ => hr
  hRadius := fun i A hA => (grid.hRadius i A hA).trans hCover

/-- Actual model evidence remains explicit: arbitrary fine rational-center
geometry and accurate original Haar masses are NOT presumed computed. -/
structure p4Q2PZ37AGP_gridData (H : ℕ) where
  grid : p4Q2PZ37AGH_originalSpatialGrid H
  centerCoordinates : ∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e)
  radii : p4Q2PZ37AGP_cellRadii H grid
  masses : p4Q2PZ37AGN_massIntervals grid

/-- Existing 24-center data is one valid instance, but is NOT the only
permitted grid. Its existence does not imply a nonzero signed certificate. -/
def p4Q2PZ37AGP_original24Data : p4Q2PZ37AGP_gridData H where
  grid := p4Q2PZ37AGN_original24Grid H
  centerCoordinates := p4Q2PZ37AGN_original24Center_rational H
  radii := p4Q2PZ37AGP_cellRadii_ofUniform H _ (p4Q2PZ37AGN_original24Radius H)
    (by unfold p4Q2PZ37AGN_original24Radius; positivity)
    (p4Q2PZ37AGN_original24Radius_exact H).symm.le
  masses := p4Q2PZ37AGN_original24MassIntervals H

variable (d : p4Q2PZ37AGP_gridData H)

def p4Q2PZ37AGP_cellBudget (m n : ℕ) (hn : 0 < n) (i : Fin d.grid.n) : ℚ :=
  p4Q2PZ37AGP_rationalCenterSlope H (d.grid.center i)
    (d.centerCoordinates i) m n hn * d.radii.radius i

theorem p4Q2PZ37AGP_cellBudget_nonneg (m n : ℕ) (hn : 0 < n) (i : Fin d.grid.n) :
    0 ≤ p4Q2PZ37AGP_cellBudget H d m n hn i :=
  mul_nonneg (p4Q2PZ37AGP_rationalCenterSlope_nonneg H (d.grid.center i)
    (d.centerCoordinates i) m n hn) (d.radii.nonneg i)

def p4Q2PZ37AGP_cellLower (B : Cfg)
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.grid.n) : ℚ :=
  max (-p4Q2PZ37AGN_transferRadius H m n hn)
    ((p4Q2PZ37AGN_originalIntegrandInterval H (d.grid.center i) B
      (d.centerCoordinates i) b m n hn).lower - p4Q2PZ37AGP_cellBudget H d m n hn i)

def p4Q2PZ37AGP_cellUpper (B : Cfg)
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.grid.n) : ℚ :=
  min (p4Q2PZ37AGN_transferRadius H m n hn)
    ((p4Q2PZ37AGN_originalIntegrandInterval H (d.grid.center i) B
      (d.centerCoordinates i) b m n hn).upper + p4Q2PZ37AGP_cellBudget H d m n hn i)

/-- Both local geometry and the independent global original range apply
pointwise on every actual cell, including empty first-center cells. -/
theorem p4Q2PZ37AGP_originalCell_bounds (B : Cfg)
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.grid.n) (A : Cfg) (hA : A ∈ d.grid.cell i) :
    (p4Q2PZ37AGP_cellLower H d B b m n hn i : ℝ) ≤ gCont B A ∧
      gCont B A ≤ (p4Q2PZ37AGP_cellUpper H d B b m n hn i : ℝ) := by
  let c := p4Q2PZ37AGN_originalIntegrandInterval H (d.grid.center i) B
    (d.centerCoordinates i) b m n hn
  have hOsc : |gCont B A - gCont B (d.grid.center i)| ≤
      (p4Q2PZ37AGP_cellBudget H d m n hn i : ℝ) :=
    p4Q2PZ37AGP_originalLocalOscillation H B A (d.grid.center i)
      (d.centerCoordinates i) m n hn (d.radii.radius i) (d.radii.hRadius i A hA)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hOsc
  have hLower : ((c.lower - p4Q2PZ37AGP_cellBudget H d m n hn i : ℚ) : ℝ) ≤
      gCont B A := by
    push_cast
    linarith only [c.hLower, hlo]
  have hUpper : gCont B A ≤
      ((c.upper + p4Q2PZ37AGP_cellBudget H d m n hn i : ℚ) : ℝ) := by
    push_cast
    linarith only [c.hUpper, hhi]
  have hGlobal := abs_le.mp (p4Q2PZ37AGO_originalIntegrand_abs_le_radius H B A m n hn)
  constructor
  · simpa [p4Q2PZ37AGP_cellLower, c] using max_le hGlobal.1 hLower
  · simpa [p4Q2PZ37AGP_cellUpper, c] using le_min hGlobal.2 hUpper

/-- AGI's signed min/max evaluator is reused on ALREADY certified cell
values. Its old center-geometry certificate is not weakened or redefined. -/
def p4Q2PZ37AGP_originalTable (B : Cfg)
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : p4Q2PZ37AGI_rationalTable d.grid.n :=
  d.masses.toTable (p4Q2PZ37AGP_cellLower H d B b m n hn)
    (p4Q2PZ37AGP_cellUpper H d B b m n hn) 0

/-- Soundness for the SAME signed transfer and SAME original Haar law. -/
theorem p4Q2PZ37AGP_originalTransfer_bounds (B : Cfg)
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    ((p4Q2PZ37AGP_originalTable H d B b m n hn).lower : ℝ) ≤ t B ∧
      t B ≤ ((p4Q2PZ37AGP_originalTable H d B b m n hn).upper : ℝ) := by
  have hi : Integrable (gCont B) muH :=
    (p4Q2PZ37AGC_originalCenteredKernelIntegrand_integrable B).congr
      (p4Q2PZ37AGE_originalIntegrand_ae_eq_continuous H B)
  have h := d.masses.integral_bounds
    (p4Q2PZ37AGP_cellLower H d B b m n hn)
    (p4Q2PZ37AGP_cellUpper H d B b m n hn) 0 (gCont B) hi (by
      intro i A hA
      simpa only [p4Q2PZ37AGN_massIntervals.toTable,
        p4Q2PZ37AGI_rationalTable.cellLower, p4Q2PZ37AGI_rationalTable.cellUpper,
        sub_zero, add_zero] using
        p4Q2PZ37AGP_originalCell_bounds H d B b m n hn i A hA)
  rw [p4Q2PZ37AGE_originalContinuousIntegral_eq_transfer H B] at h
  exact h

def p4Q2PZ37AGP_originalRawInterval (B : Cfg)
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : p4Q2PZ37AFV_verifiedInterval (t B) where
  lower := (p4Q2PZ37AGP_originalTable H d B b m n hn).lower
  upper := (p4Q2PZ37AGP_originalTable H d B b m n hn).upper
  hLower := (p4Q2PZ37AGP_originalTransfer_bounds H d B b m n hn).1
  hUpper := (p4Q2PZ37AGP_originalTransfer_bounds H d B b m n hn).2

/-- Retain every earlier certificate of this exact same physical value.
No previously certified interval is overwritten or widened. -/
def p4Q2PZ37AGP_originalTightenedInterval (B : Cfg)
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (previous : p4Q2PZ37AFV_verifiedInterval (t B)) :
    p4Q2PZ37AFV_verifiedInterval (t B) :=
  p4Q2PZ37AGN_intersectInterval (p4Q2PZ37AGP_originalRawInterval H d B b m n hn) previous

theorem p4Q2PZ37AGP_originalTightenedInterval_subset (B : Cfg)
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (previous : p4Q2PZ37AFV_verifiedInterval (t B)) :
    previous.lower ≤ (p4Q2PZ37AGP_originalTightenedInterval H d B b m n hn previous).lower ∧
      (p4Q2PZ37AGP_originalTightenedInterval H d B b m n hn previous).upper ≤ previous.upper :=
  ⟨le_max_right _ _, min_le_right _ _⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGP_coefficient_regression
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGP_radiusBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_originalCenterSlope_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_originalCenterSlope_le_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_halfCountSlope_le_AGG
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_rationalCenterSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_originalCenterSlope_le_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_rationalCenterSlope_le_uniform
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_originalLocalOscillation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_cellRadii_ofUniform
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_original24Data
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_cellBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_originalCell_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_originalTransfer_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_originalRawInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_originalTightenedInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGP_originalTightenedInterval_subset
