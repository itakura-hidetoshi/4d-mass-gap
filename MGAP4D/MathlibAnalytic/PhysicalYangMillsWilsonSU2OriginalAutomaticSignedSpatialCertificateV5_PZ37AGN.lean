import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExactWilsonHaarMeanV5_PZ37AGN
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHaarMeanEnclosureV5_PZ37AGN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGN — automatic signed intervals for original spatial transfer

The original Haar mean is the actual plaquette count, proved using the
four distinct original links of each plaquette. Thus the original
continuous centered source has an EXACT rational value at every
rational-coordinate configuration. Combine it with AGM's genuine
kernel intervals, an automatically scaled interval for the ORIGINAL
global action floor, AGD's true Haar product masses, and AGG's original
spatial slope. This constructs all of AGI's certificate fields for every
original AFQ 24-center boundary; no center-value, mean, mass or geometry
oracle is left for this fixed grid.

Intersect the resulting signed transfer enclosure with the independently
proved original global range. Exact centering improves the source bound
from p_H to p_H/2 and the transfer bound from p_H/2 to p_H/4. The floor
interval further tightens this rational radius without changing the
original source, kernel, Haar law, transfer, aggregation root or pins.

The canonical finite enumerations remain noncomputable. No large-volume
table has been evaluated and no actual nonzero signed transfer, two-sign
shell, uniform coercivity, Hamiltonian or continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Intersection retains both proved enclosures of the same real value. -/
def p4Q2PZ37AGN_intersectInterval {x : ℝ}
    (a b : p4Q2PZ37AFV_verifiedInterval x) :
    p4Q2PZ37AFV_verifiedInterval x where
  lower := max a.lower b.lower
  upper := min a.upper b.upper
  hLower := by simpa using max_le a.hLower b.hLower
  hUpper := by simpa using le_min a.hUpper b.hUpper

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGN_auto_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGN_auto_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGN_auto_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGN_auto_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGN_auto_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Wc" => p4Q2JI_actualSpatialWilsonContinuous H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "gCont" => p4Q2PZ37AGE_originalContinuousIntegrand H
local notation "kFloor" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "budget" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0
  (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
local notation "Grid" => p4Q2PZ37AFQ_GridIndex

local instance p4Q2PZ37AGN_auto_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGN_auto_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The literal original plaquette count, now as a rational value. -/
def p4Q2PZ37AGN_countRational : ℚ :=
  (periodicHypercubicEvenSpatialSlicePlaquetteList H).length

theorem p4Q2PZ37AGN_countRational_exact :
    (p4Q2PZ37AGN_countRational H : ℝ) = pH := by
  simp [p4Q2PZ37AGN_countRational, p4Q2PZ37AFZ_plaquetteCount]

/-- Genuine zero-width centered source at actual rational configurations. -/
def p4Q2PZ37AGN_centeredSourceRational
    (A : Cfg) (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e)) : ℚ :=
  p4Q2PZ37AGN_centeredActionRational H A a

theorem p4Q2PZ37AGN_centeredSourceRational_exact
    (A : Cfg) (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e)) :
    fCont A = (p4Q2PZ37AGN_centeredSourceRational H A a : ℝ) :=
  p4Q2PZ37AGN_originalCenteredContinuous_rational H A a

/-- Exact rational original global action budget, independent of centers. -/
def p4Q2PZ37AGN_actionBudgetInterval : p4Q2PZ37AFV_verifiedInterval budget where
  lower := 2 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H : ℚ)
  upper := 2 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H : ℚ)
  hLower := by simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget]
  hUpper := by simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget]

/-- Auto-scaled Taylor enclosure of the actual original exponential floor. -/
def p4Q2PZ37AGN_originalFloorRawInterval (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval kFloor := by
  let s := p4Q2PZ37AGN_actionBudgetInterval H
  let lo : ℚ := -(p4Q2PZ37AGK_upper m * s.upper)
  let hi : ℚ := -(p4Q2PZ37AGK_lower m * s.lower)
  have hs : 0 ≤ s.lower := by
    dsimp [s, p4Q2PZ37AGN_actionBudgetInterval]
    positivity
  have c := p4Q2PZ37AGJ_boltzmannInterval
    (p4Q2PZ37AGK_originalCouplingInterval m) s
    (p4Q2PZ37AGK_lower_nonneg m) hs
    (p4Q2PZ37AGM_autoScale lo hi) n
    (p4Q2PZ37AGM_autoScale_pos lo hi) hn
    (p4Q2PZ37AGM_scaledEndpoints lo hi).1
    (p4Q2PZ37AGM_scaledEndpoints lo hi).2
  simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor,
    neg_mul] using c

/-- Intersect with the proved range of the same genuine floor. -/
def p4Q2PZ37AGN_originalFloorInterval (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval kFloor :=
  p4Q2PZ37AGN_intersectInterval
    (p4Q2PZ37AGN_originalFloorRawInterval H m n hn)
    { lower := 0, upper := 1
      hLower := by simpa using
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
          H b0).le
      hUpper := by simpa using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_one
          H b0 p4Q2PZ37ADC_fixedCoupling_pos.le }

/-- The original centered integrand uses the exact source and genuine
floor midpoint; the sign of the rational source chooses the endpoints. -/
def p4Q2PZ37AGN_originalIntegrandInterval
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval (gCont B A) := by
  let s := p4Q2PZ37AGN_centeredSourceRational H A a
  let ker := p4Q2PZ37AGM_originalClippedKernelInterval H A B a b m n hn
  let fl := p4Q2PZ37AGN_originalFloorInterval H m n hn
  let lo : ℚ := ker.lower - (1 + fl.upper) / 2
  let hi : ℚ := ker.upper - (1 + fl.lower) / 2
  have hlo : (lo : ℝ) ≤ K A B - (1 + kFloor) / 2 := by
    dsimp [lo]
    push_cast
    linarith only [ker.hLower, fl.hUpper]
  have hhi : K A B - (1 + kFloor) / 2 ≤ (hi : ℝ) := by
    dsimp [hi]
    push_cast
    linarith only [ker.hUpper, fl.hLower]
  have hs : gCont B A = (s : ℝ) * (K A B - (1 + kFloor) / 2) := by
    unfold p4Q2PZ37AGE_originalContinuousIntegrand
    rw [p4Q2PZ37AGN_centeredSourceRational_exact H A a]
  have h := p4Q2PZ37AGI_signedMul_bounds (s : ℝ)
    (K A B - (1 + kFloor) / 2) (lo : ℝ) (hi : ℝ) hlo hhi
  refine { lower := min (s * lo) (s * hi), upper := max (s * lo) (s * hi),
    hLower := ?_, hUpper := ?_ }
  · rw [hs]
    simpa [mul_comm] using h.1
  · rw [hs]
    simpa [mul_comm] using h.2

/-- Exact Haar centering halves the previous global original integrand bound. -/
theorem p4Q2PZ37AGN_originalIntegrand_abs_le_halfSource (B A : Cfg) :
    |gCont B A| ≤ ((1 - kFloor) / 2) * (pH / 2) := by
  have hs := p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A
  have hk := p4Q2PZ37AGB_originalKernel_centeredMidpointBound H A B
  have hp : 0 ≤ pH / 2 := div_nonneg
    (p4Q2PZ37AGF_plaquetteCount_nonneg H) (by norm_num)
  unfold p4Q2PZ37AGE_originalContinuousIntegrand
  rw [abs_mul]
  calc
    |fCont A| * |K A B - (1 + kFloor) / 2| ≤
        (pH / 2) * ((1 - kFloor) / 2) := mul_le_mul hs hk (abs_nonneg _) hp
    _ = ((1 - kFloor) / 2) * (pH / 2) := mul_comm _ _

/-- Rational global enclosure retains the refined original floor. -/
def p4Q2PZ37AGN_transferRadius (m n : ℕ) (hn : 0 < n) : ℚ :=
  p4Q2PZ37AGN_countRational H *
    (1 - (p4Q2PZ37AGN_originalFloorInterval H m n hn).lower) / 4

theorem p4Q2PZ37AGN_originalTransfer_abs_le_radius
    (B : Cfg) (m n : ℕ) (hn : 0 < n) :
    |t B| ≤ (p4Q2PZ37AGN_transferRadius H m n hn : ℝ) := by
  have hp : 0 ≤ pH := p4Q2PZ37AGF_plaquetteCount_nonneg H
  let hf := p4Q2PZ37AGN_originalFloorInterval H m n hn
  have hPoint (A : Cfg) :
      |gCont B A| ≤ (p4Q2PZ37AGN_transferRadius H m n hn : ℝ) := by
    have h := p4Q2PZ37AGN_originalIntegrand_abs_le_halfSource H B A
    have hmul := mul_le_mul_of_nonneg_left hf.hLower hp
    dsimp [p4Q2PZ37AGN_transferRadius]
    push_cast
    rw [p4Q2PZ37AGN_countRational_exact]
    dsimp [hf] at hmul
    nlinarith only [h, hmul]
  have hi : Integrable (gCont B) muH :=
    (p4Q2PZ37AGC_originalCenteredKernelIntegrand_integrable B).congr
      (p4Q2PZ37AGE_originalIntegrand_ae_eq_continuous H B)
  rw [← p4Q2PZ37AGE_originalContinuousIntegral_eq_transfer H B]
  calc
    |∫ A : Cfg, gCont B A ∂muH| ≤ ∫ A : Cfg, |gCont B A| ∂muH :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ : Cfg, (p4Q2PZ37AGN_transferRadius H m n hn : ℝ) ∂muH :=
      integral_mono (by simpa only [Real.norm_eq_abs] using hi.norm)
        (integrable_const _) hPoint
    _ = (p4Q2PZ37AGN_transferRadius H m n hn : ℝ) := by simp

/-- In particular this is never weaker than the new p_H/4 envelope. -/
theorem p4Q2PZ37AGN_transferRadius_le_quarterCount
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGN_transferRadius H m n hn ≤ p4Q2PZ37AGN_countRational H / 4 := by
  have h0 : 0 ≤ (p4Q2PZ37AGN_originalFloorInterval H m n hn).lower := by
    exact le_max_right _ _
  have hp : 0 ≤ p4Q2PZ37AGN_countRational H := by
    unfold p4Q2PZ37AGN_countRational
    positivity
  unfold p4Q2PZ37AGN_transferRadius
  nlinarith only [mul_nonneg hp h0]

def p4Q2PZ37AGN_originalTransferGlobalInterval
    (B : Cfg) (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval (t B) where
  lower := -p4Q2PZ37AGN_transferRadius H m n hn
  upper := p4Q2PZ37AGN_transferRadius H m n hn
  hLower := by
    simpa using (abs_le.mp
      (p4Q2PZ37AGN_originalTransfer_abs_le_radius H B m n hn)).1
  hUpper := (abs_le.mp
    (p4Q2PZ37AGN_originalTransfer_abs_le_radius H B m n hn)).2

/-- A rational geometric budget from the literal original spatial radius. -/
def p4Q2PZ37AGN_original24Geometry (m : ℕ) : ℚ :=
  (6 + 13 * p4Q2PZ37AGK_upper m * p4Q2PZ37AGN_countRational H) *
    p4Q2PZ37AGN_original24Radius H

theorem p4Q2PZ37AGN_original24Geometry_covers (m : ℕ) :
    p4Q2PZ37AGG_originalSpatialSlope H *
      (p4Q2PZ37AGN_original24Grid H).radius ≤
        (p4Q2PZ37AGN_original24Geometry H m : ℝ) := by
  have hp : 0 ≤ pH := p4Q2PZ37AGF_plaquetteCount_nonneg H
  have hk : 0 ≤ kFloor :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H b0).le
  have hb := (p4Q2PZ37AGK_originalCoupling_bounds m).2
  have hmul := mul_le_mul_of_nonneg_right hb hp
  have hSlope : p4Q2PZ37AGG_originalSpatialSlope H ≤
      6 + 13 * (p4Q2PZ37AGK_upper m : ℝ) * pH := by
    unfold p4Q2PZ37AGG_originalSpatialSlope
    nlinarith only [hk, hmul]
  have h := mul_le_mul_of_nonneg_right hSlope
    (p4Q2PZ37AGN_original24Grid H).radius_nonneg
  have hCast : (p4Q2PZ37AGN_original24Geometry H m : ℝ) =
      (6 + 13 * (p4Q2PZ37AGK_upper m : ℝ) * pH) *
        (p4Q2PZ37AGN_original24Grid H).radius := by
    simp only [p4Q2PZ37AGN_original24Geometry, Rat.cast_mul, Rat.cast_add,
      Rat.cast_ofNat, p4Q2PZ37AGN_countRational_exact,
      p4Q2PZ37AGN_original24Radius_exact]
  exact h.trans_eq hCast.symm

/-- The table consists of actual original values with fully constructed
mass, source, kernel and geometric evidence, rather than synthetic samples. -/
def p4Q2PZ37AGN_original24Table
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGI_rationalTable (p4Q2PZ37AGN_original24Grid H).n where
  sampleLower := fun i => (p4Q2PZ37AGN_originalIntegrandInterval H
    ((p4Q2PZ37AGN_original24Grid H).center i) B
    (p4Q2PZ37AGN_original24Center_rational H i) b m n hn).lower
  sampleUpper := fun i => (p4Q2PZ37AGN_originalIntegrandInterval H
    ((p4Q2PZ37AGN_original24Grid H).center i) B
    (p4Q2PZ37AGN_original24Center_rational H i) b m n hn).upper
  massLower := (p4Q2PZ37AGN_original24MassIntervals H).lower
  massUpper := (p4Q2PZ37AGN_original24MassIntervals H).upper
  geometry := p4Q2PZ37AGN_original24Geometry H m

theorem p4Q2PZ37AGN_original24Table_certified
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGI_certifiedTable H B (p4Q2PZ37AGN_original24Grid H)
      (p4Q2PZ37AGN_original24Table H B b m n hn) where
  hGeometry := p4Q2PZ37AGN_original24Geometry_covers H m
  hCenterLower := fun i => (p4Q2PZ37AGN_originalIntegrandInterval H
    ((p4Q2PZ37AGN_original24Grid H).center i) B
    (p4Q2PZ37AGN_original24Center_rational H i) b m n hn).hLower
  hCenterUpper := fun i => (p4Q2PZ37AGN_originalIntegrandInterval H
    ((p4Q2PZ37AGN_original24Grid H).center i) B
    (p4Q2PZ37AGN_original24Center_rational H i) b m n hn).hUpper
  hMassLower := (p4Q2PZ37AGN_original24MassIntervals H).hLower
  hMassUpper := (p4Q2PZ37AGN_original24MassIntervals H).hUpper

/-- The actual signed AGI quadrature is intersected with the independently
proved improved global range. Both contain the same original transfer. -/
def p4Q2PZ37AGN_original24TransferInterval
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : p4Q2PZ37AFV_verifiedInterval (t B) :=
  p4Q2PZ37AGN_intersectInterval
    (p4Q2PZ37AGN_original24Table_certified H B b m n hn).toVerifiedInterval
    (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)

/-- Arbitrary assignments of the original 24 centers need only m,n,n>0. -/
def p4Q2PZ37AGN_original24BoundaryTransferInterval
    (right : Link → Fin (Fintype.card Grid)) (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval (t (fun e => p4Q2PZ37AFQ_originalCenters (right e))) :=
  p4Q2PZ37AGN_original24TransferInterval H _
    (fun e => p4Q2PZ37AGL_originalCenter_rational (right e)) m n hn

theorem p4Q2PZ37AGN_original24Transfer_positive
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (h : 0 < (p4Q2PZ37AGN_original24TransferInterval H B b m n hn).lower) :
    0 < t B :=
  p4Q2PZ37AFV_interval_positive
    (p4Q2PZ37AGN_original24TransferInterval H B b m n hn) h

theorem p4Q2PZ37AGN_original24Transfer_negative
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (h : (p4Q2PZ37AGN_original24TransferInterval H B b m n hn).upper < 0) :
    t B < 0 :=
  p4Q2PZ37AFV_interval_negative
    (p4Q2PZ37AGN_original24TransferInterval H B b m n hn) h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGN_intersectInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_countRational_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_centeredSourceRational_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_actionBudgetInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalFloorRawInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalFloorInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalIntegrandInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalIntegrand_abs_le_halfSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalTransfer_abs_le_radius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_transferRadius_le_quarterCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalTransferGlobalInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24Geometry_covers
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24Table_certified
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24TransferInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24BoundaryTransferInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24Transfer_positive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24Transfer_negative
