import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAutomaticSignedSpatialCertificateV5_PZ37AGN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGO — precise geometric obstruction for original signed tables

A true signed rational table with enclosing center samples can lose all
sign information when the geometric oscillation budget exceeds twice the
independently certified global radius. The exact min/max rational evaluator
and genuine normalized Haar upper masses imply that its raw lower and upper
endpoints span the *entire* global interval; intersection cannot regain a
physical sign.

All results here refer to the original continuous Wilson source, original
Haar cells, original kernel/floor and original centered transfer. No
synthetic sign is promoted to the physical transfer.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace p4Q2PZ37AGI_rationalTable

variable {N : ℕ}

/-- Geometry at least twice the global magnitude radius forces the
ACTUAL signed min/max evaluator to cover the whole global interval.
The upper mass endpoints need only bound a probability vector, not sum
to one. This is a general finite-table obstruction, not an assumption
about a physical sign. -/
theorem p4Q2PZ37AGO_geometry_swamps_signed_samples
    (d : p4Q2PZ37AGI_rationalTable N) (R : ℚ)
    (hR : 0 ≤ R)
    (hMass : ∀ i, 0 ≤ d.massUpper i)
    (hSum : 1 ≤ ∑ i : Fin N, d.massUpper i)
    (hSample : ∀ i, d.sampleLower i ≤ R ∧ -R ≤ d.sampleUpper i)
    (hGeom : 2 * R ≤ d.geometry) :
    d.lower ≤ -R ∧ R ≤ d.upper := by
  have hCellLo (i : Fin N) : d.cellLower i ≤ -R := by
    dsimp [cellLower]
    linarith only [(hSample i).1, hGeom]
  have hCellHi (i : Fin N) : R ≤ d.cellUpper i := by
    dsimp [cellUpper]
    linarith only [(hSample i).2, hGeom]
  have hLowerSum :
      d.lower ≤ ∑ i : Fin N, (-R) * d.massUpper i := by
    unfold lower
    apply Finset.sum_le_sum
    intro i hi
    calc
      min (d.cellLower i * d.massLower i)
          (d.cellLower i * d.massUpper i) ≤
          d.cellLower i * d.massUpper i := min_le_right _ _
      _ ≤ (-R) * d.massUpper i :=
        mul_le_mul_of_nonneg_right (hCellLo i) (hMass i)
  have hUpperSum :
      (∑ i : Fin N, R * d.massUpper i) ≤ d.upper := by
    unfold upper
    apply Finset.sum_le_sum
    intro i hi
    calc
      R * d.massUpper i ≤ d.cellUpper i * d.massUpper i :=
        mul_le_mul_of_nonneg_right (hCellHi i) (hMass i)
      _ ≤ max (d.cellUpper i * d.massLower i)
          (d.cellUpper i * d.massUpper i) := le_max_right _ _
  constructor
  · calc
      d.lower ≤ ∑ i : Fin N, (-R) * d.massUpper i := hLowerSum
      _ = (-R) * (∑ i : Fin N, d.massUpper i) := by rw [Finset.mul_sum]
      _ ≤ (-R) * 1 :=
        mul_le_mul_of_nonpos_left hSum (neg_nonpos.mpr hR)
      _ = -R := by ring
  · calc
      R = R * 1 := by ring
      _ ≤ R * (∑ i : Fin N, d.massUpper i) :=
        mul_le_mul_of_nonneg_left hSum hR
      _ = ∑ i : Fin N, R * d.massUpper i := by rw [Finset.mul_sum]
      _ ≤ d.upper := hUpperSum

/-- Both rational sign tests must reject a table whose geometric range
already covers the full global interval. -/
theorem p4Q2PZ37AGO_geometry_rejects_both_signs
    (d : p4Q2PZ37AGI_rationalTable N) (R : ℚ)
    (hR : 0 ≤ R)
    (hMass : ∀ i, 0 ≤ d.massUpper i)
    (hSum : 1 ≤ ∑ i : Fin N, d.massUpper i)
    (hSample : ∀ i, d.sampleLower i ≤ R ∧ -R ≤ d.sampleUpper i)
    (hGeom : 2 * R ≤ d.geometry) :
    d.acceptsPositive = false ∧ d.acceptsNegative = false := by
  obtain ⟨hLo, hHi⟩ :=
    p4Q2PZ37AGO_geometry_swamps_signed_samples d R hR hMass hSum hSample hGeom
  have hNotPos : ¬ (0 < d.lower) := by linarith only [hLo, hR]
  have hNotNeg : ¬ (d.upper < 0) := by linarith only [hHi, hR]
  constructor
  · simp [acceptsPositive, hNotPos]
  · simp [acceptsNegative, hNotNeg]

end p4Q2PZ37AGI_rationalTable

/-- Intersection with an independently proved symmetric global interval
is EXACTLY that interval once the raw interval contains both endpoints.
No numerical evaluation or sign oracle is used. -/
theorem p4Q2PZ37AGO_intersection_collapses {x : ℝ}
    (raw global : p4Q2PZ37AFV_verifiedInterval x) (R : ℚ)
    (hGlobal : global.lower = -R ∧ global.upper = R)
    (hRawLo : raw.lower ≤ -R) (hRawHi : R ≤ raw.upper) :
    (p4Q2PZ37AGN_intersectInterval raw global).lower = -R ∧
      (p4Q2PZ37AGN_intersectInterval raw global).upper = R := by
  constructor
  · change max raw.lower global.lower = -R
    rw [hGlobal.1]
    exact max_eq_right hRawLo
  · change min raw.upper global.upper = R
    rw [hGlobal.2]
    exact min_eq_right hRawHi

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGO_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGO_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGO_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGO_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGO_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "gCont" => p4Q2PZ37AGE_originalContinuousIntegrand H
local notation "kFloor" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H
    p4Q2PZ37ADC_fixedCoupling
local notation "t" => decomposableOneSliceTransferIntegral H 2
  p4Q2PZ37ADC_fixedCoupling
  (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AGO_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGO_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The pointwise original integrand, not a chosen L2 representative,
obeys the same rational global radius as its Haar integral. -/
theorem p4Q2PZ37AGO_originalIntegrand_abs_le_radius
    (B A : Cfg) (m n : ℕ) (hn : 0 < n) :
    |gCont B A| ≤ (p4Q2PZ37AGN_transferRadius H m n hn : ℝ) := by
  have hp : 0 ≤ pH := p4Q2PZ37AGF_plaquetteCount_nonneg H
  have h := p4Q2PZ37AGN_originalIntegrand_abs_le_halfSource H B A
  have hmul := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AGN_originalFloorInterval H m n hn).hLower hp
  dsimp [p4Q2PZ37AGN_transferRadius]
  push_cast
  rw [p4Q2PZ37AGN_countRational_exact]
  nlinarith only [h, hmul]

/-- True AGD product-Haar upper cell masses have total weight at least
one: no artificial rational mass normalization is imposed. -/
theorem p4Q2PZ37AGO_original24MassUpper_sum_ge_one :
    (1 : ℚ) ≤
      ∑ i : Fin (p4Q2PZ37AGN_original24Grid H).n,
        (p4Q2PZ37AGN_original24MassIntervals H).upper i := by
  let grid := p4Q2PZ37AGN_original24Grid H
  let masses := p4Q2PZ37AGN_original24MassIntervals H
  have hReal : (1 : ℝ) ≤
      ∑ i : Fin grid.n, (masses.upper i : ℝ) := by
    calc
      (1 : ℝ) =
          ∑ i : Fin grid.n, Measure.real muH (grid.cell i) :=
            masses.total_mass.symm
      _ ≤ ∑ i : Fin grid.n, (masses.upper i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact masses.hUpper i
  exact_mod_cast hReal

/-- At the REAL original 24-center table, the precise normalized-Haar
and centered-source hypotheses of the general obstruction all hold. -/
theorem p4Q2PZ37AGO_original24_raw_spans_global
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hGeom : 2 * p4Q2PZ37AGN_transferRadius H m n hn ≤
      p4Q2PZ37AGN_original24Geometry H m) :
    (p4Q2PZ37AGN_original24Table H B b m n hn).lower ≤
        -p4Q2PZ37AGN_transferRadius H m n hn ∧
      p4Q2PZ37AGN_transferRadius H m n hn ≤
        (p4Q2PZ37AGN_original24Table H B b m n hn).upper := by
  let R := p4Q2PZ37AGN_transferRadius H m n hn
  let grid := p4Q2PZ37AGN_original24Grid H
  let d := p4Q2PZ37AGN_original24Table H B b m n hn
  let c := p4Q2PZ37AGN_original24Table_certified H B b m n hn
  have hRreal : (0 : ℝ) ≤ (R : ℝ) :=
    (abs_nonneg (t B)).trans
      (p4Q2PZ37AGN_originalTransfer_abs_le_radius H B m n hn)
  have hR : (0 : ℚ) ≤ R := by exact_mod_cast hRreal
  have hMass (i : Fin grid.n) : 0 ≤ d.massUpper i := by
    change (0 : ℚ) ≤ p4Q2PZ37AGD_rationalUpper H
    unfold p4Q2PZ37AGD_rationalUpper
    positivity
  have hSum : (1 : ℚ) ≤ ∑ i : Fin grid.n, d.massUpper i := by
    simpa only [d, p4Q2PZ37AGN_original24Table,
      p4Q2PZ37AGN_original24MassIntervals] using
      p4Q2PZ37AGO_original24MassUpper_sum_ge_one H
  have hSample (i : Fin grid.n) :
      d.sampleLower i ≤ R ∧ -R ≤ d.sampleUpper i := by
    have hCenter := p4Q2PZ37AGO_originalIntegrand_abs_le_radius H B
      (grid.center i) m n hn
    have hLo : (d.sampleLower i : ℝ) ≤ (R : ℝ) :=
      (c.hCenterLower i).trans (abs_le.mp hCenter).2
    have hHi : (-(R : ℝ)) ≤ (d.sampleUpper i : ℝ) :=
      (abs_le.mp hCenter).1.trans (c.hCenterUpper i)
    constructor
    · exact_mod_cast hLo
    · exact_mod_cast hHi
  exact p4Q2PZ37AGI_rationalTable.p4Q2PZ37AGO_geometry_swamps_signed_samples
    d R hR hMass hSum hSample hGeom

/-- The final tightened certificate equals its independent global radius,
rather than establishing either nonzero sign, whenever original geometry
dominates twice that radius. -/
theorem p4Q2PZ37AGO_original24_interval_collapses
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hGeom : 2 * p4Q2PZ37AGN_transferRadius H m n hn ≤
      p4Q2PZ37AGN_original24Geometry H m) :
    (p4Q2PZ37AGN_original24TransferInterval H B b m n hn).lower =
        -p4Q2PZ37AGN_transferRadius H m n hn ∧
      (p4Q2PZ37AGN_original24TransferInterval H B b m n hn).upper =
        p4Q2PZ37AGN_transferRadius H m n hn := by
  let R := p4Q2PZ37AGN_transferRadius H m n hn
  let c := p4Q2PZ37AGN_original24Table_certified H B b m n hn
  have hRaw := p4Q2PZ37AGO_original24_raw_spans_global H B b m n hn hGeom
  have hCollapse := p4Q2PZ37AGO_intersection_collapses
    c.toVerifiedInterval
    (p4Q2PZ37AGN_originalTransferGlobalInterval H B m n hn)
    R ⟨rfl, rfl⟩ hRaw.1 hRaw.2
  exact hCollapse

/-- A certified physical sign cannot be extracted from the current fixed
24-center construction under the explicit critical geometry condition. -/
theorem p4Q2PZ37AGO_original24_interval_no_sign
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hGeom : 2 * p4Q2PZ37AGN_transferRadius H m n hn ≤
      p4Q2PZ37AGN_original24Geometry H m) :
    ¬ (0 < (p4Q2PZ37AGN_original24TransferInterval H B b m n hn).lower) ∧
      ¬ ((p4Q2PZ37AGN_original24TransferInterval H B b m n hn).upper < 0) := by
  obtain ⟨hLo, hHi⟩ :=
    p4Q2PZ37AGO_original24_interval_collapses H B b m n hn hGeom
  have hRreal : (0 : ℝ) ≤
      (p4Q2PZ37AGN_transferRadius H m n hn : ℝ) :=
    (abs_nonneg (t B)).trans
      (p4Q2PZ37AGN_originalTransfer_abs_le_radius H B m n hn)
  have hR : (0 : ℚ) ≤ p4Q2PZ37AGN_transferRadius H m n hn := by
    exact_mod_cast hRreal
  constructor
  · rw [hLo]
    linarith only [hR]
  · rw [hHi]
    linarith only [hR]


/-- The genuine three spatial directions and the three unordered spatial
direction pairs have the same finite cardinality. Nat.card avoids reliance
on the local Fintype.ofFinite enumeration of a physical link carrier. -/
theorem p4Q2PZ37AGO_originalSpatial_linkCount_eq_plaquetteCount :
    p4Q2PZ37AGN_countRational H =
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℚ) := by
  have hDir : Nat.card PeriodicHypercubicEvenSpatialDirection = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hPair : Nat.card PeriodicHypercubicEvenSpatialDirectionPair = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hNat :
      Nat.card (PeriodicHypercubicEvenSpatialSliceLink H) =
        Nat.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) := by
    simp only [PeriodicHypercubicEvenSpatialSliceLink,
      PeriodicHypercubicEvenSpatialSlicePlaquette, Nat.card_prod, hDir, hPair]
  have hList :
      (periodicHypercubicEvenSpatialSlicePlaquetteList H).length =
        Nat.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) := by
    simp [periodicHypercubicEvenSpatialSlicePlaquetteList,
      Fintype.card_eq_nat_card]
  have hLink :
      Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) =
        Nat.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_eq_nat_card
  unfold p4Q2PZ37AGN_countRational
  exact_mod_cast (hList.trans (hNat.symm.trans hLink.symm))

/-- In the actual original model, the 24-center spatial geometry always
dominates twice the certified transfer radius, with NO geometric hypothesis.
Refinement of beta0 or Taylor order cannot remove this fixed-cell obstacle. -/
theorem p4Q2PZ37AGO_original24_geometry_dominates_twoRadius
    (m n : ℕ) (hn : 0 < n) :
    2 * p4Q2PZ37AGN_transferRadius H m n hn ≤
      p4Q2PZ37AGN_original24Geometry H m := by
  let c : ℚ := p4Q2PZ37AGN_countRational H
  let beta : ℚ := p4Q2PZ37AGK_upper m
  let f : ℚ := (p4Q2PZ37AGN_originalFloorInterval H m n hn).lower
  have hc : 0 ≤ c := by
    dsimp [c, p4Q2PZ37AGN_countRational]
    positivity
  have hbReal : (0 : ℝ) ≤ (beta : ℝ) :=
    (p4Q2PZ37ADC_fixedCoupling_pos).le.trans
      (p4Q2PZ37AGK_originalCoupling_bounds m).2
  have hb : 0 ≤ beta := by exact_mod_cast hbReal
  have hf : 0 ≤ f := by
    change (0 : ℚ) ≤ max
      (p4Q2PZ37AGN_originalFloorRawInterval H m n hn).lower 0
    exact le_max_right _ _
  have hcf : 0 ≤ c * f := mul_nonneg hc hf
  have hbcc : 0 ≤ beta * c * c :=
    mul_nonneg (mul_nonneg hb hc) hc
  have hCount := p4Q2PZ37AGO_originalSpatial_linkCount_eq_plaquetteCount H
  change 2 * (c * (1 - f) / 4) ≤
    (6 + 13 * beta * c) * ((4 / 5 : ℚ) * (Fintype.card Link : ℚ))
  rw [← hCount]
  nlinarith only [hc, hcf, hbcc]

/-- The actual fixed 24-center signed AGI interval is IDENTICALLY the
improved global envelope, for every original rational boundary and every
permitted coupling/Taylor truncation order. -/
theorem p4Q2PZ37AGO_original24_interval_exact
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGN_original24TransferInterval H B b m n hn).lower =
        -p4Q2PZ37AGN_transferRadius H m n hn ∧
      (p4Q2PZ37AGN_original24TransferInterval H B b m n hn).upper =
        p4Q2PZ37AGN_transferRadius H m n hn :=
  p4Q2PZ37AGO_original24_interval_collapses H B b m n hn
    (p4Q2PZ37AGO_original24_geometry_dominates_twoRadius H m n hn)

/-- Neither sign-checking predicate can succeed on the actual fixed
24-center enclosure, regardless of m,n, boundary, or original Haar masses.
This does NOT say that the true physical signed transfer itself is zero. -/
theorem p4Q2PZ37AGO_original24_no_sign_unconditional
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    ¬ (0 < (p4Q2PZ37AGN_original24TransferInterval H B b m n hn).lower) ∧
      ¬ ((p4Q2PZ37AGN_original24TransferInterval H B b m n hn).upper < 0) :=
  p4Q2PZ37AGO_original24_interval_no_sign H B b m n hn
    (p4Q2PZ37AGO_original24_geometry_dominates_twoRadius H m n hn)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGI_rationalTable.p4Q2PZ37AGO_geometry_swamps_signed_samples
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGI_rationalTable.p4Q2PZ37AGO_geometry_rejects_both_signs
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGO_intersection_collapses
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGO_originalIntegrand_abs_le_radius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGO_original24MassUpper_sum_ge_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGO_original24_raw_spans_global
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGO_original24_interval_collapses
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGO_original24_interval_no_sign

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGO_originalSpatial_linkCount_eq_plaquetteCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGO_original24_geometry_dominates_twoRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGO_original24_interval_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGO_original24_no_sign_unconditional
