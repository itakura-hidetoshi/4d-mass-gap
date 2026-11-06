import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSignedSpatialIntervalCertificateV5_PZ37AGI
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAutoscaledKernelV5_PZ37AGM
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGN — original spatial Haar masses and Wilson mean enclosures

Keep the original spatial configuration, normalized product Haar law and
AFZ Hilbert centering scalar. Rational mass endpoints carry evidence for
the actual cells of any AGH spatial grid. Their total actual mass is one.
The exact AGI signed evaluator also bounds any integrable original
observable with proved cellwise bounds; no discrete probability replaces
the original Haar integral.

The original Wilson action has spatial chordal slope 24, obtained by
cancelling the SAME centering scalar in AGG's slope-12 source theorem.
AGL's exact rational center actions and a rational geometry budget then
enclose the actual Wilson Haar mean. Intersect with its established
[0,2*plaquetteCount] range. This remains useful for independent quadrature
checks and future refined grids; it does not assert that a coarse grid is
accurate enough to certify a nonzero signed transfer.

The concrete AFQ 24-center product grid supplies every required datum:
radius (4/5)*numberOfLinks, actual AGD mass endpoints, rational coordinate
witnesses and exact rational action samples. No rational-density choices
of unknown mean or mass values, replacement source, new physical premise,
two-threshold shell, coercivity, Hamiltonian or continuum gap claim enters.
Canonical finite enumeration remains noncomputable.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGN_mean_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGN_mean_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGN_mean_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGN_mean_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGN_mean_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable {H : ℕ}
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "Wc" => p4Q2JI_actualSpatialWilsonContinuous H
local notation "mH" => p4Q2PZ37AFZ_originalWilsonMean H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H

local instance p4Q2PZ37AGN_mean_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGN_mean_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Rational endpoints for the SAME original Haar cells, with separate
inclusion evidence. The endpoints need not be exact masses. -/
structure p4Q2PZ37AGN_massIntervals
    (grid : p4Q2PZ37AGH_originalSpatialGrid H) where
  lower : Fin grid.n → ℚ
  upper : Fin grid.n → ℚ
  hLower : ∀ i, (lower i : ℝ) ≤ Measure.real muH (grid.cell i)
  hUpper : ∀ i, Measure.real muH (grid.cell i) ≤ (upper i : ℝ)

namespace p4Q2PZ37AGN_massIntervals

variable {grid : p4Q2PZ37AGH_originalSpatialGrid H}

/-- Reuse the original Haar-step integration calculus without changing
the cells or the original probability measure. -/
def toHaarCells (c : p4Q2PZ37AGN_massIntervals grid) :
    p4Q2PZ37AGC_originalHaarCells H where
  n := grid.n
  cell := grid.cell
  hMeas := grid.hMeas
  hPartition := grid.hPartition
  weight := fun i => (c.lower i + c.upper i) / 2
  weightError := fun i => ((c.upper i : ℝ) - (c.lower i : ℝ)) / 2
  hWeightError_nonneg := fun i => div_nonneg
    (sub_nonneg.mpr ((c.hLower i).trans (c.hUpper i))) (by norm_num)
  hWeightAccuracy := by
    intro i
    have hlo := c.hLower i
    have hhi := c.hUpper i
    push_cast
    apply abs_le.mpr
    constructor <;> linarith only [hlo, hhi]

/-- A rational table keeps the genuine mass endpoints visible. -/
def toTable (c : p4Q2PZ37AGN_massIntervals grid)
    (lo hi : Fin grid.n → ℚ) (geometry : ℚ) :
    p4Q2PZ37AGI_rationalTable grid.n where
  sampleLower := lo
  sampleUpper := hi
  massLower := c.lower
  massUpper := c.upper
  geometry := geometry

/-- The actual mass vector is normalized even when supplied rational
endpoint vectors do not sum to one. -/
theorem total_mass (c : p4Q2PZ37AGN_massIntervals grid) :
    (∑ i : Fin grid.n, Measure.real muH (grid.cell i)) = 1 := by
  have hStep :
      p4Q2PZ37AGC_HaarStep c.toHaarCells (fun _ => (1 : ℚ)) =
        (fun _ : Cfg => (1 : ℝ)) := by
    funext A
    obtain ⟨i, hi, _⟩ := grid.hPartition A
    simpa using p4Q2PZ37AGC_HaarStep_eq_onCell
      c.toHaarCells (fun _ => (1 : ℚ)) i A hi
  have h := p4Q2PZ37AGC_HaarStep_integral
    c.toHaarCells (fun _ => (1 : ℚ))
  rw [hStep] at h
  simpa [toHaarCells] using h.symm

/-- Generic signed integration against ORIGINAL spatial Haar, using
AGI's unchanged exact rational evaluator and actual true cell masses. -/
theorem integral_bounds (c : p4Q2PZ37AGN_massIntervals grid)
    (lo hi : Fin grid.n → ℚ) (geometry : ℚ)
    (f : Cfg → ℝ) (hf : Integrable f muH)
    (hCell : ∀ i A, A ∈ grid.cell i →
      ((c.toTable lo hi geometry).cellLower i : ℝ) ≤ f A ∧
        f A ≤ ((c.toTable lo hi geometry).cellUpper i : ℝ)) :
    ((c.toTable lo hi geometry).lower : ℝ) ≤ (∫ A : Cfg, f A ∂muH) ∧
      (∫ A : Cfg, f A ∂muH) ≤ ((c.toTable lo hi geometry).upper : ℝ) := by
  let d := c.toTable lo hi geometry
  let p := c.toHaarCells
  have hLoPoint : ∀ A : Cfg,
      p4Q2PZ37AGC_HaarStep p d.cellLower A ≤ f A := by
    intro A
    obtain ⟨i, hiA, _⟩ := grid.hPartition A
    rw [p4Q2PZ37AGC_HaarStep_eq_onCell p d.cellLower i A hiA]
    exact (hCell i A hiA).1
  have hHiPoint : ∀ A : Cfg,
      f A ≤ p4Q2PZ37AGC_HaarStep p d.cellUpper A := by
    intro A
    obtain ⟨i, hiA, _⟩ := grid.hPartition A
    rw [p4Q2PZ37AGC_HaarStep_eq_onCell p d.cellUpper i A hiA]
    exact (hCell i A hiA).2
  have hLoInt := integral_mono
    (p4Q2PZ37AGC_HaarStep_integrable p d.cellLower) hf hLoPoint
  have hHiInt := integral_mono hf
    (p4Q2PZ37AGC_HaarStep_integrable p d.cellUpper) hHiPoint
  rw [p4Q2PZ37AGC_HaarStep_integral p d.cellLower] at hLoInt
  rw [p4Q2PZ37AGC_HaarStep_integral p d.cellUpper] at hHiInt
  have hCastLo : (d.lower : ℝ) = ∑ i : Fin grid.n,
      min ((d.cellLower i : ℝ) * (c.lower i : ℝ))
        ((d.cellLower i : ℝ) * (c.upper i : ℝ)) := by
    simp [p4Q2PZ37AGI_rationalTable.lower, d, toTable]
  have hCastHi : (d.upper : ℝ) = ∑ i : Fin grid.n,
      max ((d.cellUpper i : ℝ) * (c.lower i : ℝ))
        ((d.cellUpper i : ℝ) * (c.upper i : ℝ)) := by
    simp [p4Q2PZ37AGI_rationalTable.upper, d, toTable]
  have hLoSum : (d.lower : ℝ) ≤ ∑ i : Fin grid.n,
      Measure.real muH (grid.cell i) * (d.cellLower i : ℝ) := by
    rw [hCastLo]
    apply Finset.sum_le_sum
    intro i _hi
    exact (p4Q2PZ37AGI_signedMul_bounds (d.cellLower i : ℝ)
      (Measure.real muH (grid.cell i)) (c.lower i : ℝ) (c.upper i : ℝ)
      (c.hLower i) (c.hUpper i)).1
  have hHiSum : (∑ i : Fin grid.n,
      Measure.real muH (grid.cell i) * (d.cellUpper i : ℝ)) ≤ (d.upper : ℝ) := by
    rw [hCastHi]
    apply Finset.sum_le_sum
    intro i _hi
    exact (p4Q2PZ37AGI_signedMul_bounds (d.cellUpper i : ℝ)
      (Measure.real muH (grid.cell i)) (c.lower i : ℝ) (c.upper i : ℝ)
      (c.hLower i) (c.hUpper i)).2
  exact ⟨hLoSum.trans hLoInt, hHiInt.trans hHiSum⟩

/-- Independent bounds on the same actual mass can only tighten. -/
def intersect (c d : p4Q2PZ37AGN_massIntervals grid) :
    p4Q2PZ37AGN_massIntervals grid where
  lower := fun i => max (c.lower i) (d.lower i)
  upper := fun i => min (c.upper i) (d.upper i)
  hLower := by
    intro i
    have h := max_le (c.hLower i) (d.hLower i)
    simpa using h
  hUpper := by
    intro i
    have h := le_min (c.hUpper i) (d.hUpper i)
    simpa using h

end p4Q2PZ37AGN_massIntervals

/-- The original action's all-link slope follows by cancelling the SAME
true mean in the already proved original centered-source slope. -/
theorem p4Q2PZ37AGN_originalWilsonAction_allLinkSlope
    (A C : Cfg) :
    |Wc A - Wc C| ≤
      24 * p4Q2PZ37AGG_originalSpatialChordalDistance H A C := by
  have h := p4Q2PZ37AGG_originalCenteredSource_allLinkChordalSlope H A C
  have hDiff : Wc A - Wc C = 2 * (fCont A - fCont C) := by
    change Wc A - Wc C = 2 *
      ((1 / 2 : ℝ) * (Wc A - mH * 1) -
        (1 / 2 : ℝ) * (Wc C - mH * 1))
    ring
  calc
    |Wc A - Wc C| = 2 * |fCont A - fCont C| := by
      rw [hDiff, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (12 * p4Q2PZ37AGG_originalSpatialChordalDistance H A C) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 24 * p4Q2PZ37AGG_originalSpatialChordalDistance H A C := by ring

/-- Exact rational original action samples and genuine mass endpoints;
no approximation of the unknown original mean is supplied as input. -/
def p4Q2PZ37AGN_originalWilsonMeanTable
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (mass : p4Q2PZ37AGN_massIntervals grid)
    (a : ∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e))
    (geometry : ℚ) : p4Q2PZ37AGI_rationalTable grid.n :=
  mass.toTable
    (fun i => p4Q2PZ37AGL_spatialActionRational H (grid.center i) (a i))
    (fun i => p4Q2PZ37AGL_spatialActionRational H (grid.center i) (a i))
    geometry

/-- Signed rational quadrature encloses the literal AFZ Hilbert/Haar
centering scalar for any supplied certified original spatial grid. -/
theorem p4Q2PZ37AGN_originalWilsonMean_bounds
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (mass : p4Q2PZ37AGN_massIntervals grid)
    (a : ∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e))
    (geometry : ℚ) (hGeometry : 24 * grid.radius ≤ (geometry : ℝ)) :
    ((p4Q2PZ37AGN_originalWilsonMeanTable grid mass a geometry).lower : ℝ) ≤ mH ∧
      mH ≤ ((p4Q2PZ37AGN_originalWilsonMeanTable grid mass a geometry).upper : ℝ) := by
  let q := fun i => p4Q2PZ37AGL_spatialActionRational H (grid.center i) (a i)
  have hInt : Integrable (fun A : Cfg => Wc A) muH :=
    ((Lp.memLp (p4Q2JU_originalSpatialWilsonPhysicalSource H : Lp ℝ 2 muH)).integrable
      (by norm_num)).congr (p4Q2JU_originalSpatialWilsonPhysicalSource_ae H)
  have hCell : ∀ i A, A ∈ grid.cell i →
      ((mass.toTable q q geometry).cellLower i : ℝ) ≤ Wc A ∧
        Wc A ≤ ((mass.toTable q q geometry).cellUpper i : ℝ) := by
    intro i A hA
    have hOsc : |Wc A - Wc (grid.center i)| ≤ (geometry : ℝ) :=
      ((p4Q2PZ37AGN_originalWilsonAction_allLinkSlope A (grid.center i)).trans
        (mul_le_mul_of_nonneg_left (grid.hRadius i A hA) (by norm_num))).trans
          hGeometry
    have hExact : Wc (grid.center i) = (q i : ℝ) :=
      p4Q2PZ37AGL_originalSpatialAction_exact H (grid.center i) (a i)
    rw [hExact] at hOsc
    obtain ⟨hlo, hhi⟩ := abs_le.mp hOsc
    change ((q i - geometry : ℚ) : ℝ) ≤ Wc A ∧
      Wc A ≤ ((q i + geometry : ℚ) : ℝ)
    push_cast
    constructor <;> linarith only [hlo, hhi]
  have h := mass.integral_bounds q q geometry (fun A : Cfg => Wc A) hInt hCell
  rw [← p4Q2PZ37AFZ_originalWilsonMean_eq_integral H] at h
  exact h

/-- Retain both the finite-cell enclosure and the original physical
[0,2*plaquetteCount] range, so the construction is tighten-only. -/
def p4Q2PZ37AGN_originalWilsonMeanInterval
    (grid : p4Q2PZ37AGH_originalSpatialGrid H)
    (mass : p4Q2PZ37AGN_massIntervals grid)
    (a : ∀ i e, p4Q2PZ37AGL_rationalCoordinates (grid.center i e))
    (geometry : ℚ) (hGeometry : 24 * grid.radius ≤ (geometry : ℝ)) :
    p4Q2PZ37AFV_verifiedInterval mH where
  lower := max 0 (p4Q2PZ37AGN_originalWilsonMeanTable grid mass a geometry).lower
  upper := min (2 * (periodicHypercubicEvenSpatialSlicePlaquetteList H).length)
    (p4Q2PZ37AGN_originalWilsonMeanTable grid mass a geometry).upper
  hLower := by
    have h := max_le (p4Q2PZ37AFZ_originalWilsonMean_bounds H).1
      (p4Q2PZ37AGN_originalWilsonMean_bounds grid mass a geometry hGeometry).1
    simpa using h
  hUpper := by
    have h := le_min (p4Q2PZ37AFZ_originalWilsonMean_bounds H).2
      (p4Q2PZ37AGN_originalWilsonMean_bounds grid mass a geometry hGeometry).2
    simpa [p4Q2PZ37AFZ_plaquetteCount] using h

/-- The established AFQ product cells, actual centers and actual full
spatial chordal radius presented directly in AGH's original-grid type. -/
def p4Q2PZ37AGN_original24Grid (H : ℕ) :
    p4Q2PZ37AGH_originalSpatialGrid H where
  n := (p4Q2PZ37AGD_toAGCOriginalHaarCells H).n
  cell := (p4Q2PZ37AGD_toAGCOriginalHaarCells H).cell
  hMeas := (p4Q2PZ37AGD_toAGCOriginalHaarCells H).hMeas
  hPartition := (p4Q2PZ37AGD_toAGCOriginalHaarCells H).hPartition
  center := p4Q2PZ37AGE_spatialProductCenter H
  radius := p4Q2PZ37AGG_originalCellChordalRadius H
  radius_nonneg := p4Q2PZ37AGG_originalCellChordalRadius_nonneg H
  hRadius := p4Q2PZ37AGG_originalCell_spatialDistance_le H

/-- Concrete true product-Haar mass endpoints for every original AFQ
spatial cell; their proof is AGD's product of genuine one-link masses. -/
def p4Q2PZ37AGN_original24MassIntervals (H : ℕ) :
    p4Q2PZ37AGN_massIntervals (p4Q2PZ37AGN_original24Grid H) where
  lower := fun _ => p4Q2PZ37AGD_rationalLower H
  upper := fun _ => p4Q2PZ37AGD_rationalUpper H
  hLower := fun i =>
    (p4Q2PZ37AGD_spatialCell_HaarMass_interval H (p4Q2PZ37AGD_indexFromFin H i)).1
  hUpper := fun i =>
    (p4Q2PZ37AGD_spatialCell_HaarMass_interval H (p4Q2PZ37AGD_indexFromFin H i)).2

/-- Rational data equal to the original geometric radius; no rounding
or rational-density choice is used. -/
def p4Q2PZ37AGN_original24Radius (H : ℕ) : ℚ :=
  (4 / 5 : ℚ) * Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)

theorem p4Q2PZ37AGN_original24Radius_exact (H : ℕ) :
    (p4Q2PZ37AGN_original24Radius H : ℝ) =
      (p4Q2PZ37AGN_original24Grid H).radius := by
  simp [p4Q2PZ37AGN_original24Radius, p4Q2PZ37AGN_original24Grid,
    p4Q2PZ37AGG_originalCellChordalRadius]

/-- Every actual spatial center is composed of the existing original
AFQ centers, carrying AGL's exact rational coordinate witnesses. -/
def p4Q2PZ37AGN_original24Center_rational (H : ℕ)
    (i : Fin (p4Q2PZ37AGN_original24Grid H).n)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    p4Q2PZ37AGL_rationalCoordinates
      ((p4Q2PZ37AGN_original24Grid H).center i e) :=
  p4Q2PZ37AGL_originalCenter_rational (p4Q2PZ37AGD_indexFromFin H i e)

/-- An unconditional quadrature enclosure of the ORIGINAL centering
mean, from actual finite rational Wilson actions and certified Haar cells. -/
def p4Q2PZ37AGN_original24WilsonMeanInterval (H : ℕ) :
    p4Q2PZ37AFV_verifiedInterval (p4Q2PZ37AFZ_originalWilsonMean H) :=
  p4Q2PZ37AGN_originalWilsonMeanInterval
    (p4Q2PZ37AGN_original24Grid H) (p4Q2PZ37AGN_original24MassIntervals H)
    (p4Q2PZ37AGN_original24Center_rational H)
    (24 * p4Q2PZ37AGN_original24Radius H) (by
      simpa only [Rat.cast_mul, Rat.cast_ofNat, p4Q2PZ37AGN_original24Radius_exact]
        using (le_refl (24 * (p4Q2PZ37AGN_original24Grid H).radius)))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_massIntervals.toHaarCells
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_massIntervals.total_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_massIntervals.integral_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_massIntervals.intersect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalWilsonAction_allLinkSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalWilsonMean_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_originalWilsonMeanInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24Grid
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24MassIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24Radius_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24Center_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGN_original24WilsonMeanInterval
