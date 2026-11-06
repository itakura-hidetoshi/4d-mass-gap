import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFiniteCenterMaximumV5_PZ37AGX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGY — source envelope times genuine kernel/floor width maxima

AGX replaces its external eta hypothesis by the exact finite maximum of
the actual original AGN center-value interval widths on the SAME chosen
AGU precision-carrying grid. AGW proved each width is exactly
  |original centered source| * (original clipped kernel width
    + original global floor width / 2).

This append-only leaf uses the existing exact Haar-centering source bound
|s_H(C)| <= p_H/2 to separate source magnitude from the TWO genuinely
refinable physical interval widths. It forms the true finite maximum of
the original clipped Wilson kernel widths on the same original grid.

The result adds no external source, kernel or floor bounds. The selected
finite grid remains classical and noncomputable; no evaluation of large
volumes or proof of vanishing kernel/floor width is asserted. In particular
a bounded maximum is not itself a convergence certificate.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2

local instance p4Q2PZ37AGY_links : Fintype Link := Fintype.ofFinite _

/-- Exactly the width of the genuine original AGN global floor interval.
The same interval object is used at every center. -/
def p4Q2PZ37AGY_originalFloorWidth (m n : ℕ) (hn : 0 < n) : ℚ :=
  let fl := p4Q2PZ37AGN_originalFloorInterval H m n hn
  fl.upper - fl.lower

/-- No new floor assumption: the actual original global floor lies
between the rational endpoints of the SAME verified interval. -/
theorem p4Q2PZ37AGY_originalFloorWidth_nonneg (m n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AGY_originalFloorWidth H m n hn := by
  let fl := p4Q2PZ37AGN_originalFloorInterval H m n hn
  have hReal : (fl.lower : ℝ) ≤ (fl.upper : ℝ) := fl.hLower.trans fl.hUpper
  have hRat : fl.lower ≤ fl.upper := by exact_mod_cast hReal
  exact sub_nonneg.mpr hRat

/-- The original Wilson kernel width for the ACTUAL chosen rational center
and the original rational right boundary, not a hypothetical center. -/
def p4Q2PZ37AGY_originalKernelWidth
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.data.grid.n) : ℚ :=
  let ker := p4Q2PZ37AGM_originalClippedKernelInterval H
    (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn
  ker.upper - ker.lower

/-- The interval belongs to the original physical Wilson kernel,
therefore its width is nonnegative even without any approximate sign. -/
theorem p4Q2PZ37AGY_originalKernelWidth_nonneg
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.data.grid.n) :
    0 ≤ p4Q2PZ37AGY_originalKernelWidth H d B b m n hn i := by
  let ker := p4Q2PZ37AGM_originalClippedKernelInterval H
    (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn
  have hReal : (ker.lower : ℝ) ≤ (ker.upper : ℝ) :=
    ker.hLower.trans ker.hUpper
  have hRat : ker.lower ≤ ker.upper := by exact_mod_cast hReal
  exact sub_nonneg.mpr hRat

/-- The finite supremum of EXACT original clipped-kernel interval widths,
formed on the SAME nonempty AGU spatial Borel partition as AGX. -/
def p4Q2PZ37AGY_originalKernelMax
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : ℚ :=
  (Finset.univ : Finset (Fin d.data.grid.n)).sup'
    (p4Q2PZ37AGX_univNonempty H d)
    (fun i => p4Q2PZ37AGY_originalKernelWidth H d B b m n hn i)

/-- Every actual center's kernel width is controlled by its same-grid
finite maximum. No factor proportional to the number of cells arises. -/
theorem p4Q2PZ37AGY_originalKernelWidth_le_max
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.data.grid.n) :
    p4Q2PZ37AGY_originalKernelWidth H d B b m n hn i ≤
      p4Q2PZ37AGY_originalKernelMax H d B b m n hn := by
  exact Finset.le_sup'
    (s := (Finset.univ : Finset (Fin d.data.grid.n)))
    (f := fun j => p4Q2PZ37AGY_originalKernelWidth H d B b m n hn j)
    (Finset.mem_univ i)

/-- The maximum is nonnegative, witnessed by an actual original cell. -/
theorem p4Q2PZ37AGY_originalKernelMax_nonneg
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AGY_originalKernelMax H d B b m n hn := by
  obtain ⟨i, _⟩ := p4Q2PZ37AGX_univNonempty H d
  exact (p4Q2PZ37AGY_originalKernelWidth_nonneg H d B b m n hn i).trans
    (p4Q2PZ37AGY_originalKernelWidth_le_max H d B b m n hn i)

/-- The genuine centered Wilson source has the precise rational
half-plaquette-count bound, using the unchanged original real source
and AGN's exact rational center identification. -/
theorem p4Q2PZ37AGY_originalCenterSource_bound
    (A : Cfg) (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e)) :
    |p4Q2PZ37AGN_centeredSourceRational H A a| ≤
      p4Q2PZ37AGN_countRational H / 2 := by
  have hsReal := p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A
  rw [p4Q2PZ37AGN_centeredSourceRational_exact H A a,
    ← p4Q2PZ37AGN_countRational_exact H] at hsReal
  exact_mod_cast hsReal

/-- The original source envelope is nonnegative by its literal
plaquette-count definition. -/
theorem p4Q2PZ37AGY_sourceEnvelope_nonneg :
    0 ≤ p4Q2PZ37AGN_countRational H / (2 : ℚ) := by
  unfold p4Q2PZ37AGN_countRational
  positivity

/-- The original AGW center width is bounded by one common, genuinely
defined kernel maximum and the original global floor interval width. -/
theorem p4Q2PZ37AGY_centerWidth_le_components
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (i : Fin d.data.grid.n) :
    p4Q2PZ37AGW_centerWidthFormula H
      (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn ≤
      (p4Q2PZ37AGN_countRational H / 2) *
        (p4Q2PZ37AGY_originalKernelMax H d B b m n hn +
          p4Q2PZ37AGY_originalFloorWidth H m n hn / 2) := by
  let s := p4Q2PZ37AGN_centeredSourceRational H
    (d.data.grid.center i) (d.data.centerCoordinates i)
  let k := p4Q2PZ37AGY_originalKernelWidth H d B b m n hn i
  let kMax := p4Q2PZ37AGY_originalKernelMax H d B b m n hn
  let fl := p4Q2PZ37AGY_originalFloorWidth H m n hn
  let p := p4Q2PZ37AGN_countRational H / (2 : ℚ)
  have hs : |s| ≤ p :=
    p4Q2PZ37AGY_originalCenterSource_bound H
      (d.data.grid.center i) (d.data.centerCoordinates i)
  have hp : 0 ≤ p := p4Q2PZ37AGY_sourceEnvelope_nonneg H
  have hk : 0 ≤ k := p4Q2PZ37AGY_originalKernelWidth_nonneg H d B b m n hn i
  have hf : 0 ≤ fl := p4Q2PZ37AGY_originalFloorWidth_nonneg H m n hn
  have hkMax : k ≤ kMax :=
    p4Q2PZ37AGY_originalKernelWidth_le_max H d B b m n hn i
  have hnonneg : 0 ≤ k + fl / 2 :=
    add_nonneg hk (div_nonneg hf (by norm_num))
  have h1 : |s| * (k + fl / 2) ≤ p * (k + fl / 2) :=
    mul_le_mul_of_nonneg_right hs hnonneg
  have hAdd : k + fl / 2 ≤ kMax + fl / 2 := by
    linarith only [hkMax]
  have h2 : p * (k + fl / 2) ≤ p * (kMax + fl / 2) :=
    mul_le_mul_of_nonneg_left hAdd hp
  exact h1.trans h2

/-- Eliminate the AGX center maximum from the inequality in favor of
the original Wilson source envelope and two genuine interval widths. -/
theorem p4Q2PZ37AGY_actualCenterMax_le_components
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGX_actualCenterMax H d B b m n hn ≤
      (p4Q2PZ37AGN_countRational H / 2) *
        (p4Q2PZ37AGY_originalKernelMax H d B b m n hn +
          p4Q2PZ37AGY_originalFloorWidth H m n hn / 2) := by
  unfold p4Q2PZ37AGX_actualCenterMax
  apply Finset.sup'_le
  intro i _hi
  exact p4Q2PZ37AGY_centerWidth_le_components H d B b m n hn i

/-- The SAME AGU precision-carrying grid and the SAME original physical
signed transfer satisfy a decomposed finite kernel/floor error estimate.
All terms are actual original model certificates; none is an oracle. -/
theorem p4Q2PZ37AGY_fineOriginalTransferWidth_le
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).upper -
      (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).lower ≤
      (p4Q2PZ37AGN_countRational H / 2) *
        (p4Q2PZ37AGY_originalKernelMax H
          (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps) B b m n hn +
          p4Q2PZ37AGY_originalFloorWidth H m n hn / 2) +
        2 * p4Q2PZ37AGV_uniformSlope H m * R +
        2 * p4Q2PZ37AGN_transferRadius H m n hn * eps := by
  let d := p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps
  have hOld := p4Q2PZ37AGX_fineOriginalTransferWidth_le
    H R eps hR heps B b m n hn
  have hMax := p4Q2PZ37AGY_actualCenterMax_le_components H
    d B b m n hn
  linarith only [hOld, hMax]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGY_originalFloorWidth_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGY_originalKernelWidth_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGY_originalKernelWidth_le_max
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGY_originalKernelMax_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGY_originalCenterSource_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGY_sourceEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGY_centerWidth_le_components
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGY_actualCenterMax_le_components
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGY_fineOriginalTransferWidth_le
