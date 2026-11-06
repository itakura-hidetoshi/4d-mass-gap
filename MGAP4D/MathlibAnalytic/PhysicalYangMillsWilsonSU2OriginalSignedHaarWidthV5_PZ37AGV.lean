import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPrecisionCarryingFineGridV5_PZ37AGU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGV — true-mass signed interval-width inequality

The original AGI evaluator uses min/max signed products and permits a
negative lower rational Haar endpoint. This new leaf first proves an
algebraic width estimate using the ACTUAL real mass between those endpoints.
A finite partition normalized by its true mass then gives a width bound
in terms of cell oscillations and the sum of mass-interval errors.

No assumption that rational mass endpoints sum to one, and no
positive-part substitution for the signed original transfer.
-/ 

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Signed min/max multiplication: both endpoints may be negative.
The true mass p is used as the common comparison point, and M is a
certified absolute bound on the two signed sample endpoints. -/
theorem p4Q2PZ37AGV_signedCell_width_le
    (a b ml mu p M : ℝ)
    (hlo : ml ≤ p) (hhi : p ≤ mu) (hM : 0 ≤ M)
    (ha : -M ≤ a ∧ a ≤ M) (hb : -M ≤ b ∧ b ≤ M) :
    max (b * ml) (b * mu) - min (a * ml) (a * mu) ≤
      (b - a) * p + 2 * M * (mu - ml) := by
  have hpml : 0 ≤ p - ml := sub_nonneg.mpr hlo
  have hmup : 0 ≤ mu - p := sub_nonneg.mpr hhi
  have h1 : 0 ≤ (b + M) * (p - ml) := by
    apply mul_nonneg (by linarith only [hb.1]) hpml
  have h2 : 0 ≤ M * (mu - p) := mul_nonneg hM hmup
  have hb1 : b * ml ≤ b * p + M * (mu - ml) := by
    nlinarith only [h1, h2]
  have h3 : 0 ≤ (M - b) * (mu - p) := by
    apply mul_nonneg (by linarith only [hb.2]) hmup
  have h4 : 0 ≤ M * (p - ml) := mul_nonneg hM hpml
  have hb2 : b * mu ≤ b * p + M * (mu - ml) := by
    nlinarith only [h3, h4]
  have h5 : 0 ≤ (M - a) * (p - ml) := by
    apply mul_nonneg (by linarith only [ha.2]) hpml
  have ha1 : a * p - M * (mu - ml) ≤ a * ml := by
    nlinarith only [h5, h2]
  have h6 : 0 ≤ (M + a) * (mu - p) := by
    apply mul_nonneg (by linarith only [ha.1]) hmup
  have ha2 : a * p - M * (mu - ml) ≤ a * mu := by
    nlinarith only [h6, h4]
  calc
    max (b * ml) (b * mu) - min (a * ml) (a * mu) ≤
        (b * p + M * (mu - ml)) - (a * p - M * (mu - ml)) :=
      sub_le_sub (max_le hb1 hb2) (le_min ha1 ha2)
    _ = (b - a) * p + 2 * M * (mu - ml) := by ring

/-- The exact finite signed AGI arithmetic, with true (not surrogate)
nonnegative cell masses summing to one. No restriction on the sign
of any rational lower mass endpoint is used. -/
theorem p4Q2PZ37AGV_realFiniteWidth_le
    {N : ℕ} (a b ml mu p : Fin N → ℝ) (M A eps : ℝ)
    (hM : 0 ≤ M)
    (hMassLo : ∀ i, ml i ≤ p i)
    (hMassHi : ∀ i, p i ≤ mu i)
    (hMassNonneg : ∀ i, 0 ≤ p i)
    (hMassTotal : (∑ i : Fin N, p i) = 1)
    (ha : ∀ i, -M ≤ a i ∧ a i ≤ M)
    (hb : ∀ i, -M ≤ b i ∧ b i ≤ M)
    (hCellWidths : ∀ i, b i - a i ≤ A)
    (hMassWidths : (∑ i : Fin N, (mu i - ml i)) ≤ eps) :
    (∑ i : Fin N, max (b i * ml i) (b i * mu i)) -
      (∑ i : Fin N, min (a i * ml i) (a i * mu i)) ≤
        A + 2 * M * eps := by
  have hEach (i : Fin N) :
      max (b i * ml i) (b i * mu i) -
          min (a i * ml i) (a i * mu i) ≤
        A * p i + 2 * M * (mu i - ml i) := by
    have hs := p4Q2PZ37AGV_signedCell_width_le
      (a i) (b i) (ml i) (mu i) (p i) M
      (hMassLo i) (hMassHi i) hM (ha i) (hb i)
    have hw := mul_le_mul_of_nonneg_right (hCellWidths i) (hMassNonneg i)
    linarith only [hs, hw]
  calc
    (∑ i : Fin N, max (b i * ml i) (b i * mu i)) -
        (∑ i : Fin N, min (a i * ml i) (a i * mu i)) =
        (∑ i : Fin N,
          (max (b i * ml i) (b i * mu i) -
            min (a i * ml i) (a i * mu i))) := by
          rw [Finset.sum_sub_distrib]
    _ ≤ (∑ i : Fin N, (A * p i + 2 * M * (mu i - ml i))) := by
      exact Finset.sum_le_sum (fun i _ => hEach i)
    _ = A * (∑ i : Fin N, p i) +
          2 * M * (∑ i : Fin N, (mu i - ml i)) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = A + 2 * M * (∑ i : Fin N, (mu i - ml i)) := by
      rw [hMassTotal]
      ring
    _ ≤ A + 2 * M * eps := by
      have h2 : 0 ≤ 2 * M := mul_nonneg (by norm_num) hM
      exact add_le_add_left (mul_le_mul_of_nonneg_left hMassWidths h2) A

/-- The literal rational table has width equal to the sum of its
signed per-cell max-minus-min contributions. -/
theorem p4Q2PZ37AGV_rationalWidth_sum {N : ℕ}
    (d : p4Q2PZ37AGI_rationalTable N) :
    d.upper - d.lower =
      ∑ i : Fin N, (max (d.cellUpper i * d.massLower i)
        (d.cellUpper i * d.massUpper i) -
        min (d.cellLower i * d.massLower i)
          (d.cellLower i * d.massUpper i)) := by
  simp only [p4Q2PZ37AGI_rationalTable.upper,
    p4Q2PZ37AGI_rationalTable.lower, Finset.sum_sub_distrib]

/-- A true-mass partition certificate for the literal AGI signed table:
no positivity premise on lower or upper rational mass endpoints. -/
theorem p4Q2PZ37AGV_rationalTable_width_le
    {N : ℕ} (d : p4Q2PZ37AGI_rationalTable N)
    (p : Fin N → ℝ) (M A eps : ℚ)
    (hM : 0 ≤ M)
    (hMassLo : ∀ i, (d.massLower i : ℝ) ≤ p i)
    (hMassHi : ∀ i, p i ≤ (d.massUpper i : ℝ))
    (hMassNonneg : ∀ i, 0 ≤ p i)
    (hMassTotal : (∑ i : Fin N, p i) = 1)
    (ha : ∀ i, -M ≤ d.cellLower i ∧ d.cellLower i ≤ M)
    (hb : ∀ i, -M ≤ d.cellUpper i ∧ d.cellUpper i ≤ M)
    (hCellWidths : ∀ i, d.cellUpper i - d.cellLower i ≤ A)
    (hMassWidths :
      (∑ i : Fin N, (d.massUpper i - d.massLower i)) ≤ eps) :
    d.upper - d.lower ≤ A + 2 * M * eps := by
  have hReal := p4Q2PZ37AGV_realFiniteWidth_le
    (fun i => (d.cellLower i : ℝ)) (fun i => (d.cellUpper i : ℝ))
    (fun i => (d.massLower i : ℝ)) (fun i => (d.massUpper i : ℝ))
    p (M : ℝ) (A : ℝ) (eps : ℝ)
    (by exact_mod_cast hM)
    hMassLo hMassHi hMassNonneg hMassTotal
    (by intro i; constructor
      · exact_mod_cast (ha i).1
      · exact_mod_cast (ha i).2)
    (by intro i; constructor
      · exact_mod_cast (hb i).1
      · exact_mod_cast (hb i).2)
    (by intro i; exact_mod_cast hCellWidths i)
    (by exact_mod_cast hMassWidths)
  have hCast : ((d.upper - d.lower : ℚ) : ℝ) =
      (∑ i : Fin N,
        max ((d.cellUpper i : ℝ) * (d.massLower i : ℝ))
            ((d.cellUpper i : ℝ) * (d.massUpper i : ℝ))) -
      (∑ i : Fin N,
        min ((d.cellLower i : ℝ) * (d.massLower i : ℝ))
            ((d.cellLower i : ℝ) * (d.massUpper i : ℝ))) := by
    simp [p4Q2PZ37AGI_rationalTable.upper,
      p4Q2PZ37AGI_rationalTable.lower]
  have hResult : ((d.upper - d.lower : ℚ) : ℝ) ≤
      ((A + 2 * M * eps : ℚ) : ℝ) := by
    rw [hCast]
    push_cast
    exact hReal
  exact_mod_cast hResult


local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGV_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGV_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGV_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGV_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGV_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "gCont" => p4Q2PZ37AGE_originalContinuousIntegrand H

local instance p4Q2PZ37AGV_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AGV_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Actual original source/kernel geometry has a single certified
rational slope cap, independent of cell and right boundary. -/
def p4Q2PZ37AGV_uniformSlope (m : ℕ) : ℚ :=
  6 + 13 * p4Q2PZ37AGK_upper m * (p4Q2PZ37AGN_countRational H / 2)

theorem p4Q2PZ37AGV_uniformSlope_nonneg (m : ℕ) :
    0 ≤ p4Q2PZ37AGV_uniformSlope H m := by
  have hbReal : (0 : ℝ) ≤ (p4Q2PZ37AGK_upper m : ℝ) :=
    p4Q2PZ37ADC_fixedCoupling_pos.le.trans
      (p4Q2PZ37AGK_originalCoupling_bounds m).2
  have hb : (0 : ℚ) ≤ p4Q2PZ37AGK_upper m := by
    exact_mod_cast hbReal
  have hc : (0 : ℚ) ≤ p4Q2PZ37AGN_countRational H := by
    unfold p4Q2PZ37AGN_countRational
    positivity
  have hdiv : 0 ≤ p4Q2PZ37AGN_countRational H / (2 : ℚ) :=
    div_nonneg hc (by norm_num)
  unfold p4Q2PZ37AGV_uniformSlope
  exact add_nonneg (by norm_num)
    (mul_nonneg (mul_nonneg (by norm_num) hb) hdiv)

/-- The real global integrand envelope implies the rational AGN
transfer radius is nonnegative. This uses the existing ORIGINAL
pointwise inequality rather than introducing a new bound. -/
theorem p4Q2PZ37AGV_transferRadius_nonneg
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AGN_transferRadius H m n hn := by
  let C : Cfg := fun _ => 1
  have habs :=
    p4Q2PZ37AGO_originalIntegrand_abs_le_radius H C C m n hn
  have hreal : (0 : ℝ) ≤
      (p4Q2PZ37AGN_transferRadius H m n hn : ℝ) :=
    (abs_nonneg (gCont C C)).trans habs
  exact_mod_cast hreal

/-- The actual selected AGU data has the requested uniform cell
geometry budget, and each source-adapted AGP cell oscillation budget
is bounded by the same original rational slope cap times R. -/
theorem p4Q2PZ37AGV_cellBudget_le
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (hR : 0 ≤ R) (m n : ℕ) (hn : 0 < n)
    (i : Fin d.data.grid.n) :
    p4Q2PZ37AGP_cellBudget H d.data m n hn i ≤
      p4Q2PZ37AGV_uniformSlope H m * R := by
  unfold p4Q2PZ37AGP_cellBudget
  rw [d.hCellRadius i]
  exact mul_le_mul_of_nonneg_right
    (p4Q2PZ37AGP_rationalCenterSlope_le_uniform
      H (d.data.grid.center i) (d.data.centerCoordinates i) m n hn) hR

/-- The clipped original cell bounds stay within the genuine global
envelope even though its rational mass lower endpoint may be negative.
An external bound eta is needed only for the center interval widths. -/
theorem p4Q2PZ37AGV_cellEndpoints_and_width
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (hR : 0 ≤ R)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (eta : ℚ)
    (hCenterWidth : ∀ i : Fin d.data.grid.n,
      (p4Q2PZ37AGN_originalIntegrandInterval H (d.data.grid.center i) B
        (d.data.centerCoordinates i) b m n hn).upper -
      (p4Q2PZ37AGN_originalIntegrandInterval H (d.data.grid.center i) B
        (d.data.centerCoordinates i) b m n hn).lower ≤ eta)
    (i : Fin d.data.grid.n) :
    let M := p4Q2PZ37AGN_transferRadius H m n hn
    let L := p4Q2PZ37AGV_uniformSlope H m
    let lo := p4Q2PZ37AGP_cellLower H d.data B b m n hn i
    let hi := p4Q2PZ37AGP_cellUpper H d.data B b m n hn i
    (-M ≤ lo ∧ lo ≤ M) ∧
      (-M ≤ hi ∧ hi ≤ M) ∧
      hi - lo ≤ eta + 2 * L * R := by
  let M := p4Q2PZ37AGN_transferRadius H m n hn
  let L := p4Q2PZ37AGV_uniformSlope H m
  let c := p4Q2PZ37AGN_originalIntegrandInterval H
    (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn
  let budget := p4Q2PZ37AGP_cellBudget H d.data m n hn i
  let lo := p4Q2PZ37AGP_cellLower H d.data B b m n hn i
  let hi := p4Q2PZ37AGP_cellUpper H d.data B b m n hn i
  have hM : 0 ≤ M := p4Q2PZ37AGV_transferRadius_nonneg H m n hn
  have hBudget : 0 ≤ budget :=
    p4Q2PZ37AGP_cellBudget_nonneg H d.data m n hn i
  have hPoint := abs_le.mp
    (p4Q2PZ37AGO_originalIntegrand_abs_le_radius H B (d.data.grid.center i) m n hn)
  have hLowM : c.lower ≤ M := by
    have h : (c.lower : ℝ) ≤ (M : ℝ) := c.hLower.trans hPoint.2
    exact_mod_cast h
  have hHighM : -M ≤ c.upper := by
    have h : (-(M : ℝ)) ≤ (c.upper : ℝ) := hPoint.1.trans c.hUpper
    exact_mod_cast h
  have hLower1 : -M ≤ lo := by
    change -M ≤ max (-M) (c.lower - budget)
    exact le_max_left _ _
  have hLower2 : lo ≤ M := by
    change max (-M) (c.lower - budget) ≤ M
    apply max_le
    · linarith only [hM]
    · linarith only [hLowM, hBudget]
  have hUpper1 : -M ≤ hi := by
    change -M ≤ min M (c.upper + budget)
    apply le_min
    · linarith only [hM]
    · linarith only [hHighM, hBudget]
  have hUpper2 : hi ≤ M := by
    change min M (c.upper + budget) ≤ M
    exact min_le_left _ _
  have hLowClip : c.lower - budget ≤ lo := by
    change c.lower - budget ≤ max (-M) (c.lower - budget)
    exact le_max_right _ _
  have hHighClip : hi ≤ c.upper + budget := by
    change min M (c.upper + budget) ≤ c.upper + budget
    exact min_le_right _ _
  have hCenter : c.upper - c.lower ≤ eta := hCenterWidth i
  have hLocal := p4Q2PZ37AGV_cellBudget_le H d hR m n hn i
  have hWidth : hi - lo ≤ eta + 2 * L * R := by
    linarith only [hLowClip, hHighClip, hCenter, hLocal]
  exact ⟨⟨hLower1, hLower2⟩, ⟨hUpper1, hUpper2⟩, hWidth⟩

/-- The ORIGINAL signed-transfer AGP evaluator has a quantitative width
bound from the SAME precision-indexed genuine spatial grid, original
product Haar masses and rational center values. The only remaining
hypothesis is a certified center-value interval width eta. -/
theorem p4Q2PZ37AGV_originalRawTransferWidth_le
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (hR : 0 ≤ R)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (eta : ℚ) (heta : 0 ≤ eta)
    (hCenterWidth : ∀ i : Fin d.data.grid.n,
      (p4Q2PZ37AGN_originalIntegrandInterval H (d.data.grid.center i) B
        (d.data.centerCoordinates i) b m n hn).upper -
      (p4Q2PZ37AGN_originalIntegrandInterval H (d.data.grid.center i) B
        (d.data.centerCoordinates i) b m n hn).lower ≤ eta) :
    (p4Q2PZ37AGP_originalRawInterval H d.data B b m n hn).upper -
      (p4Q2PZ37AGP_originalRawInterval H d.data B b m n hn).lower ≤
      eta + 2 * p4Q2PZ37AGV_uniformSlope H m * R +
        2 * p4Q2PZ37AGN_transferRadius H m n hn * eps := by
  let tbl := p4Q2PZ37AGP_originalTable H d.data B b m n hn
  let M := p4Q2PZ37AGN_transferRadius H m n hn
  let L := p4Q2PZ37AGV_uniformSlope H m
  have hM : 0 ≤ M := p4Q2PZ37AGV_transferRadius_nonneg H m n hn
  have hL : 0 ≤ L := p4Q2PZ37AGV_uniformSlope_nonneg H m
  have hA : 0 ≤ eta + 2 * L * R := by
    have hp : 0 ≤ 2 * L * R :=
      mul_nonneg (mul_nonneg (by norm_num) hL) hR
    exact add_nonneg heta hp
  have hEval : tbl.upper - tbl.lower ≤
      (eta + 2 * L * R) + 2 * M * eps := by
    apply p4Q2PZ37AGV_rationalTable_width_le tbl
      (fun i => Measure.real muH (d.data.grid.cell i))
      M (eta + 2 * L * R) eps hM
    · intro i
      change (d.data.masses.lower i : ℝ) ≤ Measure.real muH (d.data.grid.cell i)
      exact d.data.masses.hLower i
    · intro i
      change Measure.real muH (d.data.grid.cell i) ≤ (d.data.masses.upper i : ℝ)
      exact d.data.masses.hUpper i
    · intro i
      exact Measure.real_nonneg
    · exact d.data.masses.total_mass
    · intro i
      have h := (p4Q2PZ37AGV_cellEndpoints_and_width H d hR
        B b m n hn eta hCenterWidth i).1
      simpa [tbl, p4Q2PZ37AGP_originalTable,
        p4Q2PZ37AGN_massIntervals.toTable,
        p4Q2PZ37AGI_rationalTable.cellLower] using h
    · intro i
      have h := (p4Q2PZ37AGV_cellEndpoints_and_width H d hR
        B b m n hn eta hCenterWidth i).2.1
      simpa [tbl, p4Q2PZ37AGP_originalTable,
        p4Q2PZ37AGN_massIntervals.toTable,
        p4Q2PZ37AGI_rationalTable.cellUpper] using h
    · intro i
      have h := (p4Q2PZ37AGV_cellEndpoints_and_width H d hR
        B b m n hn eta hCenterWidth i).2.2
      simpa [tbl, p4Q2PZ37AGP_originalTable,
        p4Q2PZ37AGN_massIntervals.toTable,
        p4Q2PZ37AGI_rationalTable.cellUpper,
        p4Q2PZ37AGI_rationalTable.cellLower] using h
    · simpa [tbl, p4Q2PZ37AGP_originalTable,
        p4Q2PZ37AGN_massIntervals.toTable] using d.hTotalMassWidth
  simpa [tbl, p4Q2PZ37AGP_originalRawInterval,
    add_assoc] using hEval

end GroundStatePosteriorJoint

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGV_signedCell_width_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGV_realFiniteWidth_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGV_rationalWidth_sum
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGV_rationalTable_width_le

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGV_uniformSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGV_transferRadius_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGV_cellBudget_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGV_cellEndpoints_and_width
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGV_originalRawTransferWidth_le
