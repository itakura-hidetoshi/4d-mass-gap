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

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGV_signedCell_width_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGV_realFiniteWidth_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGV_rationalWidth_sum
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGV_rationalTable_width_le
