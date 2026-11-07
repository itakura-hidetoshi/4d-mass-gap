import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSignedTransferSignCertificatesV5_PZ37AHD
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHE — genuine signed Haar midpoint/error budgets

This append-only leaf algebraically separates the ACTUAL AGP signed rational
Haar table into its rational midpoint contribution and the strictly
nonnegative mass-interval uncertainty.  It does not introduce an
independent grid, new source, kernel, floor, physical transfer, or Haar law.

For a true-Haar cell mass interval [l,u] and signed cell bound a,

  min (a*l) (a*u) = a*(l+u)/2 - |a|*(u-l)/2
  max (a*l) (a*u) = a*(l+u)/2 + |a|*(u-l)/2.

These are exact rational identities, including negative cell contributions.
Consequently the original AGP sign condition is a finite rational strict
midpoint-versus-uncertainty comparison. A Boolean checker can be applied
to genuine proof-carrying AGP data, including the original 24-center grid
and the precision-indexed AGU fine grid.

AHE also proves checker soundness for the unchanged original physical
signed transfer, and connects the fine-grid checkers to AHD completeness.
It does NOT compute a strict sign for any concrete boundary; the
noncomputably chosen AGU Haar cells are not misrepresented as executable
numerical output. The original two-sign shell, H-uniform coercivity and
continuum Yang--Mills mass gap remain unproved.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Exact sign-sensitive lower product decomposition for one true-Haar
mass interval, including a negative cell coefficient. -/
theorem p4Q2PZ37AHE_minProduct_midpoint
    (a l u : ℚ) (hMass : l ≤ u) :
    min (a * l) (a * u) =
      a * ((l + u) / 2) - |a| * ((u - l) / 2) := by
  rcases le_total (0 : ℚ) a with ha | ha
  · have hProd : a * l ≤ a * u := mul_le_mul_of_nonneg_left hMass ha
    rw [min_eq_left hProd, abs_of_nonneg ha]
    ring
  · have hProd : a * u ≤ a * l := mul_le_mul_of_nonpos_left hMass ha
    rw [min_eq_right hProd, abs_of_nonpos ha]
    ring

/-- Exact sign-sensitive upper product decomposition; unlike an unsigned
mass approximation, a negative coefficient reverses the mass endpoint. -/
theorem p4Q2PZ37AHE_maxProduct_midpoint
    (a l u : ℚ) (hMass : l ≤ u) :
    max (a * l) (a * u) =
      a * ((l + u) / 2) + |a| * ((u - l) / 2) := by
  rcases le_total (0 : ℚ) a with ha | ha
  · have hProd : a * l ≤ a * u := mul_le_mul_of_nonneg_left hMass ha
    rw [max_eq_right hProd, abs_of_nonneg ha]
    ring
  · have hProd : a * u ≤ a * l := mul_le_mul_of_nonpos_left hMass ha
    rw [max_eq_left hProd, abs_of_nonpos ha]
    ring

/-- Rational midpoint of a finite AGI table's actual mass endpoints. -/
def p4Q2PZ37AHE_massMid {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n) (i : Fin n) : ℚ :=
  (d.massLower i + d.massUpper i) / 2

/-- Rational half-width of the same true-Haar mass interval. -/
def p4Q2PZ37AHE_massHalfWidth {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n) (i : Fin n) : ℚ :=
  (d.massUpper i - d.massLower i) / 2

/-- Lower signed midpoint moment using AGP's ORIGINAL cell lower values. -/
def p4Q2PZ37AHE_lowerMoment {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n) : ℚ :=
  ∑ i : Fin n, d.cellLower i * p4Q2PZ37AHE_massMid d i

/-- Lower nonnegative absolute-mass error; signs are not discarded. -/
def p4Q2PZ37AHE_lowerError {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n) : ℚ :=
  ∑ i : Fin n, |d.cellLower i| * p4Q2PZ37AHE_massHalfWidth d i

/-- Upper signed midpoint moment from the original cell upper values. -/
def p4Q2PZ37AHE_upperMoment {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n) : ℚ :=
  ∑ i : Fin n, d.cellUpper i * p4Q2PZ37AHE_massMid d i

/-- Upper absolute-mass error using the same genuine mass endpoints. -/
def p4Q2PZ37AHE_upperError {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n) : ℚ :=
  ∑ i : Fin n, |d.cellUpper i| * p4Q2PZ37AHE_massHalfWidth d i

/-- Exact lower evaluator identity for ANY finite rational AGI table
whose supplied mass endpoints are ordered. In particular this applies
to AGP's actual original signed-Haar table without replacing it. -/
theorem p4Q2PZ37AHE_tableLower_exact {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n)
    (hMass : ∀ i, d.massLower i ≤ d.massUpper i) :
    d.lower = p4Q2PZ37AHE_lowerMoment d - p4Q2PZ37AHE_lowerError d := by
  calc
    d.lower =
        ∑ i : Fin n, (d.cellLower i * p4Q2PZ37AHE_massMid d i -
          |d.cellLower i| * p4Q2PZ37AHE_massHalfWidth d i) := by
      unfold p4Q2PZ37AGI_rationalTable.lower
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [p4Q2PZ37AHE_massMid, p4Q2PZ37AHE_massHalfWidth] using
        p4Q2PZ37AHE_minProduct_midpoint (d.cellLower i)
          (d.massLower i) (d.massUpper i) (hMass i)
    _ = (∑ i : Fin n, d.cellLower i * p4Q2PZ37AHE_massMid d i) -
        (∑ i : Fin n, |d.cellLower i| * p4Q2PZ37AHE_massHalfWidth d i) := by
      rw [Finset.sum_sub_distrib]
    _ = p4Q2PZ37AHE_lowerMoment d - p4Q2PZ37AHE_lowerError d := rfl

/-- Exact upper evaluator identity; its uncertainty has the OPPOSITE
sign from the lower evaluator, even with mixed-sign integrands. -/
theorem p4Q2PZ37AHE_tableUpper_exact {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n)
    (hMass : ∀ i, d.massLower i ≤ d.massUpper i) :
    d.upper = p4Q2PZ37AHE_upperMoment d + p4Q2PZ37AHE_upperError d := by
  calc
    d.upper =
        ∑ i : Fin n, (d.cellUpper i * p4Q2PZ37AHE_massMid d i +
          |d.cellUpper i| * p4Q2PZ37AHE_massHalfWidth d i) := by
      unfold p4Q2PZ37AGI_rationalTable.upper
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [p4Q2PZ37AHE_massMid, p4Q2PZ37AHE_massHalfWidth] using
        p4Q2PZ37AHE_maxProduct_midpoint (d.cellUpper i)
          (d.massLower i) (d.massUpper i) (hMass i)
    _ = (∑ i : Fin n, d.cellUpper i * p4Q2PZ37AHE_massMid d i) +
        (∑ i : Fin n, |d.cellUpper i| * p4Q2PZ37AHE_massHalfWidth d i) := by
      rw [Finset.sum_add_distrib]
    _ = p4Q2PZ37AHE_upperMoment d + p4Q2PZ37AHE_upperError d := rfl

theorem p4Q2PZ37AHE_lowerError_nonneg {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n)
    (hMass : ∀ i, d.massLower i ≤ d.massUpper i) :
    0 ≤ p4Q2PZ37AHE_lowerError d := by
  unfold p4Q2PZ37AHE_lowerError
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (abs_nonneg _)
    (div_nonneg (sub_nonneg.mpr (hMass i)) (by norm_num))

theorem p4Q2PZ37AHE_upperError_nonneg {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n)
    (hMass : ∀ i, d.massLower i ≤ d.massUpper i) :
    0 ≤ p4Q2PZ37AHE_upperError d := by
  unfold p4Q2PZ37AHE_upperError
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (abs_nonneg _)
    (div_nonneg (sub_nonneg.mpr (hMass i)) (by norm_num))

/-- The actual finite table checker uses ONLY exact rational arithmetic. -/
def p4Q2PZ37AHE_positiveCheck {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n) : Bool :=
  decide (p4Q2PZ37AHE_lowerError d < p4Q2PZ37AHE_lowerMoment d)

def p4Q2PZ37AHE_negativeCheck {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n) : Bool :=
  decide (p4Q2PZ37AHE_upperMoment d + p4Q2PZ37AHE_upperError d < 0)

/-- The midpoint checker is EXACTLY AGP/AGI's original strict lower test,
not a synthetic sufficient condition or a changed physical quantity. -/
theorem p4Q2PZ37AHE_positiveCheck_iff {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n)
    (hMass : ∀ i, d.massLower i ≤ d.massUpper i) :
    p4Q2PZ37AHE_positiveCheck d = true ↔ 0 < d.lower := by
  rw [p4Q2PZ37AHE_tableLower_exact d hMass]
  simp [p4Q2PZ37AHE_positiveCheck, sub_pos]

theorem p4Q2PZ37AHE_negativeCheck_iff {n : ℕ}
    (d : p4Q2PZ37AGI_rationalTable n)
    (hMass : ∀ i, d.massLower i ≤ d.massUpper i) :
    p4Q2PZ37AHE_negativeCheck d = true ↔ d.upper < 0 := by
  rw [p4Q2PZ37AHE_tableUpper_exact d hMass]
  simp [p4Q2PZ37AHE_negativeCheck]

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "t" => decomposableOneSliceTransferIntegral H 2
  p4Q2PZ37ADC_fixedCoupling (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AHE_links : Fintype Link := Fintype.ofFinite _

/-- In the ACTUAL AGP original table the mass endpoints are sound bounds
on the SAME real Haar measure of each genuine original Borel cell. -/
theorem p4Q2PZ37AHE_originalTable_massOrdered
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    ∀ i, (p4Q2PZ37AGP_originalTable H d B b m n hn).massLower i ≤
      (p4Q2PZ37AGP_originalTable H d B b m n hn).massUpper i := by
  intro i
  change d.masses.lower i ≤ d.masses.upper i
  exact_mod_cast (d.masses.hLower i).trans (d.masses.hUpper i)

/-- Non-synthetic Boolean checker of the unchanged ORIGINAL signed
physical transfer: its table contains the true Borel/Haar evidence d. -/
def p4Q2PZ37AHE_originalPositiveCheck
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : Bool :=
  p4Q2PZ37AHE_positiveCheck (p4Q2PZ37AGP_originalTable H d B b m n hn)

def p4Q2PZ37AHE_originalNegativeCheck
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : Bool :=
  p4Q2PZ37AHE_negativeCheck (p4Q2PZ37AGP_originalTable H d B b m n hn)

/-- A checked positive rational midpoint surplus strictly certifies the
UNCHANGED original signed transfer. No actual accepting sample is asserted. -/
theorem p4Q2PZ37AHE_originalPositiveCheck_sound
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hCheck : p4Q2PZ37AHE_originalPositiveCheck H d B b m n hn = true) :
    0 < t B := by
  have hMass := p4Q2PZ37AHE_originalTable_massOrdered H d B b m n hn
  have hLower : 0 < (p4Q2PZ37AGP_originalTable H d B b m n hn).lower :=
    (p4Q2PZ37AHE_positiveCheck_iff _ hMass).mp hCheck
  have hReal : (0 : ℝ) <
      ((p4Q2PZ37AGP_originalTable H d B b m n hn).lower : ℝ) := by
    exact_mod_cast hLower
  exact hReal.trans_le (p4Q2PZ37AGP_originalTransfer_bounds H d B b m n hn).1

theorem p4Q2PZ37AHE_originalNegativeCheck_sound
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hCheck : p4Q2PZ37AHE_originalNegativeCheck H d B b m n hn = true) :
    t B < 0 := by
  have hMass := p4Q2PZ37AHE_originalTable_massOrdered H d B b m n hn
  have hUpper : (p4Q2PZ37AGP_originalTable H d B b m n hn).upper < 0 :=
    (p4Q2PZ37AHE_negativeCheck_iff _ hMass).mp hCheck
  have hReal : ((p4Q2PZ37AGP_originalTable H d B b m n hn).upper : ℝ) < 0 := by
    exact_mod_cast hUpper
  exact (p4Q2PZ37AGP_originalTransfer_bounds H d B b m n hn).2.trans_lt hReal

/-- The concrete original AFQ/AGD 24-center grid and its certified
genuine product-Haar mass endpoints, not synthetic one-cell test data. -/
def p4Q2PZ37AHE_original24PositiveCheck
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : Bool :=
  p4Q2PZ37AHE_originalPositiveCheck H
    (p4Q2PZ37AGP_original24Data H) B b m n hn

def p4Q2PZ37AHE_original24NegativeCheck
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : Bool :=
  p4Q2PZ37AHE_originalNegativeCheck H
    (p4Q2PZ37AGP_original24Data H) B b m n hn

theorem p4Q2PZ37AHE_original24Positive_sound
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hCheck : p4Q2PZ37AHE_original24PositiveCheck H B b m n hn = true) :
    0 < t B :=
  p4Q2PZ37AHE_originalPositiveCheck_sound H
    (p4Q2PZ37AGP_original24Data H) B b m n hn hCheck

theorem p4Q2PZ37AHE_original24Negative_sound
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (hCheck : p4Q2PZ37AHE_original24NegativeCheck H B b m n hn = true) :
    t B < 0 :=
  p4Q2PZ37AHE_originalNegativeCheck_sound H
    (p4Q2PZ37AGP_original24Data H) B b m n hn hCheck

/-- A strictly signed rational checker on AGU's SAME genuine,
precision-indexed Haar table (chosen noncomputably but proof-carrying). -/
def p4Q2PZ37AHE_finePositiveCertificate
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) : Prop :=
  ∃ R eps : ℚ, ∃ hR : 0 < R, ∃ heps : 0 < eps,
    ∃ m n : ℕ, ∃ hn : 0 < n,
      p4Q2PZ37AHE_originalPositiveCheck H
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
        B b m n hn = true

def p4Q2PZ37AHE_fineNegativeCertificate
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) : Prop :=
  ∃ R eps : ℚ, ∃ hR : 0 < R, ∃ heps : 0 < eps,
    ∃ m n : ℕ, ∃ hn : 0 < n,
      p4Q2PZ37AHE_originalNegativeCheck H
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
        B b m n hn = true

/-- Complete conditional equivalence: a genuine AHE positive checker
accepts for SOME finite AGU table exactly if the true fixed-H transfer
is positive. The theorem constructs no unconditional physical witness. -/
theorem p4Q2PZ37AHE_finePositive_iff
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    p4Q2PZ37AHE_finePositiveCertificate H B b ↔ 0 < t B := by
  have hEquiv :
      p4Q2PZ37AHE_finePositiveCertificate H B b ↔
        p4Q2PZ37AHD_rawHaarPositiveCertificate H B b := by
    constructor
    · rintro ⟨R, eps, hR, heps, m, n, hn, hCheck⟩
      let d := (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
      have hMass := p4Q2PZ37AHE_originalTable_massOrdered H d B b m n hn
      change p4Q2PZ37AHE_positiveCheck
        (p4Q2PZ37AGP_originalTable H d B b m n hn) = true at hCheck
      exact ⟨R, eps, hR, heps, m, n, hn,
        (p4Q2PZ37AHE_positiveCheck_iff _ hMass).mp hCheck⟩
    · rintro ⟨R, eps, hR, heps, m, n, hn, hRaw⟩
      let d := (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
      have hMass := p4Q2PZ37AHE_originalTable_massOrdered H d B b m n hn
      refine ⟨R, eps, hR, heps, m, n, hn, ?_⟩
      change p4Q2PZ37AHE_positiveCheck
        (p4Q2PZ37AGP_originalTable H d B b m n hn) = true
      exact (p4Q2PZ37AHE_positiveCheck_iff _ hMass).mpr hRaw
  exact hEquiv.trans (p4Q2PZ37AHD_rawHaarPositive_iff H B b)

theorem p4Q2PZ37AHE_fineNegative_iff
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    p4Q2PZ37AHE_fineNegativeCertificate H B b ↔ t B < 0 := by
  have hEquiv :
      p4Q2PZ37AHE_fineNegativeCertificate H B b ↔
        p4Q2PZ37AHD_rawHaarNegativeCertificate H B b := by
    constructor
    · rintro ⟨R, eps, hR, heps, m, n, hn, hCheck⟩
      let d := (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
      have hMass := p4Q2PZ37AHE_originalTable_massOrdered H d B b m n hn
      change p4Q2PZ37AHE_negativeCheck
        (p4Q2PZ37AGP_originalTable H d B b m n hn) = true at hCheck
      exact ⟨R, eps, hR, heps, m, n, hn,
        (p4Q2PZ37AHE_negativeCheck_iff _ hMass).mp hCheck⟩
    · rintro ⟨R, eps, hR, heps, m, n, hn, hRaw⟩
      let d := (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
      have hMass := p4Q2PZ37AHE_originalTable_massOrdered H d B b m n hn
      refine ⟨R, eps, hR, heps, m, n, hn, ?_⟩
      change p4Q2PZ37AHE_negativeCheck
        (p4Q2PZ37AGP_originalTable H d B b m n hn) = true
      exact (p4Q2PZ37AHE_negativeCheck_iff _ hMass).mpr hRaw
  exact hEquiv.trans (p4Q2PZ37AHD_rawHaarNegative_iff H B b)

theorem p4Q2PZ37AHE_fineSign_iff_nonzero
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    (p4Q2PZ37AHE_finePositiveCertificate H B b ∨
      p4Q2PZ37AHE_fineNegativeCertificate H B b) ↔ t B ≠ 0 := by
  rw [p4Q2PZ37AHE_finePositive_iff H B b,
    p4Q2PZ37AHE_fineNegative_iff H B b]
  constructor
  · rintro (hp | hn)
    · exact ne_of_gt hp
    · exact ne_of_lt hn
  · intro hNonzero
    rcases lt_trichotomy (t B) 0 with hn | hz | hp
    · exact Or.inr hn
    · exact (hNonzero hz).elim
    · exact Or.inl hp

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHE_minProduct_midpoint
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHE_maxProduct_midpoint
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHE_tableLower_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHE_tableUpper_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHE_lowerError_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHE_upperError_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHE_positiveCheck_iff
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHE_negativeCheck_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHE_originalTable_massOrdered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHE_originalPositiveCheck_sound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHE_originalNegativeCheck_sound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHE_original24Positive_sound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHE_original24Negative_sound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHE_finePositive_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHE_fineNegative_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHE_fineSign_iff_nonzero
