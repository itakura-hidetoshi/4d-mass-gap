import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSignedTransferArbitraryWidthV5_PZ37AHC
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHD — complete conditional sign certificates for ORIGINAL signed transfer

AHC proves that at each fixed finite H, for EVERY original rational-coordinate
right boundary B, the genuine original signed-transfer value t(B) lies in
verified rational intervals of arbitrarily small width. This does NOT say
that t(B) is different from zero.

AHD shows the exact logical boundary, with no replacement physical source,
kernel, floor, probability, Haar grid, or transfer:
 * t(B)>0 iff SOME AHC-compatible ORIGINAL AGU interval has lower>0;
 * t(B)<0 iff SOME such interval has upper<0;
 * t(B)!=0 iff one of these strictly separated signs is certified;
 * t(B)=0 iff EVERY original interval straddles zero.

In the ACTUAL original AGP signed Haar quadrature, the final AGU interval is
the intersection of its raw rational table and the independently verified
symmetric AGN global range [-M,M], with M>=0. Therefore a strict positive
(or negative) AGU endpoint exists iff the SAME true-Haar signed AGP table
itself has a strictly positive lower (or strictly negative upper) endpoint.
This isolates the remaining physical obstruction to a genuine finite
rational-table sign witness, rather than hiding it inside precision.

All completeness arguments use the proved AHC arbitrary-width theorem and
rational density; they do NOT compute a classical AGU grid or establish
that either strict signed witness exists for an actual physical boundary.
No original nonzero transfer, two-sign shell, H-uniform coercivity,
Hamiltonian or continuum Yang--Mills mass gap follows unconditionally.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A verified rational interval with width smaller than a rational
positive margin below its actual positive real value has positive lower
endpoint. No numerical guess for the real value is inserted. -/
theorem p4Q2PZ37AHD_interval_lower_pos_of_width_lt
    {x : ℝ} (iv : p4Q2PZ37AFV_verifiedInterval x)
    (eta : ℚ) (hWidth : iv.upper - iv.lower < eta)
    (hMargin : (eta : ℝ) < x) :
    0 < iv.lower := by
  have hWidthR :
      (((iv.upper - iv.lower : ℚ) : ℝ)) < (eta : ℝ) :=
    (Rat.cast_lt (K := ℝ)).2 hWidth
  have hCast : (iv.upper : ℝ) - (iv.lower : ℝ) < (eta : ℝ) := by
    simpa only [Rat.cast_sub] using hWidthR
  have hPos : (0 : ℝ) < (iv.lower : ℝ) := by
    linarith only [hCast, iv.hUpper, hMargin]
  exact_mod_cast hPos

/-- The negative analogue uses the actual lower inclusion and a strict
margin above the true negative value, never an external sign oracle. -/
theorem p4Q2PZ37AHD_interval_upper_neg_of_width_lt
    {x : ℝ} (iv : p4Q2PZ37AFV_verifiedInterval x)
    (eta : ℚ) (hWidth : iv.upper - iv.lower < eta)
    (hMargin : x < -(eta : ℝ)) :
    iv.upper < 0 := by
  have hWidthR :
      (((iv.upper - iv.lower : ℚ) : ℝ)) < (eta : ℝ) :=
    (Rat.cast_lt (K := ℝ)).2 hWidth
  have hCast : (iv.upper : ℝ) - (iv.lower : ℝ) < (eta : ℝ) := by
    simpa only [Rat.cast_sub] using hWidthR
  have hNeg : (iv.upper : ℝ) < 0 := by
    linarith only [hCast, iv.hLower, hMargin]
  exact_mod_cast hNeg

/-- Every sound interval for the real number zero must straddle zero,
regardless of how small its width becomes. -/
theorem p4Q2PZ37AHD_zero_interval_straddles
    (iv : p4Q2PZ37AFV_verifiedInterval (0 : ℝ)) :
    iv.lower ≤ 0 ∧ 0 ≤ iv.upper := by
  have hlo : (iv.lower : ℝ) ≤ 0 := iv.hLower
  have hhi : (0 : ℝ) ≤ (iv.upper : ℝ) := iv.hUpper
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- A degenerate zero-width original-style verified interval is an
algebraic counterexample to the invalid inference width->nonzero. -/
theorem p4Q2PZ37AHD_zero_width_obstruction
    (eta : ℚ) (heta : 0 < eta) :
    ∃ iv : p4Q2PZ37AFV_verifiedInterval (0 : ℝ),
      iv.upper - iv.lower < eta ∧
      iv.lower ≤ 0 ∧ 0 ≤ iv.upper := by
  let iv : p4Q2PZ37AFV_verifiedInterval (0 : ℝ) :=
    ⟨0, 0, by norm_num, by norm_num⟩
  refine ⟨iv, ?_, ?_⟩
  · simpa [iv] using heta
  · exact p4Q2PZ37AHD_zero_interval_straddles iv

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "t" => decomposableOneSliceTransferIntegral H 2
  p4Q2PZ37ADC_fixedCoupling (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)

local instance p4Q2PZ37AHD_links : Fintype Link := Fintype.ofFinite _

/-- A positive SIGN certificate of the EXACT original physical transfer,
using only an original AGU selected Borel/Haar grid and finite rational
AGI/AGP/AGN endpoints. This is a Prop, not an evaluated numerical table. -/
def p4Q2PZ37AHD_finePositiveCertificate
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) : Prop :=
  ∃ R eps : ℚ, ∃ hR : 0 < R, ∃ heps : 0 < eps,
    ∃ m n : ℕ, ∃ hn : 0 < n,
      0 < (p4Q2PZ37AGU_fineOriginalTransferInterval H
        R eps hR heps B b m n hn).lower

/-- The dual strict negative certification predicate. -/
def p4Q2PZ37AHD_fineNegativeCertificate
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) : Prop :=
  ∃ R eps : ℚ, ∃ hR : 0 < R, ∃ heps : 0 < eps,
    ∃ m n : ℕ, ∃ hn : 0 < n,
      (p4Q2PZ37AGU_fineOriginalTransferInterval H
        R eps hR heps B b m n hn).upper < 0

/-- A nonzero genuine positive transfer is EVENTUALLY certified by
AHC's arbitrarily narrow exact original intervals. Conversely any
positive rational lower endpoint soundly certifies the original value.
No positive physical witness is assumed or asserted to exist. -/
theorem p4Q2PZ37AHD_finePositive_iff
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    p4Q2PZ37AHD_finePositiveCertificate H B b ↔ 0 < t B := by
  constructor
  · rintro ⟨R, eps, hR, heps, m, n, hn, hLower⟩
    exact p4Q2PZ37AFV_interval_positive
      (p4Q2PZ37AGU_fineOriginalTransferInterval H
        R eps hR heps B b m n hn) hLower
  · intro hPositive
    obtain ⟨eta, hEtaReal, hMargin⟩ := exists_rat_btwn hPositive
    have heta : (0 : ℚ) < eta := by exact_mod_cast hEtaReal
    obtain ⟨R, eps, hR, heps, m, n, hn, hWidth⟩ :=
      p4Q2PZ37AHC_exists_fineOriginalTransfer_precision H eta heta
    refine ⟨R, eps, hR, heps, m, n, hn, ?_⟩
    exact p4Q2PZ37AHD_interval_lower_pos_of_width_lt
      (p4Q2PZ37AGU_fineOriginalTransferInterval H
        R eps hR heps B b m n hn)
      eta (hWidth B b) hMargin

/-- The same completeness theorem for genuinely negative transfer.
Negative sign is only conditional on an actual negative physical value. -/
theorem p4Q2PZ37AHD_fineNegative_iff
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    p4Q2PZ37AHD_fineNegativeCertificate H B b ↔ t B < 0 := by
  constructor
  · rintro ⟨R, eps, hR, heps, m, n, hn, hUpper⟩
    exact p4Q2PZ37AFV_interval_negative
      (p4Q2PZ37AGU_fineOriginalTransferInterval H
        R eps hR heps B b m n hn) hUpper
  · intro hNegative
    have hPositiveNeg : (0 : ℝ) < -(t B) := by
      linarith only [hNegative]
    obtain ⟨eta, hEtaReal, hMargin⟩ := exists_rat_btwn hPositiveNeg
    have heta : (0 : ℚ) < eta := by exact_mod_cast hEtaReal
    have hNegativeMargin : t B < -(eta : ℝ) := by
      linarith only [hMargin]
    obtain ⟨R, eps, hR, heps, m, n, hn, hWidth⟩ :=
      p4Q2PZ37AHC_exists_fineOriginalTransfer_precision H eta heta
    refine ⟨R, eps, hR, heps, m, n, hn, ?_⟩
    exact p4Q2PZ37AHD_interval_upper_neg_of_width_lt
      (p4Q2PZ37AGU_fineOriginalTransferInterval H
        R eps hR heps B b m n hn)
      eta (hWidth B b) hNegativeMargin

/-- EXACT conditional logical completeness at fixed H. Merely making
intervals narrow does not prove that either disjunct holds. -/
theorem p4Q2PZ37AHD_fineSign_iff_nonzero
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    (p4Q2PZ37AHD_finePositiveCertificate H B b ∨
      p4Q2PZ37AHD_fineNegativeCertificate H B b) ↔ t B ≠ 0 := by
  constructor
  · rintro (hp | hn)
    · exact ne_of_gt ((p4Q2PZ37AHD_finePositive_iff H B b).mp hp)
    · exact ne_of_lt ((p4Q2PZ37AHD_fineNegative_iff H B b).mp hn)
  · intro hNonzero
    rcases lt_trichotomy (t B) 0 with hn | hz | hp
    · exact Or.inr ((p4Q2PZ37AHD_fineNegative_iff H B b).mpr hn)
    · exact (hNonzero hz).elim
    · exact Or.inl ((p4Q2PZ37AHD_finePositive_iff H B b).mpr hp)

/-- A genuine zero transfer forces ALL original AGU certified intervals
to straddle zero, at ANY precision. Conversely a nonzero transfer has
a strict sign-separating interval by AHC, so universal straddling is a
precise necessary and sufficient obstruction. -/
theorem p4Q2PZ37AHD_zero_iff_all_fine_intervals_straddle
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    t B = 0 ↔
      ∀ R eps : ℚ, ∀ (hR : 0 < R) (heps : 0 < eps)
        (m n : ℕ) (hn : 0 < n),
        (p4Q2PZ37AGU_fineOriginalTransferInterval H
          R eps hR heps B b m n hn).lower ≤ 0 ∧
        0 ≤ (p4Q2PZ37AGU_fineOriginalTransferInterval H
          R eps hR heps B b m n hn).upper := by
  constructor
  · intro hzero R eps hR heps m n hn
    let iv := p4Q2PZ37AGU_fineOriginalTransferInterval H
      R eps hR heps B b m n hn
    have hLo : (iv.lower : ℝ) ≤ 0 := by
      simpa only [hzero] using iv.hLower
    have hHi : (0 : ℝ) ≤ (iv.upper : ℝ) := by
      simpa only [hzero] using iv.hUpper
    exact ⟨by exact_mod_cast hLo, by exact_mod_cast hHi⟩
  · intro hAll
    by_contra hNonzero
    have hCert := (p4Q2PZ37AHD_fineSign_iff_nonzero H B b).mpr hNonzero
    rcases hCert with ⟨R, eps, hR, heps, m, n, hn, hp⟩ |
      ⟨R, eps, hR, heps, m, n, hn, hn⟩
    · exact (not_lt_of_ge (hAll R eps hR heps m n hn).1) hp
    · exact (not_lt_of_ge (hAll R eps hR heps m n hn).2) hn

/-- The original signed AGP/Haar table, NOT the AGN symmetric global
clipping range, must provide the strict positive lower endpoint. The
global interval's lower endpoint is -M<=0 for genuine M>=0. -/
theorem p4Q2PZ37AHD_fineLower_positive_iff_rawHaarTable
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    0 < (p4Q2PZ37AGU_fineOriginalTransferInterval H
      R eps hR heps B b m n hn).lower ↔
    0 < (p4Q2PZ37AGP_originalTable H
      (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
      B b m n hn).lower := by
  let tbl := p4Q2PZ37AGP_originalTable H
    (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
    B b m n hn
  let M := p4Q2PZ37AGN_transferRadius H m n hn
  have hM : 0 ≤ M := p4Q2PZ37AGV_transferRadius_nonneg H m n hn
  change (0 : ℚ) < max tbl.lower (-M) ↔ 0 < tbl.lower
  constructor
  · intro h
    by_contra hf
    have hRaw : tbl.lower ≤ 0 := le_of_not_gt hf
    have hGlobal : -M ≤ 0 := neg_nonpos.mpr hM
    have hMax : max tbl.lower (-M) ≤ 0 := max_le hRaw hGlobal
    exact (not_lt_of_ge hMax) h
  · intro h
    exact h.trans_le (le_max_left _ _)

/-- The dual raw-Haar-table criterion for a negative original transfer;
the AGN global upper endpoint M>=0 cannot create a negative sign. -/
theorem p4Q2PZ37AHD_fineUpper_negative_iff_rawHaarTable
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGU_fineOriginalTransferInterval H
      R eps hR heps B b m n hn).upper < 0 ↔
    (p4Q2PZ37AGP_originalTable H
      (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
      B b m n hn).upper < 0 := by
  let tbl := p4Q2PZ37AGP_originalTable H
    (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
    B b m n hn
  let M := p4Q2PZ37AGN_transferRadius H m n hn
  have hM : 0 ≤ M := p4Q2PZ37AGV_transferRadius_nonneg H m n hn
  change min tbl.upper M < (0 : ℚ) ↔ tbl.upper < 0
  constructor
  · intro h
    by_contra hf
    have hRaw : 0 ≤ tbl.upper := le_of_not_gt hf
    have hMin : 0 ≤ min tbl.upper M := le_min hRaw hM
    exact (not_lt_of_ge hMin) h
  · intro h
    exact (min_le_left _ _).trans_lt h

/-- A genuinely signed FINITE rational AGP table is the complete
conditional positive certificate. Its original Haar cells and centers
may still be classically selected rather than numerically evaluated. -/
def p4Q2PZ37AHD_rawHaarPositiveCertificate
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) : Prop :=
  ∃ R eps : ℚ, ∃ hR : 0 < R, ∃ heps : 0 < eps,
    ∃ m n : ℕ, ∃ hn : 0 < n,
      0 < (p4Q2PZ37AGP_originalTable H
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
        B b m n hn).lower

def p4Q2PZ37AHD_rawHaarNegativeCertificate
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) : Prop :=
  ∃ R eps : ℚ, ∃ hR : 0 < R, ∃ heps : 0 < eps,
    ∃ m n : ℕ, ∃ hn : 0 < n,
      (p4Q2PZ37AGP_originalTable H
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps).data
        B b m n hn).upper < 0

/-- Precise POSITIVE obstruction: a physical strict sign exists iff
some actual AGP signed-Haar rational table has a positive lower bound.
This does not supply such a table. -/
theorem p4Q2PZ37AHD_rawHaarPositive_iff
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    p4Q2PZ37AHD_rawHaarPositiveCertificate H B b ↔ 0 < t B := by
  calc
    p4Q2PZ37AHD_rawHaarPositiveCertificate H B b ↔
        p4Q2PZ37AHD_finePositiveCertificate H B b := by
      constructor
      · rintro ⟨R, eps, hR, heps, m, n, hn, hRaw⟩
        exact ⟨R, eps, hR, heps, m, n, hn,
          (p4Q2PZ37AHD_fineLower_positive_iff_rawHaarTable H
            R eps hR heps B b m n hn).mpr hRaw⟩
      · rintro ⟨R, eps, hR, heps, m, n, hn, hFine⟩
        exact ⟨R, eps, hR, heps, m, n, hn,
          (p4Q2PZ37AHD_fineLower_positive_iff_rawHaarTable H
            R eps hR heps B b m n hn).mp hFine⟩
    _ ↔ 0 < t B := p4Q2PZ37AHD_finePositive_iff H B b

theorem p4Q2PZ37AHD_rawHaarNegative_iff
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    p4Q2PZ37AHD_rawHaarNegativeCertificate H B b ↔ t B < 0 := by
  calc
    p4Q2PZ37AHD_rawHaarNegativeCertificate H B b ↔
        p4Q2PZ37AHD_fineNegativeCertificate H B b := by
      constructor
      · rintro ⟨R, eps, hR, heps, m, n, hn, hRaw⟩
        exact ⟨R, eps, hR, heps, m, n, hn,
          (p4Q2PZ37AHD_fineUpper_negative_iff_rawHaarTable H
            R eps hR heps B b m n hn).mpr hRaw⟩
      · rintro ⟨R, eps, hR, heps, m, n, hn, hFine⟩
        exact ⟨R, eps, hR, heps, m, n, hn,
          (p4Q2PZ37AHD_fineUpper_negative_iff_rawHaarTable H
            R eps hR heps B b m n hn).mp hFine⟩
    _ ↔ t B < 0 := p4Q2PZ37AHD_fineNegative_iff H B b

/-- The exact remaining nonzero obstruction is a strict original
signed-Haar table witness; both signs retain their own presentations. -/
theorem p4Q2PZ37AHD_rawHaarSign_iff_nonzero
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    (p4Q2PZ37AHD_rawHaarPositiveCertificate H B b ∨
      p4Q2PZ37AHD_rawHaarNegativeCertificate H B b) ↔
        t B ≠ 0 := by
  rw [p4Q2PZ37AHD_rawHaarPositive_iff H B b,
    p4Q2PZ37AHD_rawHaarNegative_iff H B b]
  constructor
  · rintro (hp | hn)
    · exact ne_of_gt hp
    · exact ne_of_lt hn
  · intro hNonzero
    rcases lt_trichotomy (t B) 0 with hn | hz | hp
    · exact Or.inr hn
    · exact (hNonzero hz).elim
    · exact Or.inl hp

/-- The mathematically exact zero obstruction. Arbitrary numerical
precision alone cannot prove a nonzero original transfer value. -/
theorem p4Q2PZ37AHD_zero_iff_no_rawHaar_sign
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    t B = 0 ↔
      ¬ p4Q2PZ37AHD_rawHaarPositiveCertificate H B b ∧
      ¬ p4Q2PZ37AHD_rawHaarNegativeCertificate H B b := by
  constructor
  · intro hz
    constructor
    · intro hp
      exact (ne_of_gt ((p4Q2PZ37AHD_rawHaarPositive_iff H B b).mp hp)) hz
    · intro hn
      exact (ne_of_lt ((p4Q2PZ37AHD_rawHaarNegative_iff H B b).mp hn)) hz
  · rintro ⟨hNotPositive, hNotNegative⟩
    by_contra hNonzero
    have hSign :=
      (p4Q2PZ37AHD_rawHaarSign_iff_nonzero H B b).mpr hNonzero
    exact hSign.elim hNotPositive hNotNegative

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHD_interval_lower_pos_of_width_lt
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHD_interval_upper_neg_of_width_lt
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHD_zero_interval_straddles
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHD_zero_width_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_finePositive_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_fineNegative_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_fineSign_iff_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_zero_iff_all_fine_intervals_straddle
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_fineLower_positive_iff_rawHaarTable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_fineUpper_negative_iff_rawHaarTable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_rawHaarPositive_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_rawHaarNegative_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_rawHaarSign_iff_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHD_zero_iff_no_rawHaar_sign
