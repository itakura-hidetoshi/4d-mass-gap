import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSignedHaarWidthV5_PZ37AGV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGW — original center signed interval-width factorization

AGV proves the final original signed-transfer width conditional on a
uniform bound eta for all true AGN center intervals. This append-only
leaf exposes the exact algebraic origin of that center interval width:
the original rational centered source multiplies the sum of the genuine
original clipped-kernel width and half the genuine original floor width.

No alternate source, new kernel, nonphysical cell, or invented precision
convergence theorem. The next step must prove refined original kernel
and floor widths uniformly small, not simply assume that AGK alone does.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Exact signed width of a monotone interval multiplied by an arbitrary
rational source s. The min/max are essential for negative s. -/
theorem p4Q2PZ37AGW_signedInterval_width_exact
    (s lo hi : ℚ) (h : lo ≤ hi) :
    max (s * lo) (s * hi) - min (s * lo) (s * hi) =
      |s| * (hi - lo) := by
  by_cases hs : 0 ≤ s
  · have hmul : s * lo ≤ s * hi := mul_le_mul_of_nonneg_left h hs
    rw [max_eq_right hmul, min_eq_left hmul, abs_of_nonneg hs]
    ring
  · have hs' : s ≤ 0 := le_of_lt (lt_of_not_ge hs)
    have hmul : s * hi ≤ s * lo := mul_le_mul_of_nonpos_left h hs'
    rw [max_eq_left hmul, min_eq_right hmul, abs_of_nonpos hs']
    ring

/-- An original centered product kernel minus the original floor's
midpoint has exactly the signed-width sum, including when s < 0. -/
theorem p4Q2PZ37AGW_centerProduct_width_exact
    (s kerLo kerHi floorLo floorHi : ℚ)
    (hk : kerLo ≤ kerHi) (hf : floorLo ≤ floorHi) :
    max (s * (kerLo - (1 + floorHi) / 2))
        (s * (kerHi - (1 + floorLo) / 2)) -
      min (s * (kerLo - (1 + floorHi) / 2))
        (s * (kerHi - (1 + floorLo) / 2)) =
      |s| * ((kerHi - kerLo) + (floorHi - floorLo) / 2) := by
  have hLoHi : kerLo - (1 + floorHi) / 2 ≤
      kerHi - (1 + floorLo) / 2 := by
    linarith only [hk, hf]
  calc
    max (s * (kerLo - (1 + floorHi) / 2))
        (s * (kerHi - (1 + floorLo) / 2)) -
        min (s * (kerLo - (1 + floorHi) / 2))
          (s * (kerHi - (1 + floorLo) / 2)) =
        |s| * ((kerHi - (1 + floorLo) / 2) -
          (kerLo - (1 + floorHi) / 2)) :=
      p4Q2PZ37AGW_signedInterval_width_exact s _ _ hLoHi
    _ = |s| * ((kerHi - kerLo) + (floorHi - floorLo) / 2) := by ring

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AGW_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AGW_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AGW_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AGW_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AGW_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2

local instance p4Q2PZ37AGW_links : Fintype Link := Fintype.ofFinite _

/-- An explicit exact rational error budget based solely on the original
AGN kernel and floor interval fields and the true rational center source. -/
def p4Q2PZ37AGW_centerWidthFormula
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : ℚ :=
  let s := p4Q2PZ37AGN_centeredSourceRational H A a
  let ker := p4Q2PZ37AGM_originalClippedKernelInterval H A B a b m n hn
  let fl := p4Q2PZ37AGN_originalFloorInterval H m n hn
  |s| * ((ker.upper - ker.lower) + (fl.upper - fl.lower) / 2)

/-- Unlike a generic assumed eta, this equality follows from the
literal original AGN center interval, including its signed min/max.
No precision convergence claim is contained in this equality. -/
theorem p4Q2PZ37AGW_originalCenterWidth_exact
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGN_originalIntegrandInterval H A B a b m n hn).upper -
      (p4Q2PZ37AGN_originalIntegrandInterval H A B a b m n hn).lower =
        p4Q2PZ37AGW_centerWidthFormula H A B a b m n hn := by
  let s := p4Q2PZ37AGN_centeredSourceRational H A a
  let ker := p4Q2PZ37AGM_originalClippedKernelInterval H A B a b m n hn
  let fl := p4Q2PZ37AGN_originalFloorInterval H m n hn
  have hkReal : (ker.lower : ℝ) ≤ (ker.upper : ℝ) :=
    ker.hLower.trans ker.hUpper
  have hfReal : (fl.lower : ℝ) ≤ (fl.upper : ℝ) :=
    fl.hLower.trans fl.hUpper
  have hk : ker.lower ≤ ker.upper := by exact_mod_cast hkReal
  have hf : fl.lower ≤ fl.upper := by exact_mod_cast hfReal
  have h := p4Q2PZ37AGW_centerProduct_width_exact
    s ker.lower ker.upper fl.lower fl.upper hk hf
  change max (s * (ker.lower - (1 + fl.upper) / 2))
      (s * (ker.upper - (1 + fl.lower) / 2)) -
    min (s * (ker.lower - (1 + fl.upper) / 2))
      (s * (ker.upper - (1 + fl.lower) / 2)) =
    |s| * ((ker.upper - ker.lower) + (fl.upper - fl.lower) / 2)
  exact h

/-- Every actual original center interval has nonnegative rational width.
This follows from the original interval's true real-value enclosure. -/
theorem p4Q2PZ37AGW_originalCenterWidth_nonneg
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ (p4Q2PZ37AGN_originalIntegrandInterval H A B a b m n hn).upper -
      (p4Q2PZ37AGN_originalIntegrandInterval H A B a b m n hn).lower := by
  let iv := p4Q2PZ37AGN_originalIntegrandInterval H A B a b m n hn
  have hReal : (iv.lower : ℝ) ≤ (iv.upper : ℝ) :=
    iv.hLower.trans iv.hUpper
  have hRat : iv.lower ≤ iv.upper := by exact_mod_cast hReal
  exact sub_nonneg.mpr hRat

end GroundStatePosteriorJoint

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGW_signedInterval_width_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGW_centerProduct_width_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGW_originalCenterWidth_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGW_originalCenterWidth_nonneg
