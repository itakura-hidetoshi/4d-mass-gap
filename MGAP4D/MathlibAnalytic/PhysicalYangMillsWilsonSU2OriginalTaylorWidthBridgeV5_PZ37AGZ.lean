import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalKernelFloorMaxWidthV5_PZ37AGY
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGZ — original coupling/Taylor precision descent to kernel and floor

AGY isolated TWO exact physical widths: the same-grid maximum of genuine
clipped Wilson kernel intervals and the original global minorization-floor
interval. Here the original AGM/AGN definitions are connected to their
AGK rational coupling brackets and AGJ rational scaled-Taylor endpoints.

The genuine original one-slab action is an exact AGL rational singleton,
not an assumed action-value oracle. The original floor action is the exact
AGN combinatorial budget. The difference of their rational exponential
arguments is exactly action * (AGK_upper m - AGK_lower m), hence bounded
by action * AGK_tail m. This is a genuine, unconditional geometric
coupling-precision rate, independent of Taylor order.

The actual original clipped kernel and floor widths are no larger than the
raw AGJ/AGK verified intervals, without replacing either physical value
or weakening its existing interval. Finite maxima on the SAME AGU grid
then give an explicit raw-Taylor width certificate for the final signed
transfer.

Important boundary: the independent Taylor truncation gap and the action
size are still present. No uniform vanishing of the full raw Taylor gap,
computed large-volume Haar table, original nonzero transfer sign,
H-uniform coercivity, Hamiltonian gap or continuum mass gap is asserted.
The original source/measure/kernel, all existing files, root and pins are
unchanged. No axioms or sorry are introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The actual negative exponent arguments of AGK's coupling bracket
for a NONNEGATIVE original rational action. -/
def p4Q2PZ37AGZ_exponentLower (action : ℚ) (m : ℕ) : ℚ :=
  -(p4Q2PZ37AGK_upper m * action)

def p4Q2PZ37AGZ_exponentUpper (action : ℚ) (m : ℕ) : ℚ :=
  -(p4Q2PZ37AGK_lower m * action)

/-- The very same automatic positive integer scale chosen by AGM. -/
def p4Q2PZ37AGZ_autoScale (action : ℚ) (m : ℕ) : ℕ :=
  p4Q2PZ37AGM_autoScale
    (p4Q2PZ37AGZ_exponentLower action m)
    (p4Q2PZ37AGZ_exponentUpper action m)

namespace GroundStatePosteriorJoint

/-- Exact input-width identity and the unconditional AGK geometric rate.
This does NOT confuse exponent-input precision with exp-output accuracy. -/
theorem p4Q2PZ37AGZ_exponentSpan_le_couplingTail
    (action : ℚ) (ha : 0 ≤ action) (m : ℕ) :
    0 ≤ p4Q2PZ37AGZ_exponentUpper action m -
      p4Q2PZ37AGZ_exponentLower action m ∧
    p4Q2PZ37AGZ_exponentUpper action m -
      p4Q2PZ37AGZ_exponentLower action m ≤
      action * p4Q2PZ37AGK_tail m := by
  have hw := p4Q2PZ37AGK_originalCoupling_width m
  have hEq : p4Q2PZ37AGZ_exponentUpper action m -
      p4Q2PZ37AGZ_exponentLower action m =
      action * (p4Q2PZ37AGK_upper m - p4Q2PZ37AGK_lower m) := by
    unfold p4Q2PZ37AGZ_exponentLower p4Q2PZ37AGZ_exponentUpper
    ring
  rw [hEq]
  exact ⟨mul_nonneg ha hw.1, mul_le_mul_of_nonneg_left hw.2 ha⟩

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2

local instance p4Q2PZ37AGZ_links : Fintype Link := Fintype.ofFinite _

/-- The input exponent width for each actual original AGL action obeys
AGK's explicit geometric coupling bound, without an action oracle. -/
theorem p4Q2PZ37AGZ_originalKernelExponentSpan_le
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m : ℕ) :
    0 ≤
      p4Q2PZ37AGZ_exponentUpper (p4Q2PZ37AGL_slabActionRational H A B a b) m -
        p4Q2PZ37AGZ_exponentLower (p4Q2PZ37AGL_slabActionRational H A B a b) m ∧
    p4Q2PZ37AGZ_exponentUpper (p4Q2PZ37AGL_slabActionRational H A B a b) m -
        p4Q2PZ37AGZ_exponentLower (p4Q2PZ37AGL_slabActionRational H A B a b) m ≤
      p4Q2PZ37AGL_slabActionRational H A B a b * p4Q2PZ37AGK_tail m :=
  p4Q2PZ37AGZ_exponentSpan_le_couplingTail
    (p4Q2PZ37AGL_slabActionRational H A B a b)
    (p4Q2PZ37AGM_originalActionRational_nonneg H A B a b) m

/-- The ORIGINAL global floor has a literal, exact rational action
budget; it is not inferred from an arbitrary finite grid or sample. -/
def p4Q2PZ37AGZ_originalFloorAction : ℚ :=
  (p4Q2PZ37AGN_actionBudgetInterval H).lower

theorem p4Q2PZ37AGZ_originalFloorAction_nonneg :
    0 ≤ p4Q2PZ37AGZ_originalFloorAction H := by
  unfold p4Q2PZ37AGZ_originalFloorAction
  change (0 : ℚ) ≤
    2 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H : ℚ)
  positivity

/-- Unconditional geometric input-width control also holds for the
genuine original global floor, with its exact combinatorial action. -/
theorem p4Q2PZ37AGZ_originalFloorExponentSpan_le (m : ℕ) :
    0 ≤ p4Q2PZ37AGZ_exponentUpper
      (p4Q2PZ37AGZ_originalFloorAction H) m -
      p4Q2PZ37AGZ_exponentLower (p4Q2PZ37AGZ_originalFloorAction H) m ∧
    p4Q2PZ37AGZ_exponentUpper (p4Q2PZ37AGZ_originalFloorAction H) m -
      p4Q2PZ37AGZ_exponentLower (p4Q2PZ37AGZ_originalFloorAction H) m ≤
      p4Q2PZ37AGZ_originalFloorAction H * p4Q2PZ37AGK_tail m :=
  p4Q2PZ37AGZ_exponentSpan_le_couplingTail
    (p4Q2PZ37AGZ_originalFloorAction H)
    (p4Q2PZ37AGZ_originalFloorAction_nonneg H) m

/-- Raw AGK/AGJ finite rational Taylor width of the actual original
kernel, BEFORE the already proven [0,1] AGM intersection. -/
def p4Q2PZ37AGZ_originalKernelTaylorGap
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : ℚ :=
  let raw := p4Q2PZ37AGM_originalRationalKernelInterval H A B a b m n hn
  raw.upper - raw.lower

/-- Raw AGK/AGJ Taylor width of the actual original global floor,
BEFORE AGN intersects it with its genuine [0,1] physical range. -/
def p4Q2PZ37AGZ_originalFloorTaylorGap (m n : ℕ) (hn : 0 < n) : ℚ :=
  let raw := p4Q2PZ37AGN_originalFloorRawInterval H m n hn
  raw.upper - raw.lower

/-- Both raw gaps are valid nonnegative intervals of original values;
negative gaps cannot be spuriously accepted as precision certificates. -/
theorem p4Q2PZ37AGZ_originalKernelTaylorGap_nonneg
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AGZ_originalKernelTaylorGap H A B a b m n hn := by
  let raw := p4Q2PZ37AGM_originalRationalKernelInterval H A B a b m n hn
  have hReal : (raw.lower : ℝ) ≤ (raw.upper : ℝ) :=
    raw.hLower.trans raw.hUpper
  have hRat : raw.lower ≤ raw.upper := by exact_mod_cast hReal
  exact sub_nonneg.mpr hRat

theorem p4Q2PZ37AGZ_originalFloorTaylorGap_nonneg
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AGZ_originalFloorTaylorGap H m n hn := by
  let raw := p4Q2PZ37AGN_originalFloorRawInterval H m n hn
  have hReal : (raw.lower : ℝ) ≤ (raw.upper : ℝ) :=
    raw.hLower.trans raw.hUpper
  have hRat : raw.lower ≤ raw.upper := by exact_mod_cast hReal
  exact sub_nonneg.mpr hRat

/-- AGM's original physical intersection can only tighten the raw
AGJ Taylor width. Both intervals enclose the SAME original kernel. -/
theorem p4Q2PZ37AGZ_originalKernelWidth_le_TaylorGap
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGM_originalClippedKernelInterval H A B a b m n hn).upper -
      (p4Q2PZ37AGM_originalClippedKernelInterval H A B a b m n hn).lower ≤
        p4Q2PZ37AGZ_originalKernelTaylorGap H A B a b m n hn := by
  let raw := p4Q2PZ37AGM_originalRationalKernelInterval H A B a b m n hn
  let clip := p4Q2PZ37AGM_originalClippedKernelInterval H A B a b m n hn
  have hlo : raw.lower ≤ clip.lower := by
    change raw.lower ≤ max 0 raw.lower
    exact le_max_right _ _
  have hhi : clip.upper ≤ raw.upper := by
    change min 1 raw.upper ≤ raw.upper
    exact min_le_right _ _
  change clip.upper - clip.lower ≤ raw.upper - raw.lower
  linarith only [hlo, hhi]

/-- AGN's original floor intersection also cannot enlarge the width
of the same raw AGJ/AGK rational exponential enclosure. -/
theorem p4Q2PZ37AGZ_originalFloorWidth_le_TaylorGap
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGY_originalFloorWidth H m n hn ≤
      p4Q2PZ37AGZ_originalFloorTaylorGap H m n hn := by
  let raw := p4Q2PZ37AGN_originalFloorRawInterval H m n hn
  let clip := p4Q2PZ37AGN_originalFloorInterval H m n hn
  have hlo : raw.lower ≤ clip.lower := by
    change raw.lower ≤ max raw.lower 0
    exact le_max_left _ _
  have hhi : clip.upper ≤ raw.upper := by
    change min raw.upper 1 ≤ raw.upper
    exact min_le_left _ _
  change clip.upper - clip.lower ≤ raw.upper - raw.lower
  linarith only [hlo, hhi]

/-- A finite maximum of raw AGJ/AGK Taylor gaps on precisely the
AGU precision grid used by AGY. No new grid or external eta oracle. -/
def p4Q2PZ37AGZ_originalKernelTaylorMax
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) : ℚ :=
  (Finset.univ : Finset (Fin d.data.grid.n)).sup'
    (p4Q2PZ37AGX_univNonempty H d)
    (fun i => p4Q2PZ37AGZ_originalKernelTaylorGap H
      (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn)

/-- Physical clipped kernel maximum ≤ the raw AGJ Taylor maximum on
the SAME true spatial cells, without an extra cell-count factor. -/
theorem p4Q2PZ37AGZ_originalKernelMax_le_TaylorMax
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGY_originalKernelMax H d B b m n hn ≤
      p4Q2PZ37AGZ_originalKernelTaylorMax H d B b m n hn := by
  unfold p4Q2PZ37AGY_originalKernelMax
  apply Finset.sup'_le
  intro i _hi
  have hClip := p4Q2PZ37AGZ_originalKernelWidth_le_TaylorGap H
    (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn
  exact hClip.trans
    (Finset.le_sup'
      (s := (Finset.univ : Finset (Fin d.data.grid.n)))
      (f := fun j => p4Q2PZ37AGZ_originalKernelTaylorGap H
        (d.data.grid.center j) B (d.data.centerCoordinates j) b m n hn)
      (Finset.mem_univ i))

/-- The signed original transfer is now bounded by EXACT raw rational
AGK/AGJ Taylor gaps (coupling order m and Taylor order n), plus the
already certified AGU geometry and genuine Haar-mass budgets. -/
theorem p4Q2PZ37AGZ_fineOriginalTransferWidth_le_Taylor
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).upper -
      (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).lower ≤
      (p4Q2PZ37AGN_countRational H / 2) *
        (p4Q2PZ37AGZ_originalKernelTaylorMax H
          (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps) B b m n hn +
          p4Q2PZ37AGZ_originalFloorTaylorGap H m n hn / 2) +
        2 * p4Q2PZ37AGV_uniformSlope H m * R +
        2 * p4Q2PZ37AGN_transferRadius H m n hn * eps := by
  let d := p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps
  have hOld := p4Q2PZ37AGY_fineOriginalTransferWidth_le
    H R eps hR heps B b m n hn
  have hk := p4Q2PZ37AGZ_originalKernelMax_le_TaylorMax H d B b m n hn
  have hf := p4Q2PZ37AGZ_originalFloorWidth_le_TaylorGap H m n hn
  have hp := p4Q2PZ37AGY_sourceEnvelope_nonneg H
  have hSum :
      p4Q2PZ37AGY_originalKernelMax H d B b m n hn +
        p4Q2PZ37AGY_originalFloorWidth H m n hn / 2 ≤
      p4Q2PZ37AGZ_originalKernelTaylorMax H d B b m n hn +
        p4Q2PZ37AGZ_originalFloorTaylorGap H m n hn / 2 := by
    linarith only [hk, hf]
  have hMul := mul_le_mul_of_nonneg_left hSum hp
  linarith only [hOld, hMul]

/-- Finite exact-rational obligations suffice to certify a chosen
physical signed-transfer interval width. This is a conditional checker,
NOT a claim that its conditions hold at arbitrarily fine precision. -/
theorem p4Q2PZ37AGZ_transferWidth_of_rationalChecks
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (etaK etaF : ℚ)
    (hK : p4Q2PZ37AGZ_originalKernelTaylorMax H
      (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps) B b m n hn ≤ etaK)
    (hF : p4Q2PZ37AGZ_originalFloorTaylorGap H m n hn ≤ etaF) :
    (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).upper -
      (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).lower ≤
      (p4Q2PZ37AGN_countRational H / 2) * (etaK + etaF / 2) +
        2 * p4Q2PZ37AGV_uniformSlope H m * R +
        2 * p4Q2PZ37AGN_transferRadius H m n hn * eps := by
  have hOld := p4Q2PZ37AGZ_fineOriginalTransferWidth_le_Taylor
    H R eps hR heps B b m n hn
  have hp := p4Q2PZ37AGY_sourceEnvelope_nonneg H
  have hSum :
      p4Q2PZ37AGZ_originalKernelTaylorMax H
        (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps) B b m n hn +
          p4Q2PZ37AGZ_originalFloorTaylorGap H m n hn / 2 ≤ etaK + etaF / 2 := by
    linarith only [hK, hF]
  have hMul := mul_le_mul_of_nonneg_left hSum hp
  linarith only [hOld, hMul]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_exponentSpan_le_couplingTail
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_originalKernelExponentSpan_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_originalFloorAction_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_originalFloorExponentSpan_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_originalKernelTaylorGap_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_originalFloorTaylorGap_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_originalKernelWidth_le_TaylorGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_originalFloorWidth_le_TaylorGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_originalKernelMax_le_TaylorMax
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_fineOriginalTransferWidth_le_Taylor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGZ_transferWidth_of_rationalChecks
