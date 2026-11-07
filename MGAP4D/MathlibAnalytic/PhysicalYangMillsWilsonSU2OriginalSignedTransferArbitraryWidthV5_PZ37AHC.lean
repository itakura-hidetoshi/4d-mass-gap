import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedVolumeTaylorPrecisionV5_PZ37AHB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHC — arbitrary precision of ORIGINAL signed-transfer intervals

AHB proved that for each FIXED finite H one pair of actual AGK coupling
and AGJ Taylor orders m,n bounds the true AGM clipped-kernel maximum and
the true AGN global floor width on EVERY chosen original AGU Borel grid
and rational-coordinate right boundary.

The other two physical errors in AGY's original signed transfer width
are its actual cell radius R and total original rational Haar mass
width eps. They can be chosen independently once the actual AGV geometry
slope and original AGN global transfer radius have uniform-in-orders
rational upper bounds:
   L_H(m) <= Lcap_H = 6 + 13 * p_H / 2
   M_H(m,n) <= Mcap_H = p_H / 4.

This leaf constructs a strictly positive rational mesh q from a requested
positive rational transfer-width tolerance eta. AHB then picks ONE pair
of m,n, simultaneously valid for all actual AGU grids of radius/mass
precision q and ALL original AGL-rational right boundaries. AGY produces
a verified interval for the literal original signed transfer, width < eta.

It preserves the same original signed Haar integrand, physical Wilson
kernel, centering, global floor, Borel partition and exact-source proofs.
This is fixed-volume approximation precision, NOT an actual nonzero
transfer sign, two-sign shell, H-uniform coercivity, Hamiltonian gap
or continuum 4D Yang–Mills mass gap. The selected AGU grid may remain
classical/noncomputable; no large-H numerical table is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Pure rational algebra: a source-width term plus geometry and
actual signed-Haar mass uncertainty has one common finite budget.
The estimate does not replace true masses with rational surrogates. -/
theorem p4Q2PZ37AHC_threeErrorBudget_le
    (p L M Lcap Mcap K F R eps q : ℚ)
    (hp : 0 ≤ p) (hLc : 0 ≤ Lcap) (hMc : 0 ≤ Mcap)
    (hL : L ≤ Lcap) (hM : M ≤ Mcap)
    (hK : K ≤ q) (hF : F ≤ q)
    (hR : 0 ≤ R) (hRq : R ≤ q)
    (heps : 0 ≤ eps) (hepsq : eps ≤ q) (hq : 0 ≤ q) :
    (p / 2) * (K + F / 2) + 2 * L * R + 2 * M * eps ≤
      (p + 2 * Lcap + 2 * Mcap) * q := by
  have hp2 : 0 ≤ p / (2 : ℚ) := div_nonneg hp (by norm_num)
  have hKF : K + F / 2 ≤ 2 * q := by
    linarith only [hK, hF, hq]
  have hSource : (p / 2) * (K + F / 2) ≤ p * q := by
    calc
      (p / 2) * (K + F / 2) ≤ (p / 2) * (2 * q) :=
        mul_le_mul_of_nonneg_left hKF hp2
      _ = p * q := by ring
  have hGeometry : L * R ≤ Lcap * q := by
    calc
      L * R ≤ Lcap * R := mul_le_mul_of_nonneg_right hL hR
      _ ≤ Lcap * q := mul_le_mul_of_nonneg_left hRq hLc
  have hMass : M * eps ≤ Mcap * q := by
    calc
      M * eps ≤ Mcap * eps := mul_le_mul_of_nonneg_right hM heps
      _ ≤ Mcap * q := mul_le_mul_of_nonneg_left hepsq hMc
  have hGeo2 := mul_le_mul_of_nonneg_left hGeometry
    (by norm_num : (0 : ℚ) ≤ 2)
  have hMass2 := mul_le_mul_of_nonneg_left hMass
    (by norm_num : (0 : ℚ) ≤ 2)
  calc
    (p / 2) * (K + F / 2) + 2 * L * R + 2 * M * eps ≤
        p * q + 2 * Lcap * q + 2 * Mcap * q := by
          nlinarith only [hSource, hGeo2, hMass2]
    _ = (p + 2 * Lcap + 2 * Mcap) * q := by ring

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2

local instance p4Q2PZ37AHC_links : Fintype Link := Fintype.ofFinite _

/-- Exact order-independent rational bound for original cell oscillations.
No beta0 replacement: the AGK bracket betaUpper(m) <= 1 is proved. -/
def p4Q2PZ37AHC_slopeCap : ℚ :=
  6 + 13 * (p4Q2PZ37AGN_countRational H / 2)

/-- Exact order-independent bound for the ORIGINAL global transfer radius. -/
def p4Q2PZ37AHC_radiusCap : ℚ :=
  p4Q2PZ37AGN_countRational H / 4

/-- Strictly positive rational denominator for one common allocation
of original kernel, floor, geometry and Haar-mass precision. -/
def p4Q2PZ37AHC_totalCap : ℚ :=
  p4Q2PZ37AGN_countRational H +
    2 * p4Q2PZ37AHC_slopeCap H +
    2 * p4Q2PZ37AHC_radiusCap H + 1

/-- A single fully rational positive budget for all four physical errors. -/
def p4Q2PZ37AHC_meshPrecision (eta : ℚ) : ℚ :=
  eta / (4 * p4Q2PZ37AHC_totalCap H)

theorem p4Q2PZ37AHC_count_nonneg :
    0 ≤ p4Q2PZ37AGN_countRational H := by
  unfold p4Q2PZ37AGN_countRational
  positivity

theorem p4Q2PZ37AHC_slopeCap_nonneg :
    0 ≤ p4Q2PZ37AHC_slopeCap H := by
  have hp := p4Q2PZ37AHC_count_nonneg H
  unfold p4Q2PZ37AHC_slopeCap
  positivity

theorem p4Q2PZ37AHC_radiusCap_nonneg :
    0 ≤ p4Q2PZ37AHC_radiusCap H := by
  have hp := p4Q2PZ37AHC_count_nonneg H
  unfold p4Q2PZ37AHC_radiusCap
  positivity

theorem p4Q2PZ37AHC_totalCap_pos :
    0 < p4Q2PZ37AHC_totalCap H := by
  have hp := p4Q2PZ37AHC_count_nonneg H
  have hL := p4Q2PZ37AHC_slopeCap_nonneg H
  have hM := p4Q2PZ37AHC_radiusCap_nonneg H
  unfold p4Q2PZ37AHC_totalCap
  linarith only [hp, hL, hM]

theorem p4Q2PZ37AHC_meshPrecision_pos
    (eta : ℚ) (heta : 0 < eta) :
    0 < p4Q2PZ37AHC_meshPrecision H eta := by
  unfold p4Q2PZ37AHC_meshPrecision
  exact div_pos heta
    (mul_pos (by norm_num) (p4Q2PZ37AHC_totalCap_pos H))

/-- The common fixed-H mesh costs exactly a quarter of the target
after multiplying by the full positive original error cap. -/
theorem p4Q2PZ37AHC_totalCap_mul_mesh (eta : ℚ) :
    p4Q2PZ37AHC_totalCap H * p4Q2PZ37AHC_meshPrecision H eta =
      eta / 4 := by
  have hC : p4Q2PZ37AHC_totalCap H ≠ 0 :=
    ne_of_gt (p4Q2PZ37AHC_totalCap_pos H)
  unfold p4Q2PZ37AHC_meshPrecision
  field_simp
  ring

/-- ALL original AGV slope certificates are bounded by the same
genuine original plaquette-count expression, without a dependence on m. -/
theorem p4Q2PZ37AHC_uniformSlope_le_cap (m : ℕ) :
    p4Q2PZ37AGV_uniformSlope H m ≤ p4Q2PZ37AHC_slopeCap H := by
  have hU := (p4Q2PZ37AHB_couplingBracket_unit m).2.2
  have hp := p4Q2PZ37AGY_sourceEnvelope_nonneg H
  have hMul : p4Q2PZ37AGK_upper m *
      (p4Q2PZ37AGN_countRational H / 2) ≤
      1 * (p4Q2PZ37AGN_countRational H / 2) :=
    mul_le_mul_of_nonneg_right hU hp
  have h13 := mul_le_mul_of_nonneg_left hMul
    (by norm_num : (0 : ℚ) ≤ 13)
  unfold p4Q2PZ37AGV_uniformSlope p4Q2PZ37AHC_slopeCap
  nlinarith only [h13]

/-- The original real transfer is enclosed by AGN's rational radius,
which never exceeds p_H/4 for ANY coupling/Taylor precision. -/
theorem p4Q2PZ37AHC_transferRadius_le_cap
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGN_transferRadius H m n hn ≤
      p4Q2PZ37AHC_radiusCap H := by
  simpa only [p4Q2PZ37AHC_radiusCap] using
    p4Q2PZ37AGN_transferRadius_le_quarterCount H m n hn

/-- The ACTUAL AGU fine-original-signed-transfer interval width is
bounded by the fixed-volume cap, whenever the SAME genuinely chosen
Borel precision grid has radius and Haar-width at most q and AHB
supplies both literal kernel/floor errors at most q. -/
theorem p4Q2PZ37AHC_fineOriginalTransferWidth_le_commonBudget
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) (q : ℚ)
    (hRq : R ≤ q) (hepsq : eps ≤ q)
    (hK : p4Q2PZ37AGY_originalKernelMax H
      (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps)
      B b m n hn ≤ q)
    (hF : p4Q2PZ37AGY_originalFloorWidth H m n hn ≤ q) :
    (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).upper -
      (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).lower ≤
        (p4Q2PZ37AGN_countRational H +
          2 * p4Q2PZ37AHC_slopeCap H +
          2 * p4Q2PZ37AHC_radiusCap H) * q := by
  have hOrig := p4Q2PZ37AGY_fineOriginalTransferWidth_le
    H R eps hR heps B b m n hn
  have hBound := p4Q2PZ37AHC_threeErrorBudget_le
    (p4Q2PZ37AGN_countRational H)
    (p4Q2PZ37AGV_uniformSlope H m)
    (p4Q2PZ37AGN_transferRadius H m n hn)
    (p4Q2PZ37AHC_slopeCap H)
    (p4Q2PZ37AHC_radiusCap H)
    (p4Q2PZ37AGY_originalKernelMax H
      (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps) B b m n hn)
    (p4Q2PZ37AGY_originalFloorWidth H m n hn) R eps q
    (p4Q2PZ37AHC_count_nonneg H)
    (p4Q2PZ37AHC_slopeCap_nonneg H)
    (p4Q2PZ37AHC_radiusCap_nonneg H)
    (p4Q2PZ37AHC_uniformSlope_le_cap H m)
    (p4Q2PZ37AHC_transferRadius_le_cap H m n hn)
    hK hF hR.le hRq heps.le hepsq (hR.le.trans hRq)
  exact hOrig.trans hBound

/-- FINAL fixed-volume arbitrary precision for the literal original
signed transfer. One pair m,n and one genuine AGU radius/normalized-Haar
width R,eps work simultaneously for every original rational-coordinate
right boundary B. All four parameters are chosen BEFORE B. The original
verified interval contains the SAME signed physical transfer value. -/
theorem p4Q2PZ37AHC_exists_fineOriginalTransfer_precision
    (eta : ℚ) (heta : 0 < eta) :
    ∃ R eps : ℚ, ∃ hR : 0 < R, ∃ heps : 0 < eps,
      ∃ m n : ℕ, ∃ hn : 0 < n,
        ∀ (B : Cfg)
          (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)),
          (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).upper -
            (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).lower <
              eta := by
  let q : ℚ := p4Q2PZ37AHC_meshPrecision H eta
  have hq : 0 < q := p4Q2PZ37AHC_meshPrecision_pos H eta heta
  obtain ⟨m, n, hn, hPrecision⟩ :=
    p4Q2PZ37AHB_exists_originalKernelFloor_precision H q hq
  refine ⟨q, q, hq, hq, m, n, hn, ?_⟩
  intro B b
  let d := p4Q2PZ37AGU_fineOriginalGridData H q q hq hq
  obtain ⟨hK, hF⟩ := hPrecision d B b
  have hWidth := p4Q2PZ37AHC_fineOriginalTransferWidth_le_commonBudget
    H q q hq hq B b m n hn q (le_refl _) (le_refl _) hK.le hF.le
  have hFull : (p4Q2PZ37AGN_countRational H +
        2 * p4Q2PZ37AHC_slopeCap H +
        2 * p4Q2PZ37AHC_radiusCap H) ≤
      p4Q2PZ37AHC_totalCap H := by
    unfold p4Q2PZ37AHC_totalCap
    linarith
  have hCapMul := mul_le_mul_of_nonneg_right hFull hq.le
  have hMesh : p4Q2PZ37AHC_totalCap H * q = eta / 4 := by
    simpa only [q] using p4Q2PZ37AHC_totalCap_mul_mesh H eta
  have hQuarter : eta / 4 < eta := by linarith only [heta]
  calc
    (p4Q2PZ37AGU_fineOriginalTransferInterval H q q hq hq B b m n hn).upper -
        (p4Q2PZ37AGU_fineOriginalTransferInterval H q q hq hq B b m n hn).lower ≤
      (p4Q2PZ37AGN_countRational H +
        2 * p4Q2PZ37AHC_slopeCap H +
        2 * p4Q2PZ37AHC_radiusCap H) * q := hWidth
    _ ≤ p4Q2PZ37AHC_totalCap H * q := hCapMul
    _ = eta / 4 := hMesh
    _ < eta := hQuarter

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHC_threeErrorBudget_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_count_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_slopeCap_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_radiusCap_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_totalCap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_meshPrecision_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_totalCap_mul_mesh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_uniformSlope_le_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_transferRadius_le_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_fineOriginalTransferWidth_le_commonBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHC_exists_fineOriginalTransfer_precision
