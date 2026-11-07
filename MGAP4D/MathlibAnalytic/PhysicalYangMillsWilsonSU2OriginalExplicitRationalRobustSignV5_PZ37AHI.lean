import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNonzeroRationalSignExistenceV5_PZ37AHH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHI — explicit rational spatial mesh error and stable sign margins

AHH proved unconditional EXISTENCE of a nonzero original centered ZW transfer
and of a finite original AGP true-Haar rational sign table, for every H.
AHI keeps the same source, complete Wilson kernel, fixed beta, left Haar data
and right rational AHG mesh. It converts the true one-link Lipschitz budget
to an EXPLICIT rational finite-volume envelope independent of an unknown
source Haar integral:

  beta0 = log(3/2)/64 <= 1/128,
  Msrc(H) <= p_H,  card(Link_H)=p_H,
  |T_H(B)-T_H(B_(N,a))| <= 13*p_H^2/(32*N).

Therefore a certified original table lower bound q>0 (respectively
upper <=-q) remains strictly separated with margin q/2 on every
sufficiently fine rational right-boundary mesh. There is one rational
q>0 and one sign branch which has witnesses at UNBOUNDED mesh orders.
This is stronger than a single existential rational boundary, but is
still not a numerically evaluated N, boundary assignment, Haar table
or Boolean sign branch. AHI does not claim both signs, a volume-uniform
coercivity constant or any Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Archimedean denominator bound with an arbitrary previously requested
mesh order. The proof uses only actual real arithmetic and a finite N. -/
theorem p4Q2PZ37AHI_exists_largeDenominator
    (C s : ℝ) (hC : 0 ≤ C) (hs : 0 < s) (M : ℕ) :
    ∃ N : ℕ, M < N ∧ 0 < N ∧ C / (N : ℝ) < s := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((M : ℝ) + 1 + C / s)
  have hCs : 0 ≤ C / s := div_nonneg hC hs.le
  have hMr : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hNm : (M : ℝ) < (N : ℝ) := by linarith only [hN, hCs]
  have hM : M < N := by exact_mod_cast hNm
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith only [hNm, hMr]
  have hNpos : 0 < N := by exact_mod_cast hNr
  have hQuot : C / s < (N : ℝ) := by linarith only [hN, hMr]
  have hBound : C < (N : ℝ) * s := (div_lt_iff₀ hs).mp hQuot
  refine ⟨N, hM, hNpos, ?_⟩
  exact (div_lt_iff₀ hNr).mpr (by nlinarith only [hBound])

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHI_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHI_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHI_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHI_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHI_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "t" => decomposableOneSliceTransferIntegral H 2 beta0
  (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
local notation "mesh" => p4Q2PZ37AHH_meshBoundary H

local instance p4Q2PZ37AHI_links : Fintype Link := Fintype.ofFinite _

/-- The fixed coupling has a simple exact RATIONAL upper enclosure.
No transcendental floating-point approximation is used. -/
theorem p4Q2PZ37AHI_fixedCoupling_le_one128 :
    beta0 ≤ (1 / 128 : ℝ) := by
  have hLog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  have hHalf : Real.log (3 / 2 : ℝ) ≤ (1 / 2 : ℝ) := by
    linarith only [hLog]
  unfold p4Q2PZ37ADC_fixedCoupling
  linarith only [hHalf]

/-- The genuine original source Haar L1 budget, bounded by the original
spatial plaquette count, removes all unknown Haar quantities from the slope. -/
theorem p4Q2PZ37AHI_transferSlope_le_rational :
    p4Q2PZ37AHH_transferSlope H ≤ (13 / 128 : ℝ) * pH := by
  have hb : 0 ≤ 13 * beta0 :=
    mul_nonneg (by norm_num) p4Q2PZ37ADC_fixedCoupling_pos.le
  have hbUpper : 13 * beta0 ≤ (13 / 128 : ℝ) := by
    have h := p4Q2PZ37AHI_fixedCoupling_le_one128
    linarith only [h]
  have hm : Msrc ≤ pH := p4Q2PZ37AFZ_originalCenteredSource_L1_le_plaquetteCount H
  have hp : 0 ≤ pH := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  change (13 * beta0) * Msrc ≤ (13 / 128 : ℝ) * pH
  calc
    (13 * beta0) * Msrc ≤ (13 * beta0) * pH :=
      mul_le_mul_of_nonneg_left hm hb
    _ ≤ (13 / 128 : ℝ) * pH :=
      mul_le_mul_of_nonneg_right hbUpper hp

/-- Original positive links and original plaquettes have the same
finite cardinal, as already proved in AHF; these are not new links. -/
theorem p4Q2PZ37AHI_cardLinks_eq_plaquettes :
    (Fintype.card Link : ℝ) = pH := by
  have h := p4Q2PZ37AHF_count_eq_links H
  have hr : (Fintype.card Link : ℝ) =
      ((p4Q2PZ37AGN_countRational H : ℚ) : ℝ) := by
    exact_mod_cast h.symm
  exact hr.trans (p4Q2PZ37AGN_countRational_exact H)

/-- At EVERY finite N>0 one can approximate ANY original right boundary
by an explicitly specified rational AHG right mesh with a certified,
COMPLETELY rational-coefficient error envelope. No numeric Haar mass
evaluation or compactness-selected center enters this error estimate. -/
theorem p4Q2PZ37AHI_explicitMeshError (B : Cfg)
    (N : ℕ) (hN : 0 < N) :
    ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      |t B - t (mesh N a)| ≤ (13 / 32 : ℝ) * pH ^ 2 / (N : ℝ) := by
  obtain ⟨a, ha⟩ :=
    p4Q2PZ37AHH_originalTransfer_meshApproximation H B N hN
  have hp : 0 ≤ pH := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  have hNr : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hProduct : 0 ≤ pH * (4 / (N : ℝ)) :=
    mul_nonneg hp (div_nonneg (by norm_num) hNr)
  have hSlope : p4Q2PZ37AHH_transferSlope H *
      (pH * (4 / (N : ℝ))) ≤
      ((13 / 128 : ℝ) * pH) * (pH * (4 / (N : ℝ))) :=
    mul_le_mul_of_nonneg_right
      (p4Q2PZ37AHI_transferSlope_le_rational H) hProduct
  refine ⟨a, ?_⟩
  calc
    |t B - t (mesh N a)| ≤ p4Q2PZ37AHH_transferSlope H *
        ((Fintype.card Link : ℝ) * (4 / (N : ℝ))) := ha
    _ = p4Q2PZ37AHH_transferSlope H * (pH * (4 / (N : ℝ))) := by
      rw [p4Q2PZ37AHI_cardLinks_eq_plaquettes H]
    _ ≤ ((13 / 128 : ℝ) * pH) * (pH * (4 / (N : ℝ))) := hSlope
    _ = (13 / 32 : ℝ) * pH ^ 2 / (N : ℝ) := by ring

/-- A lower endpoint q>0 in the ACTUAL AGP table remains positive with
margin q/2 under the explicit rational right-mesh error criterion. -/
theorem p4Q2PZ37AHI_positiveMargin_onMesh
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (q : ℚ)
    (hCert : q ≤ (p4Q2PZ37AGP_originalTable H d B b m n hn).lower)
    (N : ℕ) (hN : 0 < N)
    (hSmall : (13 / 32 : ℝ) * pH ^ 2 / (N : ℝ) < (q : ℝ) / 2) :
    ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      (q : ℝ) / 2 < t (mesh N a) := by
  obtain ⟨a, hErr⟩ := p4Q2PZ37AHI_explicitMeshError H B N hN
  have hqReal : (q : ℝ) ≤
      ((p4Q2PZ37AGP_originalTable H d B b m n hn).lower : ℝ) := by
    exact_mod_cast hCert
  have hPhysical : (q : ℝ) ≤ t B :=
    hqReal.trans (p4Q2PZ37AGP_originalTransfer_bounds H d B b m n hn).1
  have hDelta := (abs_le.mp hErr).2
  refine ⟨a, ?_⟩
  linarith only [hPhysical, hDelta, hSmall]

/-- The negative branch uses the true AGP upper endpoint, never an
unsigned table or an assumed sign of the centered source. -/
theorem p4Q2PZ37AHI_negativeMargin_onMesh
    (d : p4Q2PZ37AGP_gridData H)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n)
    (q : ℚ)
    (hCert : (p4Q2PZ37AGP_originalTable H d B b m n hn).upper ≤ -q)
    (N : ℕ) (hN : 0 < N)
    (hSmall : (13 / 32 : ℝ) * pH ^ 2 / (N : ℝ) < (q : ℝ) / 2) :
    ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      t (mesh N a) < -(q : ℝ) / 2 := by
  obtain ⟨a, hErr⟩ := p4Q2PZ37AHI_explicitMeshError H B N hN
  have hqReal : ((p4Q2PZ37AGP_originalTable H d B b m n hn).upper : ℝ) ≤
      -(q : ℝ) := by exact_mod_cast hCert
  have hPhysical : t B ≤ -(q : ℝ) :=
    (p4Q2PZ37AGP_originalTransfer_bounds H d B b m n hn).2.trans hqReal
  have hDelta := (abs_le.mp hErr).1
  refine ⟨a, ?_⟩
  linarith only [hPhysical, hDelta, hSmall]

/-- Choose ONE strictly positive rational margin from the original AHH
accepted true-Haar table. The SAME sign and margin recur at unbounded
explicit AHG integer-mesh orders. This is an existential strong result,
not an actually evaluated finite sample or a claim of both signs. -/
theorem p4Q2PZ37AHI_unboundedRationalMeshSignMargin :
    ∃ q : ℚ, 0 < q ∧
      ((∀ M : ℕ, ∃ N : ℕ, M < N ∧
          ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
            (q : ℝ) < t (mesh N a)) ∨
       (∀ M : ℕ, ∃ N : ℕ, M < N ∧
          ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
            t (mesh N a) < -(q : ℝ))) := by
  obtain ⟨B, b, d, m, n, hn, hSign⟩ :=
    p4Q2PZ37AHH_exists_strictOriginalHaarTable H
  have hP : 0 ≤ (13 / 32 : ℝ) * pH ^ 2 := by positivity
  rcases hSign with hPos | hNeg
  · let Q : ℚ := (p4Q2PZ37AGP_originalTable H d B b m n hn).lower
    have hQ : 0 < Q := hPos
    have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    refine ⟨Q / 2, by positivity, Or.inl ?_⟩
    intro M
    obtain ⟨N, hMN, hNN, hSmall⟩ :=
      p4Q2PZ37AHI_exists_largeDenominator
        ((13 / 32 : ℝ) * pH ^ 2) ((Q : ℝ) / 2)
        hP (div_pos hQr (by norm_num)) M
    obtain ⟨a, ha⟩ := p4Q2PZ37AHI_positiveMargin_onMesh
      H d B b m n hn Q le_rfl N hNN hSmall
    refine ⟨N, hMN, a, ?_⟩
    simpa only [Rat.cast_div, Rat.cast_ofNat] using ha
  · let Q : ℚ := -(p4Q2PZ37AGP_originalTable H d B b m n hn).upper
    have hQ : 0 < Q := by dsimp [Q]; linarith only [hNeg]
    have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
    have hUpper : (p4Q2PZ37AGP_originalTable H d B b m n hn).upper ≤ -Q := by
      dsimp [Q]
      simp
    refine ⟨Q / 2, by positivity, Or.inr ?_⟩
    intro M
    obtain ⟨N, hMN, hNN, hSmall⟩ :=
      p4Q2PZ37AHI_exists_largeDenominator
        ((13 / 32 : ℝ) * pH ^ 2) ((Q : ℝ) / 2)
        hP (div_pos hQr (by norm_num)) M
    obtain ⟨a, ha⟩ := p4Q2PZ37AHI_negativeMargin_onMesh
      H d B b m n hn Q hUpper N hNN hSmall
    refine ⟨N, hMN, a, ?_⟩
    calc
      t (mesh N a) < -(Q : ℝ) / 2 := ha
      _ = -(((Q / 2 : ℚ) : ℝ)) := by push_cast; ring

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHI_exists_largeDenominator
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHI_fixedCoupling_le_one128
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHI_transferSlope_le_rational
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHI_cardLinks_eq_plaquettes
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHI_explicitMeshError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHI_positiveMargin_onMesh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHI_negativeMargin_onMesh
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHI_unboundedRationalMeshSignMargin
