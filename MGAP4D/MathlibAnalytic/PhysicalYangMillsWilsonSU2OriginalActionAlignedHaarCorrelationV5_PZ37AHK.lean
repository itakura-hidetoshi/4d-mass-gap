import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTrueHaarHalfSourceSignStabilityV5_PZ37AHJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHK — original Wilson-action aligned signed-transfer witnesses

AHH proved the literal ZW centered source has strictly positive TRUE
full-Wilson-kernel spatial Haar quadratic energy for every finite H.
The quadratic does more than show that the transfer is not the zero
function: it is EXACTLY the original Haar pairing between the true
centered spatial Wilson action f_H and the same signed transfer t_H.

Therefore some genuine right spatial boundary has f_H(B)*t_H(B)>0:
the transfer has the SAME sign as the deviation of the original
spatial Wilson action from its proved reference Haar mean.

Using the real source Lipschitz estimate of AGG, the TRUE transfer
modulus and half-Haar source budget of AHJ, and the original explicit
AHG rational SU(2) mesh, the product correlation error is bounded by

  |f(B)t(B) - f(B_N,a)t(B_N,a)|
      <= (24*p_H^2 + (13/128)*p_H^3)/N.

This is a rational-coefficient bound using no invented probability
or altered original physical observable. It provides unconditional
existence of a genuine rational-coordinate right boundary where
the actual spatial Wilson action and transfer have matching strict signs.

The exact rational evaluation of the original action at that right
boundary is retained through AGN/AGL Type-valued evidence. AHE's
complete true-Haar AGP sign certification then yields an ORIGINAL
rational-table sign witness whose sign is aligned with the EXACT
rational original centered spatial Wilson action.

The right-boundary AHG mesh and the LEFT Haar AGU proof-carrying
quadrature grid are DISTINCT objects throughout.

The numerical center label, sign branch, Haar interval endpoints
and rational margin are existential, NOT executed or evaluated.
No both-sign result, uniform coercivity, Hamiltonian or continuum gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Exact signed-product difference bound over real numbers. -/
theorem p4Q2PZ37AHK_abs_product_difference
    (x y x' y' : ℝ) :
    |x * y - x' * y'| ≤
      |x| * |y - y'| + |y'| * |x - x'| := by
  calc
    |x * y - x' * y'| =
        |x * (y - y') + y' * (x - x')| := by ring
    _ ≤ |x * (y - y')| + |y' * (x - x')| :=
      abs_add_le _ _
    _ = |x| * |y - y'| + |y'| * |x - x'| := by
      rw [abs_mul, abs_mul]

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ

local instance p4Q2PZ37AHK_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHK_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHK_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHK_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHK_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta0
local notation "t" => decomposableOneSliceTransferIntegral H 2 beta0 f0
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "mesh" => p4Q2PZ37AHH_meshBoundary H

local instance p4Q2PZ37AHK_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHK_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The genuinely original full-Wilson Haar quadratic is the Haar
pairing of the same original continuous ZW centered source with the
genuine source-to-right-boundary transfer. No modified transfer. -/
theorem p4Q2PZ37AHK_originalHaarQuadratic_eq_signedCorrelation :
    (∫ A : Cfg, ∫ B : Cfg,
      K A B * (fCont A * fCont B) ∂muH ∂muH) =
      ∫ A : Cfg, fCont A * t A ∂muH := by
  have hRep :
      (fun A : Cfg => (f0 : Lp ℝ 2 muH) A) =ᵐ[muH] fCont := by
    rw [p4Q2PZ37AFZ_originalCenteredSource_eq_toLp]
    exact ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := (2 : ENNReal))
      (μ := muH) fCont
  apply integral_congr_ae
  filter_upwards with A
  have hSym (B : Cfg) : K A B = K B A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_symmetric
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A B
  calc
    (∫ B : Cfg, K A B * (fCont A * fCont B) ∂muH) =
        fCont A * (∫ B : Cfg, K B A * fCont B ∂muH) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with B
      rw [hSym B]
      ring
    _ = fCont A * t A := by
      rw [p4Q2LJ_originalPhysicalTransfer_eq_continuousWilsonKernelIntegral
        H beta0 f0 fCont hRep A]

/-- Strict positive ORIGINAL reference Haar energy for the actual
centered ZW action against its authentic full-Wilson transfer. -/
theorem p4Q2PZ37AHK_originalSignedCorrelation_pos :
    0 < (∫ B : Cfg, fCont B * t B ∂muH) := by
  rw [← p4Q2PZ37AHK_originalHaarQuadratic_eq_signedCorrelation H]
  exact p4Q2PZ37AHH_originalSource_fullQuadratic_pos H

/-- Strict Haar correlation forces SOME original right boundary
where the authentic centered Wilson source and its transfer have
MATCHING nonzero signs, rather than merely nonzero transfer. -/
theorem p4Q2PZ37AHK_exists_originalActionAlignedBoundary :
    ∃ B : Cfg, 0 < fCont B * t B := by
  by_contra hn
  push_neg at hn
  have hNonpos (B : Cfg) : fCont B * t B ≤ 0 := hn B
  have hInt : (∫ B : Cfg, fCont B * t B ∂muH) ≤ 0 :=
    integral_nonpos hNonpos
  exact (not_lt_of_ge hInt) (p4Q2PZ37AHK_originalSignedCorrelation_pos H)

/-- All constants are actual Wilson data: original p_H, AGG's
source slope 12, AEV's kernel slope and AHJ's true Haar L1 half bound. -/
def p4Q2PZ37AHK_rationalProductMeshBudget : ℝ :=
  24 * pH ^ 2 + (13 / 128 : ℝ) * pH ^ 3

theorem p4Q2PZ37AHK_rationalProductMeshBudget_nonneg :
    0 ≤ p4Q2PZ37AHK_rationalProductMeshBudget H := by
  unfold p4Q2PZ37AHK_rationalProductMeshBudget p4Q2PZ37AFZ_plaquetteCount
  positivity

/-- SAME AHG rational right-boundary approximation simultaneously
controls f_H and t_H. Each link uses the SAME certified original SU(2)
center: the two error bounds are not glued from unrelated witnesses. -/
theorem p4Q2PZ37AHK_jointMeshProductError
    (B : Cfg) (N : ℕ) (hN : 0 < N) :
    ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
      |fCont B * t B -
          fCont (mesh N a) * t (mesh N a)| ≤
        p4Q2PZ37AHK_rationalProductMeshBudget H / (N : ℝ) := by
  choose a ha using (fun e : Link =>
    p4Q2PZ37AHG_originalMesh_cover N hN (B e))
  let C : Cfg := mesh N a
  have hEach (e : Link) : dJ (B e) (C e) ≤ 4 / (N : ℝ) := by
    have h := ha e
    change dJ (p4Q2PZ37AHG_originalMeshCenter N (a e)) (B e) < 4 / (N : ℝ) at h
    rw [p4Q2PZ37ADK_trueChordalDistance_symm] at h
    exact h.le
  have hDist : Dsp B C ≤ pH * (4 / (N : ℝ)) := by
    unfold p4Q2PZ37AGG_originalSpatialChordalDistance
    calc
      (∑ e : Link, dJ (B e) (C e)) ≤
          ∑ _e : Link, 4 / (N : ℝ) :=
        Finset.sum_le_sum (fun e _ => hEach e)
      _ = (Fintype.card Link : ℝ) * (4 / (N : ℝ)) := by simp
      _ = pH * (4 / (N : ℝ)) := by
        rw [p4Q2PZ37AHI_cardLinks_eq_plaquettes H]
  have hDNonneg : 0 ≤ Dsp B C :=
    p4Q2PZ37AGG_originalSpatialChordalDistance_nonneg H B C
  have hp : 0 ≤ pH := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  have hF : |fCont B - fCont C| ≤ 48 * pH / (N : ℝ) := by
    calc
      |fCont B - fCont C| ≤ 12 * Dsp B C :=
        p4Q2PZ37AGG_originalCenteredSource_allLinkChordalSlope H B C
      _ ≤ 12 * (pH * (4 / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hDist (by norm_num)
      _ = 48 * pH / (N : ℝ) := by ring
  have hT : |t B - t C| ≤ (13 / 64 : ℝ) * pH ^ 2 / (N : ℝ) := by
    calc
      |t B - t C| ≤ p4Q2PZ37AHH_transferSlope H * Dsp B C :=
        p4Q2PZ37AHH_originalTransfer_allLinkSlope H B C
      _ ≤ ((13 / 256 : ℝ) * pH) * Dsp B C :=
        mul_le_mul_of_nonneg_right
          (p4Q2PZ37AHJ_transferSlope_le_halfRational H) hDNonneg
      _ ≤ ((13 / 256 : ℝ) * pH) * (pH * (4 / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hDist (by positivity)
      _ = (13 / 64 : ℝ) * pH ^ 2 / (N : ℝ) := by ring
  have hFBound : |fCont B| ≤ pH / 2 :=
    p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H B
  have hTBound : |t C| ≤ pH / 2 :=
    p4Q2PZ37AHJ_originalTransfer_abs_le_halfCount H C
  have hTerm1 :
      |fCont B| * |t B - t C| ≤
        (pH / 2) * ((13 / 64 : ℝ) * pH ^ 2 / (N : ℝ)) := by
    calc
      |fCont B| * |t B - t C| ≤
          (pH / 2) * |t B - t C| :=
        mul_le_mul_of_nonneg_right hFBound (abs_nonneg _)
      _ ≤ (pH / 2) * ((13 / 64 : ℝ) * pH ^ 2 / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
  have hTerm2 :
      |t C| * |fCont B - fCont C| ≤
        (pH / 2) * (48 * pH / (N : ℝ)) := by
    calc
      |t C| * |fCont B - fCont C| ≤
          (pH / 2) * |fCont B - fCont C| :=
        mul_le_mul_of_nonneg_right hTBound (abs_nonneg _)
      _ ≤ (pH / 2) * (48 * pH / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
  refine ⟨a, ?_⟩
  change |fCont B * t B - fCont C * t C| ≤
    p4Q2PZ37AHK_rationalProductMeshBudget H / (N : ℝ)
  calc
    |fCont B * t B - fCont C * t C| ≤
        |fCont B| * |t B - t C| +
          |t C| * |fCont B - fCont C| :=
      p4Q2PZ37AHK_abs_product_difference _ _ _ _
    _ ≤ (pH / 2) * ((13 / 64 : ℝ) * pH ^ 2 / (N : ℝ)) +
          (pH / 2) * (48 * pH / (N : ℝ)) :=
      add_le_add hTerm1 hTerm2
    _ = p4Q2PZ37AHK_rationalProductMeshBudget H / (N : ℝ) := by
      unfold p4Q2PZ37AHK_rationalProductMeshBudget
      ring

/-- A nonzero original action-transfer pairing is preserved at a TRUE
explicit rational SU(2) right boundary. No numerical boundary is selected. -/
theorem p4Q2PZ37AHK_exists_alignedRationalMeshBoundary :
    ∃ N : ℕ, 96 < N ∧
      ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
        0 < fCont (mesh N a) * t (mesh N a) := by
  obtain ⟨B, hB⟩ := p4Q2PZ37AHK_exists_originalActionAlignedBoundary H
  have hs : 0 < fCont B * t B / 2 := by positivity
  obtain ⟨N, h96, hN, hSmall⟩ :=
    p4Q2PZ37AHI_exists_largeDenominator
      (p4Q2PZ37AHK_rationalProductMeshBudget H)
      (fCont B * t B / 2)
      (p4Q2PZ37AHK_rationalProductMeshBudget_nonneg H) hs 96
  obtain ⟨a, hError⟩ :=
    p4Q2PZ37AHK_jointMeshProductError H B N hN
  have hUpper := (abs_le.mp hError).2
  refine ⟨N, h96, a, ?_⟩
  linarith only [hUpper, hSmall, hB]

/-- The actual right-boundary spatial action itself has a rational
AGL/AGN exact value, allowing a finite exact source-sign test. Together
with AHE's complete ORIGINAL true-Haar AGP sign certificate, one
unconditionally obtains a strictly aligned rational-source/sign-table
witness. Neither the rational label nor the sign branch is evaluated. -/
theorem p4Q2PZ37AHK_exists_actionAlignedOriginalHaarCertificate :
    ∃ N : ℕ, 96 < N ∧
      ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
        ((0 < p4Q2PZ37AGN_centeredActionRational H (mesh N a)
                (p4Q2PZ37AHH_meshBoundary_coordinates H N a) ∧
            p4Q2PZ37AHE_finePositiveCertificate H (mesh N a)
                (p4Q2PZ37AHH_meshBoundary_coordinates H N a)) ∨
         (p4Q2PZ37AGN_centeredActionRational H (mesh N a)
                (p4Q2PZ37AHH_meshBoundary_coordinates H N a) < 0 ∧
            p4Q2PZ37AHE_fineNegativeCertificate H (mesh N a)
                (p4Q2PZ37AHH_meshBoundary_coordinates H N a))) := by
  obtain ⟨N, h96, a, hAligned⟩ :=
    p4Q2PZ37AHK_exists_alignedRationalMeshBoundary H
  let B : Cfg := mesh N a
  let b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e) :=
    p4Q2PZ37AHH_meshBoundary_coordinates H N a
  let q : ℚ := p4Q2PZ37AGN_centeredActionRational H B b
  have hExact : fCont B = (q : ℝ) :=
    p4Q2PZ37AGN_originalCenteredContinuous_rational H B b
  refine ⟨N, h96, a, ?_⟩
  change (0 < q ∧ p4Q2PZ37AHE_finePositiveCertificate H B b) ∨
    (q < 0 ∧ p4Q2PZ37AHE_fineNegativeCertificate H B b)
  rcases (mul_pos_iff.mp hAligned) with ⟨hSource, hTransfer⟩ | ⟨hSource, hTransfer⟩
  · have hReal : (0 : ℝ) < (q : ℝ) := by rw [← hExact]; exact hSource
    have hRat : (0 : ℚ) < q := by exact_mod_cast hReal
    exact Or.inl ⟨hRat,
      (p4Q2PZ37AHE_finePositive_iff H B b).mpr hTransfer⟩
  · have hReal : (q : ℝ) < 0 := by rw [← hExact]; exact hSource
    have hRat : q < (0 : ℚ) := by exact_mod_cast hReal
    exact Or.inr ⟨hRat,
      (p4Q2PZ37AHE_fineNegative_iff H B b).mpr hTransfer⟩

/-- One strictly positive RATIONAL correlation margin survives on
a real signed product f_H(B_N)*T_H(B_N) at every sufficiently large
actual original rational right-boundary mesh order. The rational q is
existential and is NOT an evaluated magnitude or sign branch. -/
theorem p4Q2PZ37AHK_eventualAllOrdersAlignedCorrelationMargin :
    ∃ q : ℚ, 0 < q ∧ ∃ N₀ : ℕ, 96 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∃ a : Link → p4Q2PZ37AHG_meshIndex N,
          (q : ℝ) < fCont (mesh N a) * t (mesh N a) := by
  obtain ⟨B, hB⟩ := p4Q2PZ37AHK_exists_originalActionAlignedBoundary H
  have hs : 0 < fCont B * t B / 2 := by positivity
  obtain ⟨q, hqPos, hqBound⟩ := exists_rat_btwn hs
  have hq : (0 : ℚ) < q := by exact_mod_cast hqPos
  obtain ⟨N₀, h96, hAll⟩ :=
    p4Q2PZ37AHJ_eventually_small_denominator
      (p4Q2PZ37AHK_rationalProductMeshBudget H)
      (fCont B * t B / 2)
      (p4Q2PZ37AHK_rationalProductMeshBudget_nonneg H) hs 96
  refine ⟨q, hq, N₀, h96, ?_⟩
  intro N hN₀N
  have hN : 0 < N := by omega
  obtain ⟨a, hError⟩ :=
    p4Q2PZ37AHK_jointMeshProductError H B N hN
  have hUpper := (abs_le.mp hError).2
  refine ⟨a, ?_⟩
  have hSmall := hAll N hN₀N
  linarith only [hUpper, hSmall, hqBound]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHK_abs_product_difference
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHK_originalHaarQuadratic_eq_signedCorrelation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHK_originalSignedCorrelation_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHK_exists_originalActionAlignedBoundary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHK_rationalProductMeshBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHK_jointMeshProductError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHK_exists_alignedRationalMeshBoundary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHK_exists_actionAlignedOriginalHaarCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHK_eventualAllOrdersAlignedCorrelationMargin
