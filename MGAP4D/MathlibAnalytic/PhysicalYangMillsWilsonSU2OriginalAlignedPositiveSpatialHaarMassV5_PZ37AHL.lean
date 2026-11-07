import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalActionAlignedHaarCorrelationV5_PZ37AHK
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUnconditionalHaarRadiusV5_PZ37ADZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHL — positive ORIGINAL spatial Haar mass of signed alignment

AHK proved the original centered spatial Wilson action f_H and the
true original full-Wilson signed transfer t_H have strictly positive
reference Haar pairing, hence f_H(B)*t_H(B)>0 at some physical B.

The positive set is not merely a point: derive a TRUE spatial-slice
all-link chordal Lipschitz coefficient

  |f_H(B)*t_H(B) - f_H(C)*t_H(C)|
    <= (6*p_H + (13/512)*p_H^2)*D_sp(B,C),

from the original AGG one-link source bound, AEV transfer slope,
AHJ genuine Haar half-source bound, and AHK signed product identity.

Unlike a two-boundary pair-Haar estimate, obtain a quantitative
one-slice Haar floor directly from ADZ's exact SU(2) small-ball
Haar geometry, using the SAME original product-Haar slice:

  mu_H{C: D_sp(B,C)<R} >=
    kappa(R/(card(Link_H)+1))^card(Link_H) > 0.

Here kappa is the original ADQ strictly positive sphere fraction
and card(Link_H)=p_H; no change to the physical Haar measure.

Consequently there exist a positive rational q and a true spatial
ball with positive Haar mass such that f_H(C)*t_H(C)>q throughout
the ball. This gives quantitatively positive true spatial-Haar
mass of the original action-transfer sign-aligned region.

This does NOT supply numerical q, actual boundary labels,
evaluated Haar tables, both signs, volume-uniform mass floors,
coercivity, Hamiltonian or continuum Yang--Mills gap.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AHL_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AHL_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AHL_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AHL_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AHL_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" => normalizedCompactHaar G
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "t" => decomposableOneSliceTransferIntegral H 2
  p4Q2PZ37ADC_fixedCoupling (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "kappa" => p4Q2PZ37ADQ_sphereRadiusFraction

local instance p4Q2PZ37AHL_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AHL_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Original spatial all-link ℓ¹ chordal ball, not a substitute metric. -/
def p4Q2PZ37AHL_originalSpatialBall (B : Cfg) (R : ℝ) : Set Cfg :=
  {C | Dsp B C < R}

/-- The SAME centered original action and signed transfer have a
strictly positive joint product by at least a rational margin. -/
def p4Q2PZ37AHL_originalAlignedRegion (q : ℚ) : Set Cfg :=
  {C | (q : ℝ) < fCont C * t C}

/-- The original action-transfer product's finite-volume chordal
Lipschitz coefficient, expressed using only true plaquette count. -/
def p4Q2PZ37AHL_productSlope : ℝ :=
  6 * pH + (13 / 512 : ℝ) * pH ^ 2

theorem p4Q2PZ37AHL_productSlope_nonneg :
    0 ≤ p4Q2PZ37AHL_productSlope H := by
  unfold p4Q2PZ37AHL_productSlope p4Q2PZ37AFZ_plaquetteCount
  positivity

/-- AHL product slope comes from the SAME original source f_H and
right-boundary original transfer t_H. No independent modulus premise. -/
theorem p4Q2PZ37AHL_originalProduct_allLinkSlope
    (B C : Cfg) :
    |fCont B * t B - fCont C * t C| ≤
      p4Q2PZ37AHL_productSlope H * Dsp B C := by
  have hp : 0 ≤ pH := by
    unfold p4Q2PZ37AFZ_plaquetteCount
    positivity
  have hD : 0 ≤ Dsp B C :=
    p4Q2PZ37AGG_originalSpatialChordalDistance_nonneg H B C
  have hT :
      |t B - t C| ≤ ((13 / 256 : ℝ) * pH) * Dsp B C := by
    calc
      |t B - t C| ≤
          p4Q2PZ37AHH_transferSlope H * Dsp B C :=
        p4Q2PZ37AHH_originalTransfer_allLinkSlope H B C
      _ ≤ ((13 / 256 : ℝ) * pH) * Dsp B C :=
        mul_le_mul_of_nonneg_right
          (p4Q2PZ37AHJ_transferSlope_le_halfRational H) hD
  have hF :
      |fCont B - fCont C| ≤ 12 * Dsp B C :=
    p4Q2PZ37AGG_originalCenteredSource_allLinkChordalSlope H B C
  have hFBound : |fCont B| ≤ pH / 2 :=
    p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H B
  have hTBound : |t C| ≤ pH / 2 :=
    p4Q2PZ37AHJ_originalTransfer_abs_le_halfCount H C
  have hPart1 :
      |fCont B| * |t B - t C| ≤
        (pH / 2) * (((13 / 256 : ℝ) * pH) * Dsp B C) := by
    calc
      |fCont B| * |t B - t C| ≤
          (pH / 2) * |t B - t C| :=
        mul_le_mul_of_nonneg_right hFBound (abs_nonneg _)
      _ ≤ (pH / 2) * (((13 / 256 : ℝ) * pH) * Dsp B C) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
  have hPart2 :
      |t C| * |fCont B - fCont C| ≤
        (pH / 2) * (12 * Dsp B C) := by
    calc
      |t C| * |fCont B - fCont C| ≤
          (pH / 2) * |fCont B - fCont C| :=
        mul_le_mul_of_nonneg_right hTBound (abs_nonneg _)
      _ ≤ (pH / 2) * (12 * Dsp B C) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
  calc
    |fCont B * t B - fCont C * t C| ≤
        |fCont B| * |t B - t C| +
          |t C| * |fCont B - fCont C| :=
      p4Q2PZ37AHK_abs_product_difference _ _ _ _
    _ ≤ (pH / 2) * (((13 / 256 : ℝ) * pH) * Dsp B C) +
        (pH / 2) * (12 * Dsp B C) :=
      add_le_add hPart1 hPart2
    _ = p4Q2PZ37AHL_productSlope H * Dsp B C := by
      unfold p4Q2PZ37AHL_productSlope
      ring

/-- The genuine ADL all-coordinate SU(2) box fits into an original
spatial ℓ¹ ball at the explicit per-link radius R/(card(Link)+1).
The +1 ensures STRICT inclusion even with empty Link. -/
theorem p4Q2PZ37AHL_originalSliceBox_subset_spatialBall
    (B : Cfg) (R : ℝ) (hR : 0 < R) :
    p4Q2PZ37ADL_originalSliceFullChordalBox H B
      (R / ((Fintype.card Link : ℝ) + 1)) ⊆
      p4Q2PZ37AHL_originalSpatialBall H B R := by
  let L : ℝ := (Fintype.card Link : ℝ)
  let r : ℝ := R / (L + 1)
  have hDen : 0 < L + 1 := by
    dsimp [L]
    positivity
  have hr : 0 < r := div_pos hR hDen
  have hExact : r * (L + 1) = R := by
    dsimp [r]
    field_simp
  have hStrict : L * r < R := by nlinarith only [hExact, hr]
  intro C hC
  have hLink (e : Link) : dJ (B e) (C e) ≤ r :=
    (hC e (Set.mem_univ e)).le
  have hSum :
      Dsp B C ≤ ∑ _e : Link, r := by
    unfold p4Q2PZ37AGG_originalSpatialChordalDistance
    exact Finset.sum_le_sum (fun e _ => hLink e)
  have hConst : (∑ _e : Link, r) = L * r := by
    dsimp [L]
    simp
  change Dsp B C < R
  exact hSum.trans_lt (hConst ▸ hStrict)

/-- Every positive-radius original spatial chordal ball has an
EXPLICIT lower mass under the SAME original normalized product Haar.
This uses ADZ for each authentic SU(2) link and keeps the exponent at
card(Link_H), rather than the 2*card(Link_H) of pair-Haar geometry. -/
theorem p4Q2PZ37AHL_originalSpatialBall_mass_ge_explicit
    (B : Cfg) (R : ℝ) (hR : 0 < R) :
    kappa (R / ((Fintype.card Link : ℝ) + 1)) ^ Fintype.card Link ≤
      Measure.real muH (p4Q2PZ37AHL_originalSpatialBall H B R) := by
  let r : ℝ := R / ((Fintype.card Link : ℝ) + 1)
  have hr : 0 < r := by
    dsimp [r]
    exact div_pos hR (by positivity)
  have hBox :
      kappa r ^ Fintype.card Link ≤
        Measure.real muH (p4Q2PZ37ADL_originalSliceFullChordalBox H B r) := by
    rw [p4Q2PZ37ADL_sliceBox_originalHaarMass_eq H B r]
    calc
      kappa r ^ Fintype.card Link = ∏ _e : Link, kappa r := by simp
      _ ≤ ∏ e : Link, Measure.real haar
          (p4Q2PZ37ADK_trueChordalBall (B e) r) :=
        Finset.prod_le_prod
          (fun _ _ => le_of_lt (p4Q2PZ37ADQ_sphereRadiusFraction_pos r))
          (fun e _ => p4Q2PZ37ADZ_originalAllCenters_ge_explicit (B e) r hr)
  have hSub :
      p4Q2PZ37ADL_originalSliceFullChordalBox H B r ⊆
        p4Q2PZ37AHL_originalSpatialBall H B R :=
    p4Q2PZ37AHL_originalSliceBox_subset_spatialBall H B R hR
  exact hBox.trans (measureReal_mono hSub)

/-- Actual spatial-slice Haar mass is strictly positive at EVERY
positive radius and every original spatial configuration, with an
explicit SU(2)-sphere radius-only lower certificate. -/
theorem p4Q2PZ37AHL_originalSpatialBall_mass_pos
    (B : Cfg) (R : ℝ) (hR : 0 < R) :
    0 < Measure.real muH (p4Q2PZ37AHL_originalSpatialBall H B R) := by
  have hDen : (0 : ℝ) < (Fintype.card Link : ℝ) + 1 := by positivity
  have hr : 0 < R / ((Fintype.card Link : ℝ) + 1) :=
    div_pos hR hDen
  exact lt_of_lt_of_le
    (pow_pos (p4Q2PZ37ADQ_sphereRadiusFraction_pos _) _)
    (p4Q2PZ37AHL_originalSpatialBall_mass_ge_explicit H B R hR)

/-- A genuine positive action-transfer correlation at B remains above
half its strictly positive amplitude throughout an explicitly defined
original spatial chordal ball. -/
theorem p4Q2PZ37AHL_originalAlignedBall_stable
    (B : Cfg) (hB : 0 < fCont B * t B) :
    ∃ R : ℝ, 0 < R ∧
      ∀ C ∈ p4Q2PZ37AHL_originalSpatialBall H B R,
        fCont B * t B / 2 < fCont C * t C := by
  let L : ℝ := p4Q2PZ37AHL_productSlope H
  have hL : 0 ≤ L := p4Q2PZ37AHL_productSlope_nonneg H
  let R : ℝ := (fCont B * t B / 2) / (L + 1)
  have hDen : 0 < L + 1 := by linarith only [hL]
  have hHalf : 0 < fCont B * t B / 2 := by linarith only [hB]
  have hR : 0 < R := div_pos hHalf hDen
  have hEq : R * (L + 1) = fCont B * t B / 2 := by
    dsimp [R]
    field_simp
  have hScale : L * R < fCont B * t B / 2 := by
    nlinarith only [hEq, hR]
  refine ⟨R, hR, ?_⟩
  intro C hC
  have hLip : |fCont B * t B - fCont C * t C| ≤ L * Dsp B C :=
    p4Q2PZ37AHL_originalProduct_allLinkSlope H B C
  have hSmall : L * Dsp B C < fCont B * t B / 2 :=
    (mul_le_mul_of_nonneg_left (le_of_lt hC) hL).trans_lt hScale
  have hDelta := (abs_le.mp hLip).2
  linarith only [hSmall, hDelta]

/-- UNCONDITIONAL finite-volume positive Haar-mass region of the SAME
original action-transfer sign alignment, with a strictly positive
rational margin and explicit true SU(2) product-Haar radial floor. -/
theorem p4Q2PZ37AHL_exists_rationalAlignedRegion_positiveHaarMass :
    ∃ q : ℚ, 0 < q ∧
      ∃ B : Cfg, ∃ R : ℝ, 0 < R ∧
        (∀ C ∈ p4Q2PZ37AHL_originalSpatialBall H B R,
          (q : ℝ) < fCont C * t C) ∧
        kappa (R / ((Fintype.card Link : ℝ) + 1)) ^ Fintype.card Link ≤
          Measure.real muH (p4Q2PZ37AHL_originalAlignedRegion H q) ∧
        0 < Measure.real muH (p4Q2PZ37AHL_originalAlignedRegion H q) := by
  obtain ⟨B, hB⟩ := p4Q2PZ37AHK_exists_originalActionAlignedBoundary H
  obtain ⟨R, hR, hStable⟩ :=
    p4Q2PZ37AHL_originalAlignedBall_stable H B hB
  have hHalf : (0 : ℝ) < fCont B * t B / 2 := by linarith only [hB]
  obtain ⟨q, hqPos, hqTop⟩ := exists_rat_btwn hHalf
  have hq : 0 < q := by exact_mod_cast hqPos
  have hSub :
      p4Q2PZ37AHL_originalSpatialBall H B R ⊆
        p4Q2PZ37AHL_originalAlignedRegion H q := by
    intro C hC
    have hAmple := hStable C hC
    change (q : ℝ) < fCont C * t C
    exact hqTop.trans hAmple
  have hMass :
      kappa (R / ((Fintype.card Link : ℝ) + 1)) ^ Fintype.card Link ≤
        Measure.real muH (p4Q2PZ37AHL_originalAlignedRegion H q) :=
    (p4Q2PZ37AHL_originalSpatialBall_mass_ge_explicit H B R hR).trans
      (measureReal_mono hSub)
  have hPos :
      0 < Measure.real muH (p4Q2PZ37AHL_originalAlignedRegion H q) :=
    (pow_pos (p4Q2PZ37ADQ_sphereRadiusFraction_pos _) _).trans_le hMass
  refine ⟨q, hq, B, R, hR, ?_, hMass, hPos⟩
  intro C hC
  exact hqTop.trans (hStable C hC)

/-- Positive true-Haar mass of a region where the literal original
Wilson-action deviation and original transfer have the SAME nonzero
sign, not just existence at one boundary. Both sign branches are
retained, neither is independently assumed nonempty. -/
theorem p4Q2PZ37AHL_originalSameSignRegion_positiveHaarMass :
    0 < Measure.real muH
      {C : Cfg | (0 < fCont C ∧ 0 < t C) ∨
        (fCont C < 0 ∧ t C < 0)} := by
  obtain ⟨q, hq, B, R, hR, hStable, hMass, hPos⟩ :=
    p4Q2PZ37AHL_exists_rationalAlignedRegion_positiveHaarMass H
  have hSub :
      p4Q2PZ37AHL_originalAlignedRegion H q ⊆
        {C : Cfg | (0 < fCont C ∧ 0 < t C) ∨
          (fCont C < 0 ∧ t C < 0)} := by
    intro C hC
    have hqReal : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hProd : 0 < fCont C * t C :=
      hqReal.trans hC
    exact (mul_pos_iff.mp hProd)
  exact hPos.trans_le (measureReal_mono hSub)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHL_productSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHL_originalProduct_allLinkSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHL_originalSliceBox_subset_spatialBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHL_originalSpatialBall_mass_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHL_originalSpatialBall_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHL_originalAlignedBall_stable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHL_exists_rationalAlignedRegion_positiveHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHL_originalSameSignRegion_positiveHaarMass
