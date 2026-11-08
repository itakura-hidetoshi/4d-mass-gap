import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullMarginNegativeHaarBallV5_PZ37AII
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIJ — primitive-quantity original negative Haar floor

Keep the unchanged complete Wilson kernel, both spatial halfweights, ZW
signed physical L2 source, its proved continuous representative and the
original normalized spatial product Haar measure.

For every beta >= 0, the actual one-link energy bound E <= 2 gives
exp(-2*beta) <= Z1(beta). AIF's exact product identity gives
exp(-2*beta*n_H) <= Zcross_H(beta), where n_H is Nat.card of the
ORIGINAL spatial link carrier. AHN supplies the genuine variance floor
v_H = (3*p_H/8)^2 * kappa(1/96)^n_H > 0.

For beta > 0 define
  delta_H(beta) = beta * exp(-2*beta*(n_H+p_H)) * v_H / 2,
  r_H(beta) = delta_H(beta) / (13*beta*p_H+2).
Prove delta <= the original AIG margin and r <= the original AIH radius.
The AII full-margin negative center therefore has a genuine original
spatial ball of this new radius contained in the SAME AIG full-margin
negative region. AHL supplies its explicit positive product-Haar floor.

The new radius and floor no longer contain Zcross, the source variance or
source L1 integrals. The pre-existing kappa is an exact geometric bound,
not a numerically evaluated constant. All H-dependence is retained.
Old stronger certificates are kept and can be combined by taking a max;
no monotonicity of kappa, evaluated boundary, positive transfer boundary,
both-sign shell, uniform coercivity or spectral/continuum gap is assumed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIJ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIJ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIJ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIJ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIJ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "nu" => normalizedCompactHaar G

/-- Integrate the actual one-link Wilson bound, not a replacement kernel. -/
theorem p4Q2PZ37AIJ_originalSingleLinkPartition_ge_exp
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(2 * beta)) ≤ p4Q2PZ37AIF_originalSingleLinkPartition beta := by
  have hPoint (g : G) :
      Real.exp (-(2 * beta)) ≤
        Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 g) := by
    apply Real.exp_le_exp.mpr
    have hEnergy := specialUnitaryWilsonPlaquetteEnergy_le_two
      (by norm_num : 0 < (2 : ℕ)) g
    have hMul := mul_le_mul_of_nonneg_left hEnergy hbeta
    nlinarith only [hMul]
  have hInt := integral_mono
    (integrable_const (μ := nu) (Real.exp (-(2 * beta))))
    (p4Q2PZ37AIF_originalSingleLinkPartition_integrable beta) hPoint
  simpa only [integral_const, probReal_univ, one_smul,
    p4Q2PZ37AIF_originalSingleLinkPartition] using hInt

/-- Exact finite-power exponential identity, including the empty product. -/
theorem p4Q2PZ37AIJ_expPower_eq (beta : ℝ) (n : ℕ) :
    Real.exp (-(2 * beta)) ^ n = Real.exp (-(2 * beta * (n : ℝ))) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "nH" => Nat.card Link
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H
local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H
local notation "L" => p4Q2PZ37AIH_transferSlope H
local notation "R" => p4Q2PZ37AIH_originalNegativeBallRadius H
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "Ball" => p4Q2PZ37AHL_originalSpatialBall H
local notation "kappa" => p4Q2PZ37ADQ_sphereRadiusFraction

local instance p4Q2PZ37AIJ_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Genuine crossing Haar partition bounded below using original link count.
Nat.card keeps the finite presentation independent of the Fintype witness. -/
theorem p4Q2PZ37AIJ_originalCrossingPartition_ge_expCount
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(2 * beta * (nH : ℝ))) ≤ Zcross beta := by
  have hPow := pow_le_pow_left₀ (Real.exp_pos (-(2 * beta))).le
    (p4Q2PZ37AIJ_originalSingleLinkPartition_ge_exp beta hbeta) nH
  rw [p4Q2PZ37AIJ_expPower_eq] at hPow
  simpa only [p4Q2PZ37AIF_originalCrossingPartition,
    Fintype.card_eq_nat_card] using hPow

/-- AHN's identity-box variance bound, expressed without a source integral. -/
def p4Q2PZ37AIJ_sourceVarianceFloor : ℝ :=
  (3 * pH / 8) ^ 2 * kappa (1 / 96) ^ nH

local notation "vFloor" => p4Q2PZ37AIJ_sourceVarianceFloor H

theorem p4Q2PZ37AIJ_sourceVarianceFloor_pos : 0 < vFloor := by
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  unfold p4Q2PZ37AIJ_sourceVarianceFloor
  exact mul_pos (by positivity)
    (pow_pos (p4Q2PZ37ADQ_sphereRadiusFraction_pos _) _)

theorem p4Q2PZ37AIJ_sourceVarianceFloor_le_original : vFloor ≤ Vsrc := by
  simpa only [p4Q2PZ37AIJ_sourceVarianceFloor, Fintype.card_eq_nat_card] using
    p4Q2PZ37AHN_originalSource_HaarSecondMoment_explicitFloor H

/-- Explicit positive-coupling margin using beta, original counts and kappa.
The actual AIG margin is retained separately and remains at least this large. -/
def p4Q2PZ37AIJ_primitiveNegativeMargin (beta : ℝ) : ℝ :=
  beta * Real.exp (-(2 * beta * ((nH : ℝ) + pH))) * vFloor / 2

local notation "delta" => p4Q2PZ37AIJ_primitiveNegativeMargin H

theorem p4Q2PZ37AIJ_primitiveNegativeMargin_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < delta beta := by
  unfold p4Q2PZ37AIJ_primitiveNegativeMargin
  exact div_pos
    (mul_pos (mul_pos hbeta (Real.exp_pos _))
      (p4Q2PZ37AIJ_sourceVarianceFloor_pos H)) (by norm_num)

theorem p4Q2PZ37AIJ_primitiveNegativeMargin_zero : delta 0 = 0 := by
  simp only [p4Q2PZ37AIJ_primitiveNegativeMargin, zero_mul, zero_div]

/-- Combine two PROVED lower bounds, retaining the same original margin.
This is valid for beta >= 0; strict negativity is used only for beta > 0. -/
theorem p4Q2PZ37AIJ_primitiveNegativeMargin_le_original
    (beta : ℝ) (hbeta : 0 ≤ beta) : delta beta ≤ margin beta := by
  have hZ := p4Q2PZ37AIJ_originalCrossingPartition_ge_expCount H beta hbeta
  have hV := p4Q2PZ37AIJ_sourceVarianceFloor_le_original H
  have hV0 := (p4Q2PZ37AIJ_sourceVarianceFloor_pos H).le
  have hExp :
      Real.exp (-(2 * beta * ((nH : ℝ) + pH))) =
        Real.exp (-(2 * beta * (nH : ℝ))) * Real.exp (-(2 * beta * pH)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hCoeff :
      beta * Real.exp (-(2 * beta * (nH : ℝ))) * Real.exp (-(2 * beta * pH)) ≤
        beta * Zcross beta * Real.exp (-(2 * beta * pH)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZ hbeta)
      (Real.exp_pos _).le
  have hCoeff0 : 0 ≤ beta * Zcross beta * Real.exp (-(2 * beta * pH)) :=
    mul_nonneg
      (mul_nonneg hbeta (p4Q2PZ37AIF_originalCrossingPartition_pos H beta).le)
      (Real.exp_pos _).le
  calc
    delta beta =
        (beta * Real.exp (-(2 * beta * (nH : ℝ))) *
          Real.exp (-(2 * beta * pH))) * vFloor / 2 := by
      unfold p4Q2PZ37AIJ_primitiveNegativeMargin
      rw [hExp]
      ring
    _ ≤ (beta * Zcross beta * Real.exp (-(2 * beta * pH))) * Vsrc / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul hCoeff hV hV0 hCoeff0) (by norm_num)
    _ = margin beta := rfl

/-- Radius free of the original Zcross, variance and L1 integrals.
The denominator is exactly 2 times the count-based slope cap plus 2. -/
def p4Q2PZ37AIJ_primitiveNegativeBallRadius (beta : ℝ) : ℝ :=
  delta beta / (13 * beta * pH + 2)

local notation "r" => p4Q2PZ37AIJ_primitiveNegativeBallRadius H

theorem p4Q2PZ37AIJ_primitiveNegativeBallRadius_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < r beta := by
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  unfold p4Q2PZ37AIJ_primitiveNegativeBallRadius
  exact div_pos (p4Q2PZ37AIJ_primitiveNegativeMargin_pos H beta hbeta) (by positivity)

/-- Both inequalities have the correct orientations: a smaller margin and
larger denominator yield a smaller radius. No claim about kappa monotonicity. -/
theorem p4Q2PZ37AIJ_primitiveNegativeBallRadius_le_original
    (beta : ℝ) (hbeta : 0 < beta) : r beta ≤ R beta (margin beta) := by
  have hNum := p4Q2PZ37AIJ_primitiveNegativeMargin_le_original H beta hbeta.le
  have hMargin := p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta
  have hL := p4Q2PZ37AIH_transferSlope_nonneg H beta hbeta.le
  have hSlope := p4Q2PZ37AIH_transferSlope_le_halfCount H beta hbeta.le
  have hDen : 0 < 2 * (L beta + 1) := by positivity
  have hDenLe : 2 * (L beta + 1) ≤ 13 * beta * pH + 2 := by
    nlinarith only [hSlope]
  have hLargeDen : 0 < 13 * beta * pH + 2 := hDen.trans_le hDenLe
  change delta beta / (13 * beta * pH + 2) ≤
    margin beta / (2 * (L beta + 1))
  apply (div_le_div_iff₀ hLargeDen hDen).mpr
  calc
    delta beta * (2 * (L beta + 1)) ≤ margin beta * (2 * (L beta + 1)) :=
      mul_le_mul_of_nonneg_right hNum hDen.le
    _ ≤ margin beta * (13 * beta * pH + 2) :=
      mul_le_mul_of_nonneg_left hDenLe hMargin.le

/-- Original spatial balls are compared by their original scalar radius. -/
theorem p4Q2PZ37AIJ_primitiveNegativeBall_subset_original
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) :
    Ball B (r beta) ⊆ Ball B (R beta (margin beta)) := by
  intro C hC
  change Dsp B C < r beta at hC
  change Dsp B C < R beta (margin beta)
  exact hC.trans_le (p4Q2PZ37AIJ_primitiveNegativeBallRadius_le_original H beta hbeta)

/-- The smaller primitive-radius ball preserves the ORIGINAL full margin. -/
theorem p4Q2PZ37AIJ_primitiveNegativeBall_fullMargin_stable
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg)
    (hB : T beta f0 B < -(3 * margin beta / 2)) :
    ∀ C ∈ Ball B (r beta), T beta f0 C < -(margin beta) := by
  intro C hC
  exact p4Q2PZ37AII_originalFullNegativeBall_stable
    H beta hbeta.le (margin beta)
    (p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta) B hB C
    (p4Q2PZ37AIJ_primitiveNegativeBall_subset_original H beta hbeta B hC)

/-- Apply AHL directly at the new positive radius in the SAME original Haar.
No transfer of a lower bound through an unproved kappa monotonicity. -/
theorem p4Q2PZ37AIJ_primitiveNegativeBall_mass_ge_explicit
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) :
    kappa (r beta / ((nH : ℝ) + 1)) ^ nH ≤
      Measure.real muH (Ball B (r beta)) := by
  simpa only [Fintype.card_eq_nat_card] using
    (p4Q2PZ37AHL_originalSpatialBall_mass_ge_explicit H B (r beta)
      (p4Q2PZ37AIJ_primitiveNegativeBallRadius_pos H beta hbeta))

/-- Actual original full-margin negative center and a ball whose radius
and geometric mass floor contain no unevaluated original source integrals. -/
theorem p4Q2PZ37AIJ_originalTransfer_exists_primitiveNegativeHaarBall
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ B : Cfg,
      T beta f0 B < -(3 * margin beta / 2) ∧
      0 < r beta ∧
      (∀ C ∈ Ball B (r beta), T beta f0 C < -(margin beta)) ∧
      0 < kappa (r beta / ((nH : ℝ) + 1)) ^ nH ∧
      kappa (r beta / ((nH : ℝ) + 1)) ^ nH ≤
        Measure.real muH (Ball B (r beta)) := by
  obtain ⟨B, hB⟩ :=
    p4Q2PZ37AII_originalTransfer_exists_below_threeHalfMargin H beta hbeta
  exact ⟨B, hB,
    p4Q2PZ37AIJ_primitiveNegativeBallRadius_pos H beta hbeta,
    p4Q2PZ37AIJ_primitiveNegativeBall_fullMargin_stable H beta hbeta B hB,
    pow_pos (p4Q2PZ37ADQ_sphereRadiusFraction_pos _) _,
    p4Q2PZ37AIJ_primitiveNegativeBall_mass_ge_explicit H beta hbeta B⟩

/-- Primitive-quantity quantitative Haar floor for the unchanged AIG
FULL-margin negative region, at EVERY positive beta and every finite H. -/
theorem p4Q2PZ37AIJ_originalFullNegativeRegion_primitiveMass
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < kappa (r beta / ((nH : ℝ) + 1)) ^ nH ∧
      kappa (r beta / ((nH : ℝ) + 1)) ^ nH ≤ Measure.real muH (Region beta) := by
  obtain ⟨B, _hB, _hR, hStable, hPos, hMass⟩ :=
    p4Q2PZ37AIJ_originalTransfer_exists_primitiveNegativeHaarBall H beta hbeta
  have hSub : Ball B (r beta) ⊆ Region beta := by
    intro C hC
    exact hStable C hC
  exact ⟨hPos, hMass.trans (measureReal_mono hSub)⟩

/-- A completely primitive negative threshold also contains the original
full-margin region. It is a larger set, not a redefinition of AIG's region. -/
theorem p4Q2PZ37AIJ_primitiveNegativeRegion_mass
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < kappa (r beta / ((nH : ℝ) + 1)) ^ nH ∧
      kappa (r beta / ((nH : ℝ) + 1)) ^ nH ≤
        Measure.real muH {C : Cfg | T beta f0 C < -(delta beta)} := by
  have hMass := p4Q2PZ37AIJ_originalFullNegativeRegion_primitiveMass H beta hbeta
  have hDelta := p4Q2PZ37AIJ_primitiveNegativeMargin_le_original H beta hbeta.le
  have hSub : Region beta ⊆ {C : Cfg | T beta f0 C < -(delta beta)} := by
    intro C hC
    change T beta f0 C < -(margin beta) at hC
    exact hC.trans_le (neg_le_neg hDelta)
  exact ⟨hMass.1, hMass.2.trans (measureReal_mono hSub)⟩

/-- Retain both certified bounds: their max is still a lower bound.
This neither replaces AII nor assumes an ordering of the kappa values. -/
theorem p4Q2PZ37AIJ_originalFullNegativeRegion_combinedMass
    (beta : ℝ) (hbeta : 0 < beta) :
    max (kappa (r beta / ((nH : ℝ) + 1)) ^ nH)
      (kappa (R beta (margin beta) / ((nH : ℝ) + 1)) ^ nH) ≤
        Measure.real muH (Region beta) := by
  exact max_le
    (p4Q2PZ37AIJ_originalFullNegativeRegion_primitiveMass H beta hbeta).2
    (p4Q2PZ37AII_originalFullNegativeRegion_mass_ge_explicit H beta hbeta).2

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_originalSingleLinkPartition_ge_exp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_expPower_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_originalCrossingPartition_ge_expCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_sourceVarianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_sourceVarianceFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_sourceVarianceFloor_le_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeMargin_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeMargin_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeMargin_le_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeBallRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeBallRadius_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeBallRadius_le_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeBall_subset_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeBall_fullMargin_stable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeBall_mass_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_originalTransfer_exists_primitiveNegativeHaarBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_originalFullNegativeRegion_primitiveMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_primitiveNegativeRegion_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIJ_originalFullNegativeRegion_combinedMass
