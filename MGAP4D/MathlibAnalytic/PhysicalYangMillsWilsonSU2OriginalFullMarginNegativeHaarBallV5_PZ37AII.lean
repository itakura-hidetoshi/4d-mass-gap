import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllCouplingNegativeHaarBallV5_PZ37AIH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AII — genuine full-margin original negative Haar ball

AIG proved an actual positive-Haar negative region at the explicit original
finite-volume margin, and AIH proved a general-positive-coupling all-link
Lipschitz slope but propagated only a HALF-margin ball.

The AIG weighted-average inequality is strictly stronger than existence of
a boundary below -epsilon: the negative average is <= -2*epsilon*exp(beta*p_H).
Using the unchanged right halfweight bound gives a physical boundary with
the original transfer < -3*epsilon/2 at EVERY beta>0.

AIH's true original signed transfer slope and original spatial chordal
distance then provide a radius epsilon/(2*(Lambda_H(beta)+1)) > 0 on which
the ORIGINAL transfer is < -epsilon, not merely < -epsilon/2.
AHL's genuine one-slice SU(2) product Haar geometry supplies an explicit,
strictly positive quantitative lower bound for the ORIGINAL AIG full-margin
negative region itself.

This strictly strengthens AIG and AIH without a new sign assumption or
replacement physics. The source, complete slab kernel, both spatial
halfweights, exact Haar measure, Lean/mathlib pins and previous proof
histories are unchanged. No numerical boundary assignment, positive
transfer boundary, both-sign shell, H-uniform coercivity, Hamiltonian gap
or continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AII_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AII_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AII_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AII_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AII_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Avg" => p4Q2PZ37AIF_originalRightWeightedTransferAverage H
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H
local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H
local notation "L" => p4Q2PZ37AIH_transferSlope H
local notation "R" => p4Q2PZ37AIH_originalNegativeBallRadius H
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "Ball" => p4Q2PZ37AHL_originalSpatialBall H
local notation "kappa" => p4Q2PZ37ADQ_sphereRadiusFraction
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AII_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The original negative weighted transfer average forces a STRICTLY
stronger original negative center, below -3*epsilon/2. This uses neither
a positive transfer point nor an extra source or full-support assumption.
The original halfweight cannot exceed exp(beta*p_H). -/
theorem p4Q2PZ37AII_originalTransfer_exists_below_threeHalfMargin
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ B : Cfg, T beta f0 B < -(3 * margin beta / 2) := by
  have hMargin : 0 < margin beta :=
    p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta
  have hM : 0 < Real.exp (beta * pH) := Real.exp_pos _
  have hProduct : 0 < margin beta * Real.exp (beta * pH) :=
    mul_pos hMargin hM
  have hBudget :
      Avg beta ≤ -(2 * (margin beta * Real.exp (beta * pH))) := by
    have hOld :=
      p4Q2PZ37AIG_originalRightWeightedTransferAverage_le_negativeVariance
        H beta hbeta.le
    have hScale :=
      p4Q2PZ37AIG_originalNegativeTransferMargin_weightIdentity H beta
    linarith only [hOld, hScale]
  by_contra hNo
  have hPoint (B : Cfg) :
      -(3 * margin beta / 2) ≤ T beta f0 B :=
    le_of_not_gt (fun hB => hNo ⟨B, hB⟩)
  have hPointwise : ∀ᵐ B : Cfg ∂muH,
      -(3 * (margin beta * Real.exp (beta * pH)) / 2) ≤
        Real.exp ((beta / 2) * W B) * T beta f0 B := by
    filter_upwards with B
    have hWeight :=
      p4Q2PZ37AIG_originalRightWeight_le_expCount H beta hbeta.le B
    have hNeg : -(3 * margin beta / 2) ≤ 0 := by
      linarith only [hMargin]
    calc
      -(3 * (margin beta * Real.exp (beta * pH)) / 2) =
          (-(3 * margin beta / 2)) * Real.exp (beta * pH) := by ring
      _ ≤ (-(3 * margin beta / 2)) * Real.exp ((beta / 2) * W B) :=
        mul_le_mul_of_nonpos_left hWeight hNeg
      _ = Real.exp ((beta / 2) * W B) * (-(3 * margin beta / 2)) := by ring
      _ ≤ Real.exp ((beta / 2) * W B) * T beta f0 B :=
        mul_le_mul_of_nonneg_left (hPoint B) (Real.exp_pos _).le
  have hLower :
      -(3 * (margin beta * Real.exp (beta * pH)) / 2) ≤ Avg beta := by
    change -(3 * (margin beta * Real.exp (beta * pH)) / 2) ≤
      ∫ B : Cfg, Real.exp ((beta / 2) * W B) * T beta f0 B ∂muH
    simpa only [integral_const, probReal_univ, one_smul] using
      (integral_mono_ae
        (integrable_const (μ := muH)
          (-(3 * (margin beta * Real.exp (beta * pH)) / 2)))
        (p4Q2PZ37AIF_originalRightWeightedTransfer_integrable H beta)
        hPointwise)
  linarith only [hLower, hBudget, hProduct]

/-- An actual center below -3*epsilon/2 preserves the FULL -epsilon
threshold on the original AIH-radius ball, for any beta >= 0.
The stronger threshold is essential: AIH's earlier center only gives
the half-margin statement. -/
theorem p4Q2PZ37AII_originalFullNegativeBall_stable
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (B : Cfg) (hB : T beta f0 B < -(3 * epsilon / 2)) :
    ∀ C ∈ Ball B (R beta epsilon), T beta f0 C < -epsilon := by
  have hL : 0 ≤ L beta :=
    p4Q2PZ37AIH_transferSlope_nonneg H beta hbeta
  have hDen : 0 < 2 * (L beta + 1) := by positivity
  have hR : 0 < R beta epsilon :=
    p4Q2PZ37AIH_originalNegativeBallRadius_pos H beta hbeta epsilon hepsilon
  have hEq : R beta epsilon * (2 * (L beta + 1)) = epsilon := by
    unfold p4Q2PZ37AIH_originalNegativeBallRadius
    exact div_mul_cancel₀ epsilon hDen.ne'
  have hScale : L beta * R beta epsilon < epsilon / 2 := by
    nlinarith only [hEq, hR]
  intro C hC
  change Dsp B C < R beta epsilon at hC
  have hLip : |T beta f0 B - T beta f0 C| ≤ L beta * Dsp B C :=
    p4Q2PZ37AIH_originalTransfer_allLinkSlope H beta hbeta B C
  have hSmall : L beta * Dsp B C < epsilon / 2 :=
    (mul_le_mul_of_nonneg_left hC.le hL).trans_lt hScale
  have hDelta : -(L beta * Dsp B C) ≤ T beta f0 B - T beta f0 C :=
    (abs_le.mp hLip).1
  linarith only [hB, hSmall, hDelta]

/-- An original negative center below -3*epsilon/2 gives the true AHL
geometric Haar floor for the FULL -epsilon sublevel, not just a
half-margin region. All inequalities use the same spatial Haar. -/
theorem p4Q2PZ37AII_originalFullNegativeRegion_mass_of_center
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (B : Cfg) (hB : T beta f0 B < -(3 * epsilon / 2)) :
    kappa (R beta epsilon / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH {C : Cfg | T beta f0 C < -epsilon} ∧
      0 < Measure.real muH {C : Cfg | T beta f0 C < -epsilon} := by
  have hSub :
      Ball B (R beta epsilon) ⊆ {C : Cfg | T beta f0 C < -epsilon} := by
    intro C hC
    exact p4Q2PZ37AII_originalFullNegativeBall_stable
      H beta hbeta epsilon hepsilon B hB C hC
  have hMono :
      Measure.real muH (Ball B (R beta epsilon)) ≤
        Measure.real muH {C : Cfg | T beta f0 C < -epsilon} :=
    measureReal_mono hSub
  exact ⟨
    (p4Q2PZ37AIH_originalNegativeBall_mass_ge_explicit
      H beta hbeta epsilon hepsilon B).trans hMono,
    (p4Q2PZ37AIH_originalNegativeBall_mass_pos
      H beta hbeta epsilon hepsilon B).trans_le hMono⟩

/-- Unconditional ALL-positive-coupling original FULL-margin ball:
a true boundary lies below -3epsilon/2, the true complete-kernel
transfer remains below -epsilon on its AIH radius, and the authentic
SU(2) spatial product-Haar floor bounds both ball and AIG region. -/
theorem p4Q2PZ37AII_originalTransfer_exists_fullNegativeHaarBall
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ B : Cfg,
      T beta f0 B < -(3 * margin beta / 2) ∧
      0 < R beta (margin beta) ∧
      (∀ C ∈ Ball B (R beta (margin beta)),
        T beta f0 C < -(margin beta)) ∧
      0 < kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ∧
      kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH (Ball B (R beta (margin beta))) ∧
      kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH (Region beta) := by
  have hMargin :=
    p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta
  obtain ⟨B, hB⟩ :=
    p4Q2PZ37AII_originalTransfer_exists_below_threeHalfMargin H beta hbeta
  have hFloor :
      0 < kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link :=
    pow_pos (p4Q2PZ37ADQ_sphereRadiusFraction_pos _) _
  have hReg :=
    (p4Q2PZ37AII_originalFullNegativeRegion_mass_of_center
      H beta hbeta.le (margin beta) hMargin B hB).1
  change
    kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
      Measure.real muH (Region beta) at hReg
  exact ⟨B, hB,
    p4Q2PZ37AIH_originalNegativeBallRadius_pos
      H beta hbeta.le (margin beta) hMargin,
    p4Q2PZ37AII_originalFullNegativeBall_stable
      H beta hbeta.le (margin beta) hMargin B hB,
    hFloor,
    p4Q2PZ37AIH_originalNegativeBall_mass_ge_explicit
      H beta hbeta.le (margin beta) hMargin B,
    hReg⟩

/-- The explicit, strictly positive radius-only floor applies to AIG's
original FULL-margin negative region for every beta > 0. This is
stronger than AIG's qualitative positive mass and AIH's quantitative
HALF-margin region; no H-independent constant is inferred. -/
theorem p4Q2PZ37AII_originalFullNegativeRegion_mass_ge_explicit
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ∧
      kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH (Region beta) := by
  obtain ⟨B, _hCenter, _hR, _hStable, hFloor, _hBall, hRegion⟩ :=
    p4Q2PZ37AII_originalTransfer_exists_fullNegativeHaarBall H beta hbeta
  exact ⟨hFloor, hRegion⟩

/-- At the unchanged original fixed coupling, the AII full-margin floor
uses exactly the existing AIG radius. No change to beta0 or the
right-boundary source is made. -/
theorem p4Q2PZ37AII_originalFixedFullNegativeRegion_mass_ge_explicit :
    0 < kappa
      (p4Q2PZ37AIG_originalFixedNegativeBallRadius H (margin beta0) /
        ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ∧
      kappa
        (p4Q2PZ37AIG_originalFixedNegativeBallRadius H (margin beta0) /
          ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH (Region beta0) := by
  simpa only [p4Q2PZ37AIH_originalNegativeBallRadius_fixedCoupling] using
    (p4Q2PZ37AII_originalFullNegativeRegion_mass_ge_explicit
      H beta0 p4Q2PZ37ADC_fixedCoupling_pos)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AII_originalTransfer_exists_below_threeHalfMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AII_originalFullNegativeBall_stable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AII_originalFullNegativeRegion_mass_of_center
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AII_originalTransfer_exists_fullNegativeHaarBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AII_originalFullNegativeRegion_mass_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AII_originalFixedFullNegativeRegion_mass_ge_explicit
