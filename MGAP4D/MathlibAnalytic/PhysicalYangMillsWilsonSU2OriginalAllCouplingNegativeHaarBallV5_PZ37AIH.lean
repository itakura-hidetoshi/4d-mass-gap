import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNegativeTransferHaarRegionV5_PZ37AIG
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIH — all-positive-coupling original negative Haar balls

Keep the original complete SU(2) Wilson one-slab action and kernel, both
spatial halfweights, the ZW signed physical L2 source, its proved continuous
representative, and the same original spatial product Haar measure.

For every beta >= 0 the actual right one-link action variation is at most
13*d_J. The already proved nonnegative-action Boltzmann estimate therefore
gives the ORIGINAL kernel coefficient 13*beta. Finite-coordinate telescoping
and signed Haar integration give the genuine source-dependent coefficient

  Lambda_H(beta) = (13*beta) * integral |f0_H| dmu_H
                <= (13*beta) * p_H/2.

No new regularity, small-coupling or nonzero-transfer premise is assumed.
At the unchanged fixed coupling this coefficient is exactly the AHH slope.

For every beta > 0 use AIG's actual negative center and explicit positive
margin epsilon_H(beta). The radius epsilon/[2*(Lambda+1)] is positive and
the same physical transfer remains below -epsilon/2 throughout that ball.
AHL yields the genuine Haar floor kappa(R/(Nat.card Link_H+1))^Nat.card Link_H.
The full-margin AIG region and this certified half-margin region are distinct.

The source mass, margin, radius and Haar floor depend on H. No evaluated
boundary assignment, positive transfer boundary, both-sign shell, volume-
uniform coercivity, Hamiltonian spectral gap or continuum mass gap follows.
Existing files, physical definitions, assumptions, histories, canonical root,
Lean/mathlib pins and workflow settings remain unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIH_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIH_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIH_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIH_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIH_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AIH_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AIH_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance
/-- The original complete action has right one-link slope 13: the crossing
term contributes one, the right spatial half-action contributes 24/2,
and the unchanged left half-action cancels exactly. -/
theorem p4Q2PZ37AIH_originalOneSlabAction_rightOneLinkChordSlope
    (A B : Cfg) (e : Link) (g h : G) :
    |S A (Function.update B e g) - S A (Function.update B e h)| ≤
      13 * dJ g h := by
  have hCross :
      |Cross A (Function.update B e g) - Cross A (Function.update B e h)| ≤
        dJ g h := by
    simpa only [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]
      using p4Q2PZ37AEM_originalTemporalCrossing_oneLinkChordLipschitz H A B e g h
  have hSpatial :
      |W (Function.update B e g) - W (Function.update B e h)| ≤
        24 * dJ g h := by
    simpa only [periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]
      using p4Q2PZ37AEM_originalSpatialAction_oneLinkChordLipschitz H B e g h
  have hEq :
      S A (Function.update B e g) - S A (Function.update B e h) =
        (Cross A (Function.update B e g) - Cross A (Function.update B e h)) +
          (1 / 2 : ℝ) *
            (W (Function.update B e g) - W (Function.update B e h)) := by
    unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    ring
  rw [hEq]
  calc
    _ ≤ |Cross A (Function.update B e g) - Cross A (Function.update B e h)| +
        |(1 / 2 : ℝ) *
          (W (Function.update B e g) - W (Function.update B e h))| :=
      abs_add_le _ _
    _ = |Cross A (Function.update B e g) - Cross A (Function.update B e h)| +
        (1 / 2 : ℝ) *
          |W (Function.update B e g) - W (Function.update B e h)| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ dJ g h + (1 / 2 : ℝ) * (24 * dJ g h) :=
      add_le_add hCross (mul_le_mul_of_nonneg_left hSpatial (by norm_num))
    _ = 13 * dJ g h := by ring

/-- General nonnegative coupling, proved from the unchanged complete kernel.
No small-beta premise and no exponential amplification factor are needed,
because both true Wilson actions are nonnegative. -/
theorem p4Q2PZ37AIH_originalKernel_rightOneLinkChordSlope
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : Cfg) (e : Link) (g h : G) :
    |K beta A (Function.update B e g) - K beta A (Function.update B e h)| ≤
      (13 * beta) * dJ g h := by
  have hAg : 0 ≤ S A (Function.update B e g) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A (Function.update B e g)
  have hAh : 0 ≤ S A (Function.update B e h) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A (Function.update B e h)
  have hAction :=
    p4Q2PZ37AIH_originalOneSlabAction_rightOneLinkChordSlope H A B e g h
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  calc
    _ ≤ beta * |S A (Function.update B e g) - S A (Function.update B e h)| :=
      p4Q2PZ37AEM_real_nonnegativeWilsonBoltzmannLipschitz beta _ _ hbeta hAg hAh
    _ ≤ beta * (13 * dJ g h) := mul_le_mul_of_nonneg_left hAction hbeta
    _ = (13 * beta) * dJ g h := by ring
/-- All original right boundary links, at every nonnegative coupling.
The left integration configuration is retained as an arbitrary original A. -/
theorem p4Q2PZ37AIH_originalKernel_rightAllLinkChordSlope
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B C : Cfg) :
    |K beta A B - K beta A C| ≤ (13 * beta) * Dsp B C := by
  exact p4Q2PZ37AGG_finiteCoordinate_absLipschitz
    dJ p4Q2PZ37ADK_trueChordalDistance_symm (13 * beta)
    (fun D : Cfg => K beta A D)
    (fun u i g h =>
      p4Q2PZ37AIH_originalKernel_rightOneLinkChordSlope H beta hbeta A u i g h)
    B C

/-- The genuine original source Haar L1 mass fixes the transfer coefficient.
This definition extends AHH without replacing its fixed-coupling value. -/
def p4Q2PZ37AIH_transferSlope (beta : ℝ) : ℝ :=
  (13 * beta) * Msrc

local notation "L" => p4Q2PZ37AIH_transferSlope H

theorem p4Q2PZ37AIH_transferSlope_nonneg
    (beta : ℝ) (hbeta : 0 ≤ beta) : 0 ≤ L beta := by
  unfold p4Q2PZ37AIH_transferSlope
  exact mul_nonneg (mul_nonneg (by norm_num) hbeta)
    (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)

/-- A purely original plaquette-count cap, using AHJ's genuine Haar bound. -/
theorem p4Q2PZ37AIH_transferSlope_le_halfCount
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    L beta ≤ (13 * beta) * (pH / 2) := by
  exact mul_le_mul_of_nonneg_left
    (p4Q2PZ37AHJ_originalCenteredSource_L1_le_halfCount H)
    (mul_nonneg (by norm_num) hbeta)

theorem p4Q2PZ37AIH_transferSlope_zero : L 0 = 0 := by
  simp only [p4Q2PZ37AIH_transferSlope, mul_zero, zero_mul]

/-- Exact recovery of the existing original fixed-coupling coefficient. -/
theorem p4Q2PZ37AIH_transferSlope_fixedCoupling :
    L beta0 = p4Q2PZ37AHH_transferSlope H := rfl

/-- The SAME physical transfer obeys the all-link bound for every beta >= 0.
AHP transports the physical L2 integral to its proved continuous source;
AEV integrates the signed difference, and AHN restores the true L1 scalar. -/
theorem p4Q2PZ37AIH_originalTransfer_allLinkSlope
    (beta : ℝ) (hbeta : 0 ≤ beta) (B C : Cfg) :
    |T beta f0 B - T beta f0 C| ≤ L beta * Dsp B C := by
  have hVar := p4Q2PZ37AEV_real_signedWeightedIntegral_absVariation
    muH (fun A : Cfg => fCont A)
    (fun A : Cfg => K beta A B) (fun A : Cfg => K beta A C)
    ((13 * beta) * Dsp B C)
    (p4Q2PZ37AHP_originalContinuousSource_integrable H)
    (p4Q2PZ37AHP_originalKernelWeightedSource_integrable H beta B)
    (p4Q2PZ37AHP_originalKernelWeightedSource_integrable H beta C)
    (fun A => p4Q2PZ37AIH_originalKernel_rightAllLinkChordSlope H beta hbeta A B C)
  calc
    |T beta f0 B - T beta f0 C| =
        |(∫ A : Cfg, fCont A * K beta A B ∂muH) -
          (∫ A : Cfg, fCont A * K beta A C ∂muH)| := by
      rw [p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta B,
        p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta C]
    _ ≤ ((13 * beta) * Dsp B C) * (∫ A : Cfg, |fCont A| ∂muH) := hVar
    _ = L beta * Dsp B C := by
      rw [← p4Q2PZ37AHN_originalSource_L1_eq_continuousIntegral H]
      unfold p4Q2PZ37AIH_transferSlope
      ring

/-- Optional original-count envelope; the stronger true L1 estimate remains. -/
theorem p4Q2PZ37AIH_originalTransfer_allLinkHalfCountSlope
    (beta : ℝ) (hbeta : 0 ≤ beta) (B C : Cfg) :
    |T beta f0 B - T beta f0 C| ≤
      ((13 * beta) * (pH / 2)) * Dsp B C := by
  exact (p4Q2PZ37AIH_originalTransfer_allLinkSlope H beta hbeta B C).trans
    (mul_le_mul_of_nonneg_right
      (p4Q2PZ37AIH_transferSlope_le_halfCount H beta hbeta)
      (p4Q2PZ37AGG_originalSpatialChordalDistance_nonneg H B C))
local notation "Ball" => p4Q2PZ37AHL_originalSpatialBall H
local notation "kappa" => p4Q2PZ37ADQ_sphereRadiusFraction
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H

/-- General-coupling radius using the actual source-dependent slope. -/
def p4Q2PZ37AIH_originalNegativeBallRadius (beta epsilon : ℝ) : ℝ :=
  epsilon / (2 * (L beta + 1))

local notation "R" => p4Q2PZ37AIH_originalNegativeBallRadius H

theorem p4Q2PZ37AIH_originalNegativeBallRadius_pos
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    0 < R beta epsilon := by
  unfold p4Q2PZ37AIH_originalNegativeBallRadius
  have hL : 0 ≤ L beta := p4Q2PZ37AIH_transferSlope_nonneg H beta hbeta
  exact div_pos hepsilon (by positivity)

/-- The new radius recovers AIG's original fixed-coupling radius exactly. -/
theorem p4Q2PZ37AIH_originalNegativeBallRadius_fixedCoupling
    (epsilon : ℝ) :
    R beta0 epsilon = p4Q2PZ37AIG_originalFixedNegativeBallRadius H epsilon := rfl

/-- Stability at HALF the supplied margin on the original all-link ball. -/
theorem p4Q2PZ37AIH_originalNegativeBall_stable
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (B : Cfg) (hB : T beta f0 B < -epsilon) :
    ∀ C ∈ Ball B (R beta epsilon), T beta f0 C < -(epsilon / 2) := by
  have hL : 0 ≤ L beta := p4Q2PZ37AIH_transferSlope_nonneg H beta hbeta
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

/-- The genuine original product-Haar lower bound, with Nat.card removing
the presentation-dependent Fintype argument of the existing AHL theorem. -/
theorem p4Q2PZ37AIH_originalNegativeBall_mass_ge_explicit
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (B : Cfg) :
    kappa (R beta epsilon / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
      Measure.real muH (Ball B (R beta epsilon)) := by
  simpa only [Fintype.card_eq_nat_card] using
    (p4Q2PZ37AHL_originalSpatialBall_mass_ge_explicit H B (R beta epsilon)
      (p4Q2PZ37AIH_originalNegativeBallRadius_pos H beta hbeta epsilon hepsilon))

theorem p4Q2PZ37AIH_originalNegativeBall_mass_pos
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (B : Cfg) :
    0 < Measure.real muH (Ball B (R beta epsilon)) :=
  p4Q2PZ37AHL_originalSpatialBall_mass_pos H B (R beta epsilon)
    (p4Q2PZ37AIH_originalNegativeBallRadius_pos H beta hbeta epsilon hepsilon)

/-- The explicit Haar floor passes to the HALF-margin negative region.
No inclusion of the whole ball into AIG's FULL-margin region is asserted. -/
theorem p4Q2PZ37AIH_originalHalfNegativeRegion_mass_of_center
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (B : Cfg) (hB : T beta f0 B < -epsilon) :
    kappa (R beta epsilon / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH {C : Cfg | T beta f0 C < -(epsilon / 2)} ∧
      0 < Measure.real muH {C : Cfg | T beta f0 C < -(epsilon / 2)} := by
  have hSub :
      Ball B (R beta epsilon) ⊆ {C : Cfg | T beta f0 C < -(epsilon / 2)} := by
    intro C hC
    exact p4Q2PZ37AIH_originalNegativeBall_stable
      H beta hbeta epsilon hepsilon B hB C hC
  have hMono :
      Measure.real muH (Ball B (R beta epsilon)) ≤
        Measure.real muH {C : Cfg | T beta f0 C < -(epsilon / 2)} :=
    measureReal_mono hSub
  exact ⟨
    (p4Q2PZ37AIH_originalNegativeBall_mass_ge_explicit
      H beta hbeta epsilon hepsilon B).trans hMono,
    (p4Q2PZ37AIH_originalNegativeBall_mass_pos
      H beta hbeta epsilon hepsilon B).trans_le hMono⟩

/-- Every original positive coupling has an actual negative center, a
specified positive radius, uniform half-margin negativity on its original
spatial ball, and an explicit strictly positive genuine Haar mass floor. -/
theorem p4Q2PZ37AIH_originalTransfer_exists_negativeHaarBall
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ B : Cfg,
      T beta f0 B < -(margin beta) ∧
      0 < R beta (margin beta) ∧
      (∀ C ∈ Ball B (R beta (margin beta)),
        T beta f0 C < -(margin beta / 2)) ∧
      0 < kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ∧
      kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH (Ball B (R beta (margin beta))) := by
  have hMargin := p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta
  obtain ⟨B, hB⟩ :=
    p4Q2PZ37AIG_originalTransfer_exists_below_negativeMargin H beta hbeta
  exact ⟨B, hB,
    p4Q2PZ37AIH_originalNegativeBallRadius_pos H beta hbeta.le (margin beta) hMargin,
    p4Q2PZ37AIH_originalNegativeBall_stable H beta hbeta.le (margin beta) hMargin B hB,
    pow_pos (p4Q2PZ37ADQ_sphereRadiusFraction_pos _) _,
    p4Q2PZ37AIH_originalNegativeBall_mass_ge_explicit
      H beta hbeta.le (margin beta) hMargin B⟩

/-- The prescribed general-coupling radius quantitatively bounds the
genuine Haar mass of the actual HALF-margin negative transfer region. -/
theorem p4Q2PZ37AIH_originalHalfNegativeRegion_mass_ge_explicit
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ∧
      kappa (R beta (margin beta) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH {C : Cfg | T beta f0 C < -(margin beta / 2)} := by
  have hMargin := p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta
  obtain ⟨B, hB⟩ :=
    p4Q2PZ37AIG_originalTransfer_exists_below_negativeMargin H beta hbeta
  exact ⟨pow_pos (p4Q2PZ37ADQ_sphereRadiusFraction_pos _) _,
    (p4Q2PZ37AIH_originalHalfNegativeRegion_mass_of_center
      H beta hbeta.le (margin beta) hMargin B hB).1⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalOneSlabAction_rightOneLinkChordSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalKernel_rightOneLinkChordSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalKernel_rightAllLinkChordSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_transferSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_transferSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_transferSlope_le_halfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_transferSlope_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_transferSlope_fixedCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalTransfer_allLinkSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalTransfer_allLinkHalfCountSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalNegativeBallRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalNegativeBallRadius_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalNegativeBallRadius_fixedCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalNegativeBall_stable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalNegativeBall_mass_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalNegativeBall_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalHalfNegativeRegion_mass_of_center
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalTransfer_exists_negativeHaarBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIH_originalHalfNegativeRegion_mass_ge_explicit
