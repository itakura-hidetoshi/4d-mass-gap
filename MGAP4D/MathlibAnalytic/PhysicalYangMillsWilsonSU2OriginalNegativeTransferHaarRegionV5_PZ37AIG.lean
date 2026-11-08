import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCrossingHaarTransferAverageV5_PZ37AIF
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNonzeroRationalSignExistenceV5_PZ37AHH
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAlignedPositiveSpatialHaarMassV5_PZ37AHL
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIG — original negative transfer region with genuine positive Haar mass

Keep the original full Wilson kernel, both spatial halfweights, ZW signed
physical L2 source, its proved continuous representative, and original spatial
product Haar. AIE's variance bound and AIF's exact crossing/Fubini identity
give an explicit positive negative-transfer margin at every beta > 0.

The actual right-boundary transfer is continuous for every real beta.
The strict negative sublevel at the explicit margin is open and has positive
genuine Haar mass: a null sublevel would force an a.e. lower bound on AIF's
weighted average that contradicts its proved negative variance budget.
At the unchanged beta0, existing all-link chordal stability gives a specified
positive radius and the existing original Haar ball theorem gives its mass floor.

All constants depend on H. No positive boundary, both-sign shell, evaluated
numerical boundary, uniform coercivity, Hamiltonian spectral gap, or continuum
Yang--Mills mass gap is asserted. Existing definitions, assumptions, histories,
canonical root, Lean/mathlib pins and workflows are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIG_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIG_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIG_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIG_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIG_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "Avg" => p4Q2PZ37AIF_originalRightWeightedTransferAverage H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AIG_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Quantitative negativity of the actual original right-weighted transfer
average, retaining both original halfweights and the exact crossing partition. -/
theorem p4Q2PZ37AIG_originalRightWeightedTransferAverage_le_negativeVariance
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Avg beta ≤ -(beta * Zcross beta * Real.exp (-(beta * pH)) * Vsrc) := by
  have hLap :=
    p4Q2PZ37AIE_originalCenteredSourceLaplace_le_negativeVariance H beta hbeta
  have hFactor : 0 ≤ Zcross beta * Real.exp (-(beta * (pH / 2))) :=
    mul_nonneg (p4Q2PZ37AIF_originalCrossingPartition_pos H beta).le
      (Real.exp_pos _).le
  have hExp :
      Real.exp (-(beta * (pH / 2))) * Real.exp (-(beta * (pH / 2))) =
        Real.exp (-(beta * pH)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_Laplace H beta]
  calc
    _ ≤ (Zcross beta * Real.exp (-(beta * (pH / 2)))) *
        (-(beta * Real.exp (-(beta * (pH / 2))) * Vsrc)) :=
      mul_le_mul_of_nonneg_left hLap hFactor
    _ = -(beta * Zcross beta *
        (Real.exp (-(beta * (pH / 2))) * Real.exp (-(beta * (pH / 2)))) *
          Vsrc) := by ring
    _ = -(beta * Zcross beta * Real.exp (-(beta * pH)) * Vsrc) := by rw [hExp]

/-- An explicit finite-volume transfer margin. The genuine crossing partition
and genuine source variance are retained, rather than supplied as estimates. -/
def p4Q2PZ37AIG_originalNegativeTransferMargin (beta : ℝ) : ℝ :=
  beta * Zcross beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2

local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H

theorem p4Q2PZ37AIG_originalNegativeTransferMargin_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < margin beta := by
  unfold p4Q2PZ37AIG_originalNegativeTransferMargin
  exact div_pos
    (mul_pos
      (mul_pos (mul_pos hbeta (p4Q2PZ37AIF_originalCrossingPartition_pos H beta))
        (Real.exp_pos _))
      (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2)
    (by norm_num)

/-- Exact conversion of the margin to half of the negative average budget. -/
theorem p4Q2PZ37AIG_originalNegativeTransferMargin_weightIdentity
    (beta : ℝ) :
    margin beta * Real.exp (beta * pH) =
      beta * Zcross beta * Real.exp (-(beta * pH)) * Vsrc / 2 := by
  have hExp :
      Real.exp (-(2 * beta * pH)) * Real.exp (beta * pH) =
        Real.exp (-(beta * pH)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold p4Q2PZ37AIG_originalNegativeTransferMargin
  calc
    _ = beta * Zcross beta *
        (Real.exp (-(2 * beta * pH)) * Real.exp (beta * pH)) * Vsrc / 2 := by ring
    _ = _ := by rw [hExp]

/-- The original right inverse halfweight has the actual spatial-action bound. -/
theorem p4Q2PZ37AIG_originalRightWeight_le_expCount
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Real.exp ((beta / 2) * W B) ≤ Real.exp (beta * pH) := by
  have hW : W B ≤ 2 * pH :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H 2 (by norm_num) B
  have hMul := mul_le_mul_of_nonneg_left hW (div_nonneg hbeta (by norm_num : (0 : ℝ) ≤ 2))
  apply Real.exp_le_exp.mpr
  nlinarith only [hMul]

/-- The original pointwise physical transfer is continuous in its RIGHT
boundary for every real coupling. Source continuity alone is not the claim:
the original complete kernel, both halfweights, compact parametric integration,
and the genuine AHP a.e.-source bridge are all used. -/
theorem p4Q2PZ37AIG_originalTransfer_continuous (beta : ℝ) :
    Continuous (fun B : Cfg => T beta f0 B) := by
  have hf : Continuous (fun P : Cfg × Cfg => fCont P.2) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_snd
  have hKernel : Continuous (fun Q : Cfg × Cfg => K beta Q.1 Q.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 beta
  have hSwap : Continuous (Prod.swap : Cfg × Cfg → Cfg × Cfg) :=
    continuous_swap
  have hk : Continuous (fun P : Cfg × Cfg => K beta P.2 P.1) :=
    Continuous.comp
      (g := fun Q : Cfg × Cfg => K beta Q.1 Q.2)
      (f := (Prod.swap : Cfg × Cfg → Cfg × Cfg))
      hKernel hSwap
  have hJoint : Continuous (fun P : Cfg × Cfg =>
      fCont P.2 * K beta P.2 P.1) := hf.mul hk
  have hIntegral : Continuous (fun B : Cfg =>
      ∫ A : Cfg, fCont A * K beta A B ∂muH) := by
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := muH)
        (f := fun B A : Cfg => fCont A * K beta A B)
        hJoint (s := Set.univ) isCompact_univ)
  have hEq :
      (fun B : Cfg => T beta f0 B) =
        (fun B : Cfg => ∫ A : Cfg, fCont A * K beta A B ∂muH) := by
    funext B
    exact p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta B
  rw [hEq]
  exact hIntegral

/-- The original pointwise physical transfer, not just its weighted average,
is integrable against the original spatial Haar measure. -/
theorem p4Q2PZ37AIG_originalTransfer_integrable (beta : ℝ) :
    Integrable (fun B : Cfg => T beta f0 B) muH :=
  (p4Q2PZ37AIG_originalTransfer_continuous H beta).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- A definite negative sublevel of the actual original physical transfer.
The margin depends only on the stated original finite-volume quantities. -/
def p4Q2PZ37AIG_originalNegativeTransferRegion (beta : ℝ) : Set Cfg :=
  {B | T beta f0 B < -(margin beta)}

local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H

theorem p4Q2PZ37AIG_originalNegativeTransferRegion_isOpen (beta : ℝ) :
    IsOpen (Region beta) :=
  isOpen_lt (p4Q2PZ37AIG_originalTransfer_continuous H beta) continuous_const

theorem p4Q2PZ37AIG_originalNegativeTransferRegion_measurable (beta : ℝ) :
    MeasurableSet (Region beta) :=
  (p4Q2PZ37AIG_originalNegativeTransferRegion_isOpen H beta).measurableSet

/-- Positive genuine Haar mass follows from the negative average budget.
It is not inferred merely from existence of a negative point. -/
theorem p4Q2PZ37AIG_originalNegativeTransferRegion_measure_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < muH (Region beta) := by
  have hMargin := p4Q2PZ37AIG_originalNegativeTransferMargin_pos H beta hbeta
  have hD : 0 < beta * Zcross beta * Real.exp (-(beta * pH)) * Vsrc :=
    mul_pos
      (mul_pos (mul_pos hbeta (p4Q2PZ37AIF_originalCrossingPartition_pos H beta))
        (Real.exp_pos _))
      (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hScale := p4Q2PZ37AIG_originalNegativeTransferMargin_weightIdentity H beta
  have hBudget :=
    p4Q2PZ37AIG_originalRightWeightedTransferAverage_le_negativeVariance
      H beta hbeta.le
  by_contra hNotPos
  have hZero : muH (Region beta) = 0 :=
    le_antisymm (le_of_not_gt hNotPos) (zero_le _)
  have hAE : ∀ᵐ B ∂muH, -(margin beta) ≤ T beta f0 B := by
    rw [ae_iff]
    simpa only [p4Q2PZ37AIG_originalNegativeTransferRegion, not_le] using hZero
  have hPointwise : ∀ᵐ B ∂muH,
      -(margin beta * Real.exp (beta * pH)) ≤
        Real.exp ((beta / 2) * W B) * T beta f0 B := by
    filter_upwards [hAE] with B hB
    calc
      -(margin beta * Real.exp (beta * pH)) =
          (-(margin beta)) * Real.exp (beta * pH) := by ring
      _ ≤ (-(margin beta)) * Real.exp ((beta / 2) * W B) :=
        mul_le_mul_of_nonpos_left
          (p4Q2PZ37AIG_originalRightWeight_le_expCount H beta hbeta.le B)
          (neg_nonpos.mpr hMargin.le)
      _ = Real.exp ((beta / 2) * W B) * (-(margin beta)) := by ring
      _ ≤ Real.exp ((beta / 2) * W B) * T beta f0 B :=
        mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
  have hLower : -(margin beta * Real.exp (beta * pH)) ≤ Avg beta := by
    change -(margin beta * Real.exp (beta * pH)) ≤
      ∫ B : Cfg, Real.exp ((beta / 2) * W B) * T beta f0 B ∂muH
    simpa only [integral_const, probReal_univ, one_smul] using
      (integral_mono_ae
        (integrable_const (μ := muH) (-(margin beta * Real.exp (beta * pH))))
        (p4Q2PZ37AIF_originalRightWeightedTransfer_integrable H beta) hPointwise)
  linarith only [hLower, hBudget, hScale, hD]

theorem p4Q2PZ37AIG_originalNegativeTransferRegion_realMeasure_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < Measure.real muH (Region beta) := by
  have hPos := p4Q2PZ37AIG_originalNegativeTransferRegion_measure_pos H beta hbeta
  exact ENNReal.toReal_pos hPos.ne' (measure_ne_top muH _)

/-- The boundary witness now lies below the explicit nonzero margin. -/
theorem p4Q2PZ37AIG_originalTransfer_exists_below_negativeMargin
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ B : Cfg, T beta f0 B < -(margin beta) := by
  have hPos := p4Q2PZ37AIG_originalNegativeTransferRegion_measure_pos H beta hbeta
  by_contra hNo
  have hEmpty : Region beta = ∅ := by
    ext B
    constructor
    · intro hB
      exact False.elim (hNo ⟨B, hB⟩)
    · intro hB
      exact False.elim hB
  rw [hEmpty, measure_empty] at hPos
  exact (lt_irrefl (0 : ENNReal)) hPos

/-- The unchanged original fixed coupling has an open measurable negative
region of positive true Haar mass with the same explicit variance margin. -/
theorem p4Q2PZ37AIG_originalFixedNegativeTransferRegion_realMeasure_pos :
    0 < Measure.real muH (Region beta0) :=
  p4Q2PZ37AIG_originalNegativeTransferRegion_realMeasure_pos
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos

local notation "t" => T beta0 f0
local notation "Dsp" => p4Q2PZ37AGG_originalSpatialChordalDistance H
local notation "L" => p4Q2PZ37AHH_transferSlope H
local notation "Ball" => p4Q2PZ37AHL_originalSpatialBall H
local notation "kappa" => p4Q2PZ37ADQ_sphereRadiusFraction

/-- Radius from the actual original transfer slope and a supplied margin. -/
def p4Q2PZ37AIG_originalFixedNegativeBallRadius (epsilon : ℝ) : ℝ :=
  epsilon / (2 * (L + 1))

local notation "R" => p4Q2PZ37AIG_originalFixedNegativeBallRadius H

theorem p4Q2PZ37AIG_originalFixedNegativeBallRadius_pos
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    0 < R epsilon := by
  unfold p4Q2PZ37AIG_originalFixedNegativeBallRadius
  have hL : 0 ≤ L := p4Q2PZ37AHH_transferSlope_nonneg H
  exact div_pos hepsilon (by positivity)

/-- A center below -epsilon remains below -epsilon/2 throughout this
positive-radius ball in the SAME original all-link chordal distance. -/
theorem p4Q2PZ37AIG_originalFixedNegativeBall_stable
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (B : Cfg) (hB : t B < -epsilon) :
    ∀ C ∈ Ball B (R epsilon), t C < -(epsilon / 2) := by
  have hL : 0 ≤ L := p4Q2PZ37AHH_transferSlope_nonneg H
  have hDen : 0 < 2 * (L + 1) := by positivity
  have hR : 0 < R epsilon :=
    p4Q2PZ37AIG_originalFixedNegativeBallRadius_pos H epsilon hepsilon
  have hEq : R epsilon * (2 * (L + 1)) = epsilon := by
    unfold p4Q2PZ37AIG_originalFixedNegativeBallRadius
    exact div_mul_cancel₀ epsilon hDen.ne'
  have hScale : L * R epsilon < epsilon / 2 := by
    nlinarith only [hEq, hR]
  intro C hC
  change Dsp B C < R epsilon at hC
  have hLip : |t B - t C| ≤ L * Dsp B C :=
    p4Q2PZ37AHH_originalTransfer_allLinkSlope H B C
  have hSmall : L * Dsp B C < epsilon / 2 :=
    (mul_le_mul_of_nonneg_left hC.le hL).trans_lt hScale
  have hDelta : -(L * Dsp B C) ≤ t B - t C :=
    (abs_le.mp hLip).1
  linarith only [hB, hSmall, hDelta]

/-- Nat.card removes the presentation-dependent Fintype argument from the
already proved AHL lower bound. The measure is still the original muH. -/
theorem p4Q2PZ37AIG_originalFixedNegativeBall_mass_ge_explicit
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (B : Cfg) :
    kappa (R epsilon / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
      Measure.real muH (Ball B (R epsilon)) := by
  simpa only [Fintype.card_eq_nat_card] using
    (p4Q2PZ37AHL_originalSpatialBall_mass_ge_explicit H B (R epsilon)
      (p4Q2PZ37AIG_originalFixedNegativeBallRadius_pos H epsilon hepsilon))

theorem p4Q2PZ37AIG_originalFixedNegativeBall_mass_pos
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (B : Cfg) :
    0 < Measure.real muH (Ball B (R epsilon)) := by
  exact p4Q2PZ37AHL_originalSpatialBall_mass_pos H B (R epsilon)
    (p4Q2PZ37AIG_originalFixedNegativeBallRadius_pos H epsilon hepsilon)

/-- Both the explicit original product-Haar floor and strict positive mass
pass from the chordal ball to the actual negative physical-transfer region. -/
theorem p4Q2PZ37AIG_originalFixedNegativeRegion_mass_of_center
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (B : Cfg) (hB : t B < -epsilon) :
    kappa (R epsilon / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH {C : Cfg | t C < -(epsilon / 2)} ∧
      0 < Measure.real muH {C : Cfg | t C < -(epsilon / 2)} := by
  have hSub :
      Ball B (R epsilon) ⊆ {C : Cfg | t C < -(epsilon / 2)} := by
    intro C hC
    exact p4Q2PZ37AIG_originalFixedNegativeBall_stable
      H epsilon hepsilon B hB C hC
  have hMono :
      Measure.real muH (Ball B (R epsilon)) ≤
        Measure.real muH {C : Cfg | t C < -(epsilon / 2)} :=
    measureReal_mono hSub
  exact ⟨
    (p4Q2PZ37AIG_originalFixedNegativeBall_mass_ge_explicit
      H epsilon hepsilon B).trans hMono,
    (p4Q2PZ37AIG_originalFixedNegativeBall_mass_pos
      H epsilon hepsilon B).trans_le hMono⟩

/-- Unconditional original fixed-coupling certificate: the margin and center
are supplied by the true average theorem, and the radius and Haar floor by
the original all-link slope and genuine SU(2) product-Haar geometry. -/
theorem p4Q2PZ37AIG_originalFixedTransfer_exists_negativeHaarBall :
    ∃ B : Cfg,
      t B < -(margin beta0) ∧
      0 < R (margin beta0) ∧
      (∀ C ∈ Ball B (R (margin beta0)), t C < -(margin beta0 / 2)) ∧
      kappa (R (margin beta0) / ((Nat.card Link : ℝ) + 1)) ^ Nat.card Link ≤
        Measure.real muH (Ball B (R (margin beta0))) ∧
      0 < Measure.real muH (Ball B (R (margin beta0))) := by
  have hMargin := p4Q2PZ37AIG_originalNegativeTransferMargin_pos
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
  obtain ⟨B, hB⟩ := p4Q2PZ37AIG_originalTransfer_exists_below_negativeMargin
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
  exact ⟨B, hB,
    p4Q2PZ37AIG_originalFixedNegativeBallRadius_pos H (margin beta0) hMargin,
    p4Q2PZ37AIG_originalFixedNegativeBall_stable H (margin beta0) hMargin B hB,
    p4Q2PZ37AIG_originalFixedNegativeBall_mass_ge_explicit
      H (margin beta0) hMargin B,
    p4Q2PZ37AIG_originalFixedNegativeBall_mass_pos H (margin beta0) hMargin B⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalRightWeightedTransferAverage_le_negativeVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalNegativeTransferMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalNegativeTransferMargin_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalNegativeTransferMargin_weightIdentity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalRightWeight_le_expCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalTransfer_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalTransfer_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalNegativeTransferRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalNegativeTransferRegion_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalNegativeTransferRegion_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalNegativeTransferRegion_measure_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalNegativeTransferRegion_realMeasure_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalTransfer_exists_below_negativeMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalFixedNegativeTransferRegion_realMeasure_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalFixedNegativeBallRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalFixedNegativeBallRadius_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalFixedNegativeBall_stable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalFixedNegativeBall_mass_ge_explicit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalFixedNegativeBall_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalFixedNegativeRegion_mass_of_center
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIG_originalFixedTransfer_exists_negativeHaarBall
