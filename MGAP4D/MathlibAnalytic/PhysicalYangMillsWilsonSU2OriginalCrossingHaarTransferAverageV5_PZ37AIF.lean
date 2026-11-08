import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSourceHaarLaplaceAnticorrelationV5_PZ37AIE
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIF — original crossing Haar normalization and negative transfer boundary

Every original spatial-link Wilson factor uses the literal relative holonomy
A(e)^(-1) * B(e). Left Haar translation removes A(e) from its integral. Finite
product Haar Fubini identifies the full crossing partition as the power of the
same positive one-link integral, without a boundary-independence assumption.

Retain the complete original one-slab action, both spatial halfweights, the
original ZW physical L2 source, its existing continuous representative, and
the original spatial product Haar measure. The weighted right-boundary Haar
average of the true transfer is exactly Zcross * exp(-beta*pH/2) * LaplaceSrc.
Product integrability is proved before changing the order of integration.
AIE then implies a strictly negative average and an actual negative right
boundary at every beta > 0, including the unchanged fixed beta0.

This proves existence, without selecting or numerically evaluating a boundary.
It does not prove a positive transfer boundary, a both-sign shell, uniform-in-H
coercivity, a Hamiltonian spectral gap, or a continuum Yang--Mills mass gap.
All existing definitions, assumptions, proof history, root, pins and workflows
are retained unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIF_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIF_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIF_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIF_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIF_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local notation "nu" => normalizedCompactHaar G
local instance p4Q2PZ37AIF_linkHaar : Measure.IsHaarMeasure nu := by
  dsimp [normalizedCompactHaar]
  infer_instance

namespace GroundStatePosteriorJoint

/-- The actual single-link SU(2) Wilson Boltzmann integral against the
original normalized compact Haar probability, for every real coupling. -/
def p4Q2PZ37AIF_originalSingleLinkPartition (beta : ℝ) : ℝ :=
  ∫ g : G, Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 g) ∂nu

theorem p4Q2PZ37AIF_originalSingleLinkPartition_integrable (beta : ℝ) :
    Integrable (fun g : G =>
      Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 g)) nu :=
  (Real.continuous_exp.comp
    (continuous_const.mul (continuous_specialUnitaryWilsonPlaquetteEnergy 2))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Strict positivity is a theorem about the actual exponential Haar integral. -/
theorem p4Q2PZ37AIF_originalSingleLinkPartition_pos (beta : ℝ) :
    0 < p4Q2PZ37AIF_originalSingleLinkPartition beta := by
  exact integral_exp_pos (p4Q2PZ37AIF_originalSingleLinkPartition_integrable beta)

/-- Original relative holonomy A^(-1)B, normalized by LEFT Haar translation.
No symmetry approximation or replacement of the original link action. -/
theorem p4Q2PZ37AIF_originalSingleLinkKernel_haarIntegral
    (beta : ℝ) (a : G) :
    (∫ b : G, specialUnitaryWilsonRelativeKernel 2 beta a b ∂nu) =
      p4Q2PZ37AIF_originalSingleLinkPartition beta := by
  change (∫ b : G,
    Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 (a⁻¹ * b)) ∂nu) =
      ∫ g : G, Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 g) ∂nu
  exact integral_mul_left_eq_self (μ := nu)
    (fun g : G => Real.exp (-beta * specialUnitaryWilsonPlaquetteEnergy 2 g)) a⁻¹

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Cross" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "KC" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "LaplaceSrc" => p4Q2PZ37AIE_originalCenteredSourceLaplace H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AIF_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Explicit normalization: the genuine single-link Haar integral to the
number of actual original spatial links. -/
def p4Q2PZ37AIF_originalCrossingPartition (beta : ℝ) : ℝ :=
  (p4Q2PZ37AIF_originalSingleLinkPartition beta) ^ Fintype.card Link

local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H

theorem p4Q2PZ37AIF_originalCrossingPartition_pos (beta : ℝ) :
    0 < Zcross beta := by
  exact pow_pos (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta) _

/-- Finite product Haar Fubini, followed by each ORIGINAL link's left
translation, proves independence of the left boundary exactly. -/
theorem p4Q2PZ37AIF_originalCrossingKernel_haarIntegral
    (beta : ℝ) (A : Cfg) :
    (∫ B : Cfg, KC beta A B ∂muH) = Zcross beta := by
  classical
  have hMeasure : muH = Measure.pi (fun _ : Link => nu) := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    exact congrArg
      (fun i : Fintype Link =>
        letI : Fintype Link := i
        Measure.pi (fun _ : Link => nu))
      (Subsingleton.elim
        (oneSlabHaarL2SpatialLinkFintype H)
        (inferInstance : Fintype Link))
  rw [hMeasure]
  simp only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel,
    periodicHypercubicEvenSpatialSliceLinkList, Finset.prod_map_toList]
  calc
    _ = ∏ e : Link,
        ∫ b : G, specialUnitaryWilsonRelativeKernel 2 beta (A e) b ∂nu :=
      integral_fintype_prod_eq_prod
        (μ := fun _ : Link => nu)
        (fun e : Link => fun b : G => specialUnitaryWilsonRelativeKernel 2 beta (A e) b)
    _ = Zcross beta := by
      simp_rw [p4Q2PZ37AIF_originalSingleLinkKernel_haarIntegral beta]
      simp [p4Q2PZ37AIF_originalCrossingPartition]

/-- The normalized kernel is the exponential of the original crossing action. -/
theorem p4Q2PZ37AIF_originalCrossingBoltzmann_haarIntegral
    (beta : ℝ) (A : Cfg) :
    (∫ B : Cfg, Real.exp (-beta * Cross A B) ∂muH) = Zcross beta := by
  simpa only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
    using p4Q2PZ37AIF_originalCrossingKernel_haarIntegral H beta A


/-- The exact source-weighted crossing integrand is integrable for product Haar.
This is the analytic hypothesis used in Fubini, proved from compact continuity. -/
theorem p4Q2PZ37AIF_originalWeightedCrossing_jointIntegrable (beta : ℝ) :
    Integrable (fun P : Cfg × Cfg =>
      (fCont P.1 * Real.exp (-(beta / 2) * W P.1)) *
        KC beta P.1 P.2) (Measure.prod muH muH) := by
  have hf : Continuous (fun P : Cfg × Cfg => fCont P.1) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.comp continuous_fst
  have hw : Continuous (fun P : Cfg × Cfg => W P.1) :=
    (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2).comp
      continuous_fst
  have hk : Continuous (fun P : Cfg × Cfg => KC beta P.1 P.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous H 2 beta
  exact ((hf.mul (Real.continuous_exp.comp (continuous_const.mul hw))).mul
    hk).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Multiplying by the inverse RIGHT halfweight leaves the unchanged LEFT
halfweight and the unchanged full crossing kernel, pointwise. -/
theorem p4Q2PZ37AIF_originalKernel_rightWeightCancellation
    (beta : ℝ) (A B : Cfg) :
    Real.exp ((beta / 2) * W B) * K beta A B =
      Real.exp (-(beta / 2) * W A) * KC beta A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  ring

/-- Equality at EVERY right boundary uses the original physical L2 source's
already proved a.e. equality to fCont; no chosen L2 point value is assumed. -/
theorem p4Q2PZ37AIF_originalRightWeightedTransfer_eq_crossingIntegral
    (beta : ℝ) (B : Cfg) :
    Real.exp ((beta / 2) * W B) * T beta f0 B =
      ∫ A : Cfg, (fCont A * Real.exp (-(beta / 2) * W A)) * KC beta A B ∂muH := by
  rw [p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta B,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with A
  calc
    Real.exp ((beta / 2) * W B) * (fCont A * K beta A B) =
        fCont A * (Real.exp ((beta / 2) * W B) * K beta A B) := by ring
    _ = (fCont A * Real.exp (-(beta / 2) * W A)) * KC beta A B := by
      rw [p4Q2PZ37AIF_originalKernel_rightWeightCancellation H beta A B]
      ring

theorem p4Q2PZ37AIF_originalRightWeightedTransfer_integrable (beta : ℝ) :
    Integrable (fun B : Cfg =>
      Real.exp ((beta / 2) * W B) * T beta f0 B) muH := by
  apply (p4Q2PZ37AIF_originalWeightedCrossing_jointIntegrable H beta).integral_prod_right.congr
  filter_upwards with B
  exact (p4Q2PZ37AIF_originalRightWeightedTransfer_eq_crossingIntegral H beta B).symm

/-- The requested weighted right-boundary Haar average of the ORIGINAL
full one-slab physical source transfer. -/
def p4Q2PZ37AIF_originalRightWeightedTransferAverage (beta : ℝ) : ℝ :=
  ∫ B : Cfg, Real.exp ((beta / 2) * W B) * T beta f0 B ∂muH

local notation "Avg" => p4Q2PZ37AIF_originalRightWeightedTransferAverage H

/-- Exact Fubini and true crossing-Haar normalization, with both original
halfweights accounted for. No crossing independence assumption is introduced. -/
theorem p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_crossingPartition
    (beta : ℝ) :
    Avg beta = Zcross beta *
      (∫ A : Cfg, fCont A * Real.exp (-(beta / 2) * W A) ∂muH) := by
  unfold p4Q2PZ37AIF_originalRightWeightedTransferAverage
  calc
    (∫ B : Cfg, Real.exp ((beta / 2) * W B) * T beta f0 B ∂muH) =
        ∫ B : Cfg, ∫ A : Cfg,
          (fCont A * Real.exp (-(beta / 2) * W A)) * KC beta A B ∂muH ∂muH := by
      apply integral_congr_ae
      filter_upwards with B
      exact p4Q2PZ37AIF_originalRightWeightedTransfer_eq_crossingIntegral H beta B
    _ = ∫ A : Cfg, ∫ B : Cfg,
          (fCont A * Real.exp (-(beta / 2) * W A)) * KC beta A B ∂muH ∂muH :=
      (integral_integral_swap
        (p4Q2PZ37AIF_originalWeightedCrossing_jointIntegrable H beta)).symm
    _ = Zcross beta *
        (∫ A : Cfg, fCont A * Real.exp (-(beta / 2) * W A) ∂muH) := by
      simp_rw [integral_const_mul, p4Q2PZ37AIF_originalCrossingKernel_haarIntegral H beta]
      rw [integral_mul_const]
      ring

/-- Exact source centering connects the remaining left halfweight to AIE's
genuine source-only Haar-Laplace integral. -/
theorem p4Q2PZ37AIF_originalLeftHalfweightSource_eq_Laplace (beta : ℝ) :
    (∫ A : Cfg, fCont A * Real.exp (-(beta / 2) * W A) ∂muH) =
      Real.exp (-(beta * (pH / 2))) * LaplaceSrc beta := by
  have hFactor (A : Cfg) :
      Real.exp (-(beta / 2) * W A) =
        Real.exp (-(beta * (pH / 2))) * Real.exp (-(beta * fCont A)) := by
    rw [← Real.exp_add]
    congr 1
    rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H A]
    ring
  calc
    (∫ A : Cfg, fCont A * Real.exp (-(beta / 2) * W A) ∂muH) =
        ∫ A : Cfg, Real.exp (-(beta * (pH / 2))) *
          (fCont A * Real.exp (-(beta * fCont A))) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      rw [hFactor A]
      ring
    _ = Real.exp (-(beta * (pH / 2))) * LaplaceSrc beta := by
      rw [integral_const_mul]
      rfl

/-- The full original transfer's average is exactly a positive crossing
partition times a positive scalar times the true AIE source Laplace integral. -/
theorem p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_Laplace
    (beta : ℝ) :
    Avg beta = Zcross beta * Real.exp (-(beta * (pH / 2))) * LaplaceSrc beta := by
  rw [p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_crossingPartition H beta,
    p4Q2PZ37AIF_originalLeftHalfweightSource_eq_Laplace H beta]
  ring

/-- Unconditional strict negative Haar average of the original physical
transfer for every finite H and every positive coupling. -/
theorem p4Q2PZ37AIF_originalRightWeightedTransferAverage_neg
    (beta : ℝ) (hbeta : 0 < beta) : Avg beta < 0 := by
  rw [p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_Laplace H beta]
  exact mul_neg_of_pos_of_neg
    (mul_pos (p4Q2PZ37AIF_originalCrossingPartition_pos H beta) (Real.exp_pos _))
    (p4Q2PZ37AIE_originalCenteredSourceLaplace_neg H beta hbeta)

/-- There exists an actual right boundary with strictly negative original
full physical transfer. This is an existence theorem, not a selected grid value. -/
theorem p4Q2PZ37AIF_originalTransfer_exists_negativeBoundary
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ B : Cfg, T beta f0 B < 0 := by
  by_contra hNone
  have hNonneg : ∀ B : Cfg, 0 ≤ T beta f0 B := by
    intro B
    exact le_of_not_gt (fun h => hNone ⟨B, h⟩)
  have hAvgNonneg : 0 ≤ Avg beta := by
    unfold p4Q2PZ37AIF_originalRightWeightedTransferAverage
    apply integral_nonneg
    intro B
    exact mul_nonneg (Real.exp_pos _).le (hNonneg B)
  exact (not_lt_of_ge hAvgNonneg)
    (p4Q2PZ37AIF_originalRightWeightedTransferAverage_neg H beta hbeta)

theorem p4Q2PZ37AIF_originalFixedRightWeightedTransferAverage_neg :
    Avg beta0 < 0 :=
  p4Q2PZ37AIF_originalRightWeightedTransferAverage_neg
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos

theorem p4Q2PZ37AIF_originalFixedTransfer_exists_negativeBoundary :
    ∃ B : Cfg, T beta0 f0 B < 0 :=
  p4Q2PZ37AIF_originalTransfer_exists_negativeBoundary
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalSingleLinkPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalSingleLinkPartition_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalSingleLinkPartition_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalSingleLinkKernel_haarIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalCrossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalCrossingPartition_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalCrossingKernel_haarIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalCrossingBoltzmann_haarIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalWeightedCrossing_jointIntegrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalKernel_rightWeightCancellation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalRightWeightedTransfer_eq_crossingIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalRightWeightedTransfer_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalRightWeightedTransferAverage
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_crossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalLeftHalfweightSource_eq_Laplace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalRightWeightedTransferAverage_eq_Laplace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalRightWeightedTransferAverage_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalTransfer_exists_negativeBoundary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalFixedRightWeightedTransferAverage_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIF_originalFixedTransfer_exists_negativeBoundary
