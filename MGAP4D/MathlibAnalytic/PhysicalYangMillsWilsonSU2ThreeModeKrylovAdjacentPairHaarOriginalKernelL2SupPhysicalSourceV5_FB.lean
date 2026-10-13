import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedFineFrozenTraceRayleighV5_FA
import Mathlib.Tactic

/-!
# P4-Q2-FB: actual Wilson kernel L2-to-sup smoothing and physical-source Rayleigh

The missing implication is NOT an embedding of arbitrary Haar L2 into
BCF. The original mean is a specific integral operator:
M_f(B) = lambda^(-1) integral K(A,B) f(A) dHaar(A) / Omega(B).
For the ACTUAL Wilson kernel |K| <= 1 and probability Haar, its integral
has absolute value <= ||f||_2, for every signed source. Thus

  ||M_f||_sup <= lambda^(-1) ||Omega^(-1)||_sup ||f||_2.

This closes the finite-volume L2/BCF gap without a new norm hypothesis.
A weighted pointwise bound keeps the positive vacuum cancellation.
The exact EU source/vacuum factor is consequently <= B(H,beta)||F_a||_2,
where B = ||W|| lambda^(-1) ||Omega^(-1)|| (exp(8 beta)+2).
Every actual fine-right mode has norm <= 1, so its factor <= B, with no
mode, horizon or fine-coupling dependence in B. These finite-volume
constants are NOT asserted uniform in H or the frozen coupling.

Crucially apply the estimate to the WHOLE SIGNED physical source,
not to a trace or coefficient-l1 majorant. The original Gram satisfies

  a*G a <= 3072 (H+1)^3 beta^2 B(H,beta)^2 ||sum_i a_i R_i||_2^2.

This is a comparison to the genuine physical input Gram norm. It does
not falsely identify a nonorthogonal Krylov coefficient norm with the
physical norm and does not postulate Bessel, marginal, or mixing bounds.
C1/C2/C3 and H2/H3/H4 continuum Yang--Mills remain OPEN.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 900000

local instance p4Q2FB_topologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2FB_compactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2FB_secondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2FB_measurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2FB_borelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2FB_haarProbability (H N : ℕ) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

/-- Genuine original Wilson integral smoothing. No positivity of the
source is required and no L2 representative is bounded pointwise. -/
theorem p4Q2FB_originalTransferIntegral_abs_le_sourceL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |decomposableOneSliceTransferIntegral H N beta f B| ≤ ‖f‖ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  have hf : Integrable (fun A => f A) μ :=
    (Lp.memLp f).integrable (by norm_num)
  have hDom : ∀ A, ‖K A B * f A‖ ≤ ‖f A‖ := by
    intro A
    have hK : |K A B| ≤ 1 :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta A B
    calc
      ‖K A B * f A‖ = |K A B| * ‖f A‖ := by
        rw [norm_mul, Real.norm_eq_abs]
      _ ≤ 1 * ‖f A‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ = ‖f A‖ := one_mul _
  have hIntegral : ‖∫ A, K A B * f A ∂μ‖ ≤ ∫ A, ‖f A‖ ∂μ :=
    norm_integral_le_of_norm_le hf.norm (Filter.Eventually.of_forall hDom)
  have hAbs : |decomposableOneSliceTransferIntegral H N beta f B| ≤
      ∫ A, ‖f A‖ ∂μ := by
    simpa only [Real.norm_eq_abs] using hIntegral
  exact hAbs.trans (physicalHaarSignedSource_integral_norm_le_L2 H N f)

/-- The positive vacuum is cancelled before taking a pointwise bound.
This weighted estimate has no inverse-vacuum supremum. -/
theorem p4Q2FB_originalVacuumMean_weighted_abs_le_sourceL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta B *
      |normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f B| ≤
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹ * ‖f‖ := by
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  let omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta B
  let F : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := f
  let t := decomposableOneSliceTransferIntegral H N beta F B
  have hL : 0 ≤ L := inv_nonneg.mpr (norm_nonneg _)
  have hp : 0 < omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  have hInt : |t| ≤ ‖f‖ :=
    p4Q2FB_originalTransferIntegral_abs_le_sourceL2 H N hN beta hbeta F B
  change omega * |L * t / omega| ≤ L * ‖f‖
  rw [abs_div, abs_mul, abs_of_nonneg hL, abs_of_pos hp]
  calc
    omega * (L * |t| / omega) = (L * |t|) * (omega / omega) := by ring
    _ = L * |t| := by rw [div_self hp.ne', mul_one]
    _ ≤ L * ‖f‖ := mul_le_mul_of_nonneg_left hInt hL

/-- Pointwise original Wilson mean smoothing with precisely its true
continuous positive vacuum inverse and physical transfer normalization. -/
theorem p4Q2FB_originalVacuumMean_abs_le_sourceL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f B| ≤
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
      ‖normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta‖ * ‖f‖ := by
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  let omega := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta B
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let m := normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f B
  have hp : 0 < omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  have hL : 0 ≤ L := inv_nonneg.mpr (norm_nonneg _)
  have hw : omega * |m| ≤ L * ‖f‖ :=
    p4Q2FB_originalVacuumMean_weighted_abs_le_sourceL2 H N hN beta hbeta f B
  have hInv : omega⁻¹ ≤ ‖V‖ :=
    normalizedPhysicalOneSlabContinuousVacuumInverse_le_norm H N hN beta hbeta B
  calc
    |m| = omega⁻¹ * (omega * |m|) := by rw [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    _ ≤ omega⁻¹ * (L * ‖f‖) := mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hp.le)
    _ ≤ ‖V‖ * (L * ‖f‖) := mul_le_mul_of_nonneg_right hInv (mul_nonneg hL (norm_nonneg _))
    _ = L * ‖V‖ * ‖f‖ := by ring

/-- The previously missing BCF sup norm bound on the ACTUAL original
Wilson joint mean. This is unconditional for every signed physical L2
source at every finite volume, not a certificate supplied by the user. -/
theorem p4Q2FB_originalVacuumMeanJoint_norm_le_sourceL2
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f‖ ≤
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
      ‖normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta‖ * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).2
  intro z
  change ‖normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f z.2‖ ≤ _
  simpa only [Real.norm_eq_abs] using
    p4Q2FB_originalVacuumMean_abs_le_sourceL2 H N hN beta hbeta f z.2

/-- Constructed original Wilson physical Hilbert coefficient. It depends
on finite geometry and frozen coupling, NOT on the signed source,
fine coupling, mode index or Krylov horizon. No volume uniformity. -/
noncomputable def p4Q2FB_originalPhysicalHilbertCoefficient
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  ‖normalizedPhysicalOneSlabJointHalfDensityWeightBCF
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖ *
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖⁻¹ *
    ‖normalizedPhysicalOneSlabContinuousVacuumInverseBCF
      H 2 specialUnitaryTwoWilsonRankPositive beta hbeta‖ *
    (Real.exp (8 * beta) + 2)

theorem p4Q2FB_originalPhysicalHilbertCoefficient_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ p4Q2FB_originalPhysicalHilbertCoefficient H beta hbeta := by
  unfold p4Q2FB_originalPhysicalHilbertCoefficient
  positivity

/-- Eliminate the unknown mean sup norm from EU's exact physical factor,
using the just-PROVED Wilson smoothing and the whole signed source. -/
theorem p4Q2FB_originalSignedFactor_le_physicalSourceNorm
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    fineRightKrylovOriginalSignedSourceVacuumFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a ≤
    p4Q2FB_originalPhysicalHilbertCoefficient (halfExtent (n + 1)) (beta n) (hbeta n) *
      ‖fineRightKrylovOriginalSignedPhysicalSource
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a‖ := by
  let H := halfExtent (n + 1)
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)‖⁻¹
  let V := ‖normalizedPhysicalOneSlabContinuousVacuumInverseBCF
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)‖
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let M := fineRightKrylovOriginalVacuumMeanJointBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hMean : ‖M‖ ≤ L * V * ‖F‖ :=
    p4Q2FB_originalVacuumMeanJoint_norm_le_sourceL2
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) F
  change ‖W‖ * (L * (Real.exp (8 * beta n) + 1) * V * ‖F‖ + ‖M‖) ≤ _
  calc
    ‖W‖ * (L * (Real.exp (8 * beta n) + 1) * V * ‖F‖ + ‖M‖) ≤
      ‖W‖ * (L * (Real.exp (8 * beta n) + 1) * V * ‖F‖ + L * V * ‖F‖) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hMean _) (norm_nonneg W)
    _ = p4Q2FB_originalPhysicalHilbertCoefficient H (beta n) (hbeta n) * ‖F‖ := by
      change ‖W‖ * (L * (Real.exp (8 * beta n) + 1) * V * ‖F‖ + L * V * ‖F‖) =
        (‖W‖ * L * V * (Real.exp (8 * beta n) + 2)) * ‖F‖
      ring

/-- Actual physical individual fine Krylov mode factors are controlled
uniformly in the mode index and horizon at fixed frozen volume/coupling.
The source is the existing genuine basis mode, not an invented carrier. -/
theorem p4Q2FB_originalModeNormFactor_le_physicalCoefficient
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i : Fin (r + 1)) :
    p4Q2EY_originalWilsonRightModeNormFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i ≤
    p4Q2FB_originalPhysicalHilbertCoefficient (halfExtent (n + 1)) (beta n) (hbeta n) := by
  classical
  let a := p4Q2EY_originalRightModeBasis r i
  let F := physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (i : ℕ)
  let C := p4Q2FB_originalPhysicalHilbertCoefficient (halfExtent (n + 1)) (beta n) (hbeta n)
  have hBasis : fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a = F := by
    simp [fineRightKrylovOriginalSignedPhysicalSource, a, p4Q2EY_originalRightModeBasis, F]
  have hNorm : ‖F‖ ≤ 1 :=
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (i : ℕ)
  have hC : 0 ≤ C := p4Q2FB_originalPhysicalHilbertCoefficient_nonneg _ _ _
  have hFactor := p4Q2FB_originalSignedFactor_le_physicalSourceNorm
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  rw [hBasis] at hFactor
  calc
    p4Q2EY_originalWilsonRightModeNormFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i ≤ C * ‖F‖ := hFactor
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hNorm hC
    _ = C := mul_one _

/-- The actual signed Wilson Gram is bounded in the genuine PHYSICAL
source norm, not an assumed orthonormal coefficient norm. There is no
trace or explicit Krylov-rank loss. The geometry/coupling coefficient
is fully constructed, not an unproved additional physical hypothesis. -/
theorem p4Q2FB_originalSignedGram_rayleigh_le_smallBetaPhysicalSourceNorm
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) ≤
    3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
      (p4Q2FB_originalPhysicalHilbertCoefficient (halfExtent (n + 1)) (beta n) (hbeta n)) ^ 2 *
      ‖fineRightKrylovOriginalSignedPhysicalSource
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a‖ ^ 2 := by
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let B := p4Q2FB_originalPhysicalHilbertCoefficient (halfExtent (n + 1)) (beta n) (hbeta n)
  let A := fineRightKrylovOriginalSignedSourceVacuumFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let C : ℝ := 3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2
  have hA : 0 ≤ A := fineRightKrylovOriginalSignedSourceVacuumFactor_nonneg
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hAB : A ≤ B * ‖F‖ := p4Q2FB_originalSignedFactor_le_physicalSourceNorm
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hSq : A ^ 2 ≤ (B * ‖F‖) ^ 2 := pow_le_pow_left₀ hA hAB 2
  have hC : 0 ≤ C := by positivity
  calc
    star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) ≤ C * A ^ 2 :=
      fineRightKrylovPairHaarResidualGram_rayleigh_le_smallBetaCubic
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a hSmall
    _ ≤ C * (B * ‖F‖) ^ 2 := mul_le_mul_of_nonneg_left hSq hC
    _ = C * B ^ 2 * ‖F‖ ^ 2 := by ring

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FB_originalTransferIntegral_abs_le_sourceL2
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FB_originalVacuumMean_weighted_abs_le_sourceL2
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FB_originalVacuumMean_abs_le_sourceL2
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FB_originalVacuumMeanJoint_norm_le_sourceL2
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FB_originalPhysicalHilbertCoefficient_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FB_originalSignedFactor_le_physicalSourceNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FB_originalModeNormFactor_le_physicalCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FB_originalSignedGram_rayleigh_le_smallBetaPhysicalSourceNorm
