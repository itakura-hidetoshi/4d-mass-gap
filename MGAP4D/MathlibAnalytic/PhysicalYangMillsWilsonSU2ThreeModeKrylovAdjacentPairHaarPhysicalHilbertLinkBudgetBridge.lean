import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHalfDensityLocalHarnack
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSignedPhysicalMeanLinkSourceHilbert
import Mathlib.Tactic

/-!
# P4-Q2: original Wilson half-density and signed Hilbert-mean link bridge

The original uncentered fine-right Krylov source F_a = sum_j a_j R_{n,j}
uses beta(n+1) in its actual physical orbit; the Wilson kernel, vacuum,
half-density, and normalized final receiver use frozen beta(n).

PR #5328 proves the actual half-density factor has
  osc_e(W) <= (exp(8 beta)-1) ||W||_sup.
PR #5330 proves the signed mean has the *pointwise*
  |Delta_e M_f(B)| <= lambda^-1 (exp(8 beta)^2-1)
                     Omega(B)^-1 ||f||_L2(Haar).

Here the reciprocal of the *actual positive continuous vacuum*
is made into a bounded continuous function on the compact spatial
configuration space. Its genuine supremum norm converts the signed
pointwise estimate into a BCF right-link oscillation norm estimate.

Combining both results with the #5326 authentic BCF Leibniz coefficient
gives an explicit **constructed** physical Hilbert link budget and the
resulting true uncentered right-Krylov Gram Rayleigh upper bound.

IMPORTANT: lambda^-1, ||Omega^-1||_sup, ||W||_sup, ||M_f||_sup,
and the sum over true links still depend on finite volume. This
theorem deliberately does NOT claim a Q2-C/D volume-uniform bound.
No finite-range posterior or Dobrushin assumption, and no new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4HilbertBridgeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4HilbertBridgeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4HilbertBridgeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4HilbertBridgeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4HilbertBridgeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4HilbertBridgeLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Actual inverse of the canonical positive continuous Wilson vacuum.
Compactness gives a genuine bounded-continuous function, without
asserting any finite-volume-uniform bound on its norm. -/
noncomputable def normalizedPhysicalOneSlabContinuousVacuumInverseBCF
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ := by
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  have hΩ : Continuous Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta
  have hc : Continuous (fun B => (Ω B)⁻¹) := by
    have hi : Continuous (fun B => (1 : ℝ) / Ω B) :=
      continuous_const.div hΩ
        (fun B =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
            H N hN beta hbeta B).ne')
    simpa only [one_div] using hi
  exact BoundedContinuousFunction.mkOfCompact ⟨fun B => (Ω B)⁻¹, hc⟩

/-- Every right-boundary inverse vacuum value is bounded by precisely
the constructed physical inverse-vacuum BCF norm. -/
theorem normalizedPhysicalOneSlabContinuousVacuumInverse_le_norm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta B)⁻¹ ≤
      ‖normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta‖ := by
  have hp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  have h :=
    (normalizedPhysicalOneSlabContinuousVacuumInverseBCF
      H N hN beta hbeta).norm_coe_le_norm B
  change
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta B)⁻¹‖ ≤
      ‖normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta‖ at h
  simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)] using h

/-- Genuine joint right-link BCF oscillation of the physical signed
normalized-transfer mean, bounded by its original source-Haar Hilbert
norm and the ORIGINAL continuous vacuum's inverse sup norm. -/
theorem normalizedPhysicalOneSlabVacuumMeanJointBCF_rightLinkOscillation_norm_le_signedSourceHilbert
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖physicalJointBCFRightLinkDifference H N
      (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f) e‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        ((Real.exp (8 * beta)) ^ 2 - 1) *
        ‖normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta‖ *
        ‖f‖ := by
  let Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let D : ℝ := (Real.exp (8 * beta)) ^ 2 - 1
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let C : ℝ := l * D * ‖V‖ * ‖f‖
  have hL : 0 ≤ l :=
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)).le
  have hR : 1 ≤ Real.exp (8 * beta) := by
    have hBeta : (0 : ℝ) ≤ 8 * beta := by nlinarith [hbeta]
    simpa using
      (Real.exp_le_exp.mpr hBeta :
        Real.exp (0 : ℝ) ≤ Real.exp (8 * beta))
  have hD : 0 ≤ D := by dsimp [D]; nlinarith [hR]
  have hLD : 0 ≤ l * D := mul_nonneg hL hD
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg hLD (norm_nonneg V)) (norm_nonneg f)
  change ‖physicalJointBCFRightLinkDifference H N
    (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f) e‖ ≤ C
  apply (BoundedContinuousFunction.norm_le hC).2
  rintro ⟨z, g⟩
  change ‖normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f z.2 -
    normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f
      (Function.update z.2 e g)‖ ≤ C
  rw [Real.norm_eq_abs, abs_sub_comm]
  have hSigned :=
    normalizedPhysicalOneSlabVacuumReceiverBCF_rightLinkDifference_abs_le_signedSourceL2
      H N hN beta hbeta f z.2 e g
  have hVac : (Ω z.2)⁻¹ ≤ ‖V‖ := by
    simpa only [Ω, V] using
      (normalizedPhysicalOneSlabContinuousVacuumInverse_le_norm
        H N hN beta hbeta z.2)
  have hMul : (l * D) * (Ω z.2)⁻¹ ≤ (l * D) * ‖V‖ :=
    mul_le_mul_of_nonneg_left hVac hLD
  calc
    |normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f
        (Function.update z.2 e g) -
      normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f z.2| ≤
        l * (D / Ω z.2) * ‖f‖ := by
      simpa [l, D, Ω] using hSigned
    _ = (l * D) * (Ω z.2)⁻¹ * ‖f‖ := by ring
    _ ≤ ((l * D) * ‖V‖) * ‖f‖ :=
      mul_le_mul_of_nonneg_right hMul (norm_nonneg f)
    _ = C := rfl

/-- The actual beta(n+1)-evolved signed fine-right Krylov source,
observed through frozen beta(n), yields a constructed physical
Hilbert-oscillation envelope for EVERY authentic spatial link. -/
noncomputable def fineRightKrylovOriginalPhysicalMeanHilbertLinkEnvelope
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) : ℝ :=
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)‖⁻¹ *
    ((Real.exp (8 * beta n)) ^ 2 - 1) *
    ‖normalizedPhysicalOneSlabContinuousVacuumInverseBCF
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)‖ *
    ‖fineRightKrylovOriginalSignedPhysicalSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a‖

theorem fineRightKrylovOriginalPhysicalMeanLinkOscillation_norm_le_HilbertEnvelope
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    ‖physicalJointBCFRightLinkDifference (halfExtent (n + 1)) 2
      (fineRightKrylovOriginalVacuumMeanJointBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a) e‖ ≤
      fineRightKrylovOriginalPhysicalMeanHilbertLinkEnvelope
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a := by
  simpa only [fineRightKrylovOriginalVacuumMeanJointBCF,
    fineRightKrylovOriginalPhysicalMeanHilbertLinkEnvelope,
    fineRightKrylovOriginalSignedPhysicalSource] using
    (normalizedPhysicalOneSlabVacuumMeanJointBCF_rightLinkOscillation_norm_le_signedSourceHilbert
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)) e)

/-- Explicit finite-volume physical Hilbert upper envelope for the
TRUE constructed #5326 link budget. The only surviving finite-volume
quantities are original physical norms and the actual link sum. -/
noncomputable def fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) : ℝ :=
  let H := halfExtent (n + 1)
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let M := fineRightKrylovOriginalVacuumMeanJointBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let B := fineRightKrylovOriginalPhysicalMeanHilbertLinkEnvelope
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  ‖W‖ * B + ‖M‖ * ((Real.exp (8 * beta n) - 1) * ‖W‖)

theorem fineRightKrylovOriginalHalfDensityMeanLinkBudget_le_physicalHilbertEnvelope
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    fineRightKrylovOriginalHalfDensityMeanLinkBudget
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a e ≤
      fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a := by
  let H := halfExtent (n + 1)
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let M := fineRightKrylovOriginalVacuumMeanJointBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let B := fineRightKrylovOriginalPhysicalMeanHilbertLinkEnvelope
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hMean : ‖physicalJointBCFRightLinkDifference H 2 M e‖ ≤ B :=
    fineRightKrylovOriginalPhysicalMeanLinkOscillation_norm_le_HilbertEnvelope
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a e
  have hWeight :
      ‖physicalJointBCFRightLinkDifference H 2 W e‖ ≤
      (Real.exp (8 * beta n) - 1) * ‖W‖ :=
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightLinkOscillation_norm_le
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
  change ‖W‖ * ‖physicalJointBCFRightLinkDifference H 2 M e‖ +
      ‖M‖ * ‖physicalJointBCFRightLinkDifference H 2 W e‖ ≤
    ‖W‖ * B + ‖M‖ * ((Real.exp (8 * beta n) - 1) * ‖W‖)
  exact add_le_add
    (mul_le_mul_of_nonneg_left hMean (norm_nonneg W))
    (mul_le_mul_of_nonneg_left hWeight (norm_nonneg M))

/-- The actual original uncentered right-Krylov Gram has a quantitative
physical Wilson Harnack + signed-Hilbert Rayleigh envelope, retaining
ALL genuine finite-volume dependence. This does NOT close Q2-C or Q2-D. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_physicalHilbertLinkBudget
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (1 / 2 : ℝ) *
        ∑ _e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
          (fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r a) ^ 2 := by
  have hRay :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_constructedHalfDensityMeanLinkBudget
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hEach (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
      (fineRightKrylovOriginalHalfDensityMeanLinkBudget
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a e) ^ 2 ≤
      (fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a) ^ 2 := by
    exact pow_le_pow_left₀
      (fineRightKrylovOriginalHalfDensityMeanLinkBudget_nonneg
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a e)
      (fineRightKrylovOriginalHalfDensityMeanLinkBudget_le_physicalHilbertEnvelope
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a e) 2
  exact hRay.trans
    (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun e _he => hEach e))
      (by norm_num : (0 : ℝ) ≤ 1 / 2))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
