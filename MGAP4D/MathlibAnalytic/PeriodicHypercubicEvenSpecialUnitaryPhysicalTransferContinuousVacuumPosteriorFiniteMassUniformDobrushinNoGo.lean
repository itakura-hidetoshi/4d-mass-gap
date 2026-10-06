import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorFiniteMassCouplingAwayFromZero
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Finite posterior mass scaling is impossible inside the strict uniform Dobrushin interval

PRs #5203--#5206 isolate the necessary behavior of any finite positive
posterior full-sweep generator-scaling certificate.  In particular,

  alpha_bar(s,beta_n) -> 1,

while every beta_n is constrained by the certificate to the canonical closed
uniform Dobrushin interval

  0 <= beta_n <= beta_cut(s).

On that interval the same canonical coefficient is pointwise strictly below
one.  The remaining issue is whether the strictness could nevertheless be lost
along a sequence approaching the boundary.

This file closes that loophole.  The elementary Harnack and half-barrier
bootstrap scalars are continuous at every point where their reciprocal
denominator is strict.  Hence alpha_bar(s,.) is continuous at every point of
the canonical closed uniform Dobrushin interval.  Compactness then extracts a
convergent subsequence beta_(phi n) -> beta_*.  Continuity gives

  alpha_bar(s,beta_(phi n)) -> alpha_bar(s,beta_*),

whereas finite generator scaling gives the same subsequence the limit one.
Uniqueness of limits forces alpha_bar(s,beta_*) = 1, contradicting the strict
Dobrushin theorem at beta_*.

Thus the current proof-relevant finite-mass generator-scaling certificate is
empty: a finite positive continuum mass cannot be obtained while the entire
coupling sequence remains inside this canonical strict-Dobrushin regime.

This is a no-go theorem for that specific posterior-sweep scaling route.  It
does not identify posterior sweep time with Euclidean transfer time, construct
a critical coupling outside the strict interval, close H1-D5 exact descent, or
prove the complete four-dimensional Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology

noncomputable section

private theorem continuous_backgroundUpdateHarnackInfluence :
    Continuous
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
  dsimp
  have hK :
      Continuous (fun beta : ℝ => (Real.exp (32 * beta)) ^ 2) := by
    fun_prop
  exact
    continuous_const.mul
      ((hK.sub continuous_const).div
        (hK.add continuous_const)
        (fun beta => by
          dsimp
          have hsq : 0 < (Real.exp (32 * beta)) ^ 2 :=
            pow_pos (Real.exp_pos _) 2
          exact ne_of_gt (by linarith)))

private theorem continuous_fixedRightBoundaryUpdateHarnackInfluence :
    Continuous
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
  dsimp
  have hK :
      Continuous (fun beta : ℝ => (Real.exp (8 * beta)) ^ 2) := by
    fun_prop
  exact
    continuous_const.mul
      ((hK.sub continuous_const).div
        (hK.add continuous_const)
        (fun beta => by
          dsimp
          have hsq : 0 < (Real.exp (8 * beta)) ^ 2 :=
            pow_pos (Real.exp_pos _) 2
          exact ne_of_gt (by linarith)))

private theorem continuous_halfBarrierPinFreeCoefficient
    (s : ℝ) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s) := by
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
  have hEta : Continuous eta := by
    simpa [eta] using continuous_backgroundUpdateHarnackInfluence
  have hExp :
      Continuous (fun beta : ℝ => Real.exp (16 * beta)) := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
  change
    Continuous
      (fun beta : ℝ =>
        18 * eta beta * s ^ 2 +
          Real.exp (16 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier)
  exact
    (((continuous_const.mul hEta).mul continuous_const).add
      (hExp.mul continuous_const))

private theorem continuousAt_halfBarrierBootstrapMap_of_pinFree_lt_one
    (s beta : ℝ)
    (hPinFree :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          s beta < 1) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s) beta := by
  let etaR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
  let c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s
  have hEtaR : ContinuousAt etaR beta := by
    exact continuous_fixedRightBoundaryUpdateHarnackInfluence.continuousAt
  have hC : ContinuousAt c beta := by
    simpa [c] using (continuous_halfBarrierPinFreeCoefficient s).continuousAt
  have hExp :
      ContinuousAt (fun x : ℝ => Real.exp (16 * x)) beta := by
    fun_prop
  have hc : c beta < 1 := by
    simpa [c] using hPinFree
  have hDenNe : 1 - c beta ≠ 0 :=
    ne_of_gt (sub_pos.mpr hc)
  have hInv :
      ContinuousAt (fun x : ℝ => (1 - c x)⁻¹) beta :=
    (continuousAt_const.sub hC).inv₀ hDenNe
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
  change
    ContinuousAt
      (fun x : ℝ =>
        20 * s ^ 2 * Real.exp (16 * x) * etaR x +
          etaR x * Real.exp (16 * x) * (1 - c x)⁻¹)
      beta
  exact
    (((continuousAt_const.mul hExp).mul hEtaR).add
      ((hEtaR.mul hExp).mul hInv))

private theorem continuousAt_bootstrapInfluencePrefactor_of_mem_uniformDobrushinInterval
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
        s) beta := by
  have hHalfBarrier :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hbetaCutoff.trans
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_le_halfBarrierCutoff
        s hs)
  have hMap :
      ContinuousAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s) beta := by
    by_cases hZero : beta = 0
    · subst beta
      exact
        continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s
    · have hbetaPos : 0 < beta :=
        lt_of_le_of_ne hbeta (Ne.symm hZero)
      have hPinFree :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_spec
          s beta hbetaPos hHalfBarrier).1
      exact
        continuousAt_halfBarrierBootstrapMap_of_pinFree_lt_one
          s beta hPinFree
  have hExp :
      ContinuousAt (fun x : ℝ => Real.exp (-8 * x)) beta := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
  exact
    (continuousAt_const.mul hMap).div hExp
      (Real.exp_ne_zero (-8 * beta))

/-- The actual H- and N-independent posterior Dobrushin coefficient is
continuous at every point of the canonical closed strict-Dobrushin interval,
not merely at the decoupled endpoint beta = 0. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient_of_mem_uniformDobrushinInterval
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s) beta := by
  have hLocal :
      ContinuousAt
        (fun x : ℝ =>
          18 *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
              x)
        beta :=
    continuousAt_const.mul
      continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence.continuousAt
  have hRemote :
      ContinuousAt
        (fun x : ℝ =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
              s x *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
              s)
        beta :=
    (continuousAt_bootstrapInfluencePrefactor_of_mem_uniformDobrushinInterval
      s hs beta hbeta hbetaCutoff).mul continuousAt_const
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
  exact hLocal.add hRemote

namespace
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling

variable
    {s : ℝ}
    {hs : 8 < s}
    {latticeSpacing beta : ℕ → ℝ}

/-- No finite positive generator-scaling certificate can keep its entire
coupling sequence inside the canonical closed strict-Dobrushin interval.

The contradiction is compactness-based: a bounded coupling sequence has a
convergent subsequence, continuity transports that subsequence through
alpha_bar, finite-mass scaling forces the transported limit to one, while the
canonical strict-Dobrushin theorem keeps the cluster-point value below one. -/
theorem impossible_inside_uniformDobrushinInterval
    (A :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) :
    False := by
  let cutoff : ℝ :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
      s hs
  let alpha : ℝ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
      s
  have hBetaMem :
      ∀ n : ℕ, beta n ∈ Set.Icc (0 : ℝ) cutoff := by
    intro n
    exact
      ⟨A.beta_nonneg n,
        by
          simpa [cutoff] using A.beta_le_cutoff n⟩
  have hCompact :
      IsCompact (Set.Icc (0 : ℝ) cutoff) :=
    isCompact_Icc
  obtain ⟨betaStar, hBetaStar, phi, hPhiMono, hBetaSubsequence⟩ :=
    hCompact.tendsto_subseq hBetaMem
  have hBetaStarNonneg : 0 ≤ betaStar :=
    hBetaStar.1
  have hBetaStarCutoff : betaStar ≤ cutoff :=
    hBetaStar.2
  have hBetaStarCutoffRaw :
      betaStar ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs := by
    simpa [cutoff] using hBetaStarCutoff
  have hAlphaContinuous :
      ContinuousAt alpha betaStar := by
    simpa [alpha] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient_of_mem_uniformDobrushinInterval
        s hs betaStar hBetaStarNonneg hBetaStarCutoffRaw
  have hAlphaSubsequenceStar :
      Tendsto
        (fun n : ℕ => alpha (beta (phi n)))
        atTop
        (nhds (alpha betaStar)) := by
    have h :=
      hAlphaContinuous.tendsto.comp hBetaSubsequence
    simpa [Function.comp_def] using h
  have hAlphaFull :
      Tendsto
        (fun n : ℕ => alpha (beta n))
        atTop
        (nhds 1) := by
    simpa [alpha] using A.coefficient_tendsto_one
  have hAlphaSubsequenceOne :
      Tendsto
        (fun n : ℕ => alpha (beta (phi n)))
        atTop
        (nhds 1) := by
    have h :=
      hAlphaFull.comp hPhiMono.tendsto_atTop
    simpa [Function.comp_def] using h
  have hAlphaStar :
      alpha betaStar = 1 :=
    tendsto_nhds_unique hAlphaSubsequenceStar hAlphaSubsequenceOne
  have hStrictRaw :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_coefficient_lt_one
      s hs betaStar hBetaStarNonneg hBetaStarCutoffRaw
  have hStrict : alpha betaStar < 1 := by
    simpa [alpha] using hStrictRaw
  rw [hAlphaStar] at hStrict
  exact (lt_irrefl (1 : ℝ)) hStrict

/-- Type-level form of the no-go theorem: the current finite positive posterior
full-sweep generator-scaling certificate has no inhabitants. -/
theorem not_nonempty_inside_uniformDobrushinInterval :
    ¬ Nonempty
      (PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling
        s hs latticeSpacing beta) := by
  rintro ⟨A⟩
  exact A.impossible_inside_uniformDobrushinInterval

end
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalUniformFullSweepGeneratorScaling

end

end MathlibAnalytic
end MGAP4D
