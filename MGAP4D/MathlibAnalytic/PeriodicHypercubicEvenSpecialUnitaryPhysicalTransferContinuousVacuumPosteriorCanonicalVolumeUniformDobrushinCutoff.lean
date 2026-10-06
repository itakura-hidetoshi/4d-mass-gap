import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorCanonicalVolumeUniformDobrushin
import Mathlib.Tactic

/-!
# Positive volume-uniform posterior Dobrushin interval

PR #5195 gives the actual canonical posterior refined influence the explicit
volume-independent coefficient

  alpha_bar(s,beta)
    = 18 * q_local(beta)
      + [2 Mbar(s,beta) / exp(-8 beta)] * shellMassBar(s),

for every fixed exponential scale s > 8.

The scalar ingredients satisfy

  q_local(0) = 0,
  Mbar(s,0) = 0,

and both are continuous at beta = 0.  Therefore alpha_bar(s,0) = 0 and
alpha_bar(s,.) is continuous at zero.  Intersecting a small continuity
neighborhood with the already-authoritative canonical half-barrier interval
produces a strictly positive cutoff, depending only on s, such that

  alpha_bar(s,beta) < 1

for every 0 <= beta below the cutoff.

Consequently, on that interval the literal continuous-vacuum posterior
one-link conditionals carry strict Dobrushin data uniformly in the finite
volume H and rank N.

This is a volume-uniform positive-coupling posterior Dobrushin theorem.  It
does not identify random-scan update time with Euclidean physical time, prove a
spacing-scaled continuum generator limit, close H1-D5 exact descent, or prove
the complete four-dimensional Yang--Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical posterior influence prefactor is continuous at zero
coupling. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
        s) 0 := by
  have hM :
      ContinuousAt
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s) 0 :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
      s
  have hExp :
      ContinuousAt (fun beta : ℝ => Real.exp (-8 * beta)) 0 := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
  exact
    (continuousAt_const.mul hM).div hExp
      (by norm_num [Real.exp_ne_zero])

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
        s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor]

/-- The H- and N-independent actual posterior Dobrushin coefficient is
continuous at zero coupling. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s) 0 := by
  have hLocal :
      ContinuousAt
        (fun beta : ℝ =>
          18 *
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence
              beta) 0 :=
    continuousAt_const.mul
      continuous_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDirectOneSourceInfluence.continuousAt
  have hRemote :
      ContinuousAt
        (fun beta : ℝ =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
              s beta *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
              s) 0 :=
    (continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapInfluencePrefactor
      s).mul continuousAt_const
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
  exact hLocal.add hRemote

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient]

/-- For every fixed exponential scale s > 8 there is a positive, H- and
N-independent coupling interval on which the actual posterior Dobrushin
coefficient is strictly below one.  The interval is chosen inside the
canonical half-barrier interval required by the actual-response construction. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
    (s : ℝ)
    (_hs : 8 < s) :
    ∃ cutoff : ℝ,
      0 < cutoff ∧
      cutoff ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s ∧
      ∀ beta : ℝ,
        0 ≤ beta →
        beta ≤ cutoff →
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
            s beta < 1 := by
  let alpha : ℝ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
      s
  have hAt : ContinuousAt alpha 0 := by
    simpa [alpha] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s
  rw [Metric.continuousAt_iff] at hAt
  obtain ⟨delta, hDelta, hControl⟩ :=
    hAt 1 (by norm_num)
  let baseCutoff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
      s
  have hBasePos : 0 < baseCutoff := by
    dsimp [baseCutoff]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_pos
        s
  let cutoff := min (delta / 2) baseCutoff
  refine ⟨cutoff, ?_, ?_, ?_⟩
  · dsimp [cutoff]
    exact lt_min (by positivity) hBasePos
  · dsimp [cutoff]
    exact min_le_right _ _
  · intro beta hbeta hbetaCutoff
    by_cases hZero : beta = 0
    · subst beta
      simp
    · have hBetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hZero)
      have hBetaHalfDelta :
          beta ≤ delta / 2 := by
        exact hbetaCutoff.trans (by
          dsimp [cutoff]
          exact min_le_left _ _)
      have hBetaDelta : beta < delta := by
        linarith
      have hDist : dist beta 0 < delta := by
        rw [Real.dist_eq]
        simp [abs_of_pos hBetaPos]
        exact hBetaDelta
      have hImage := hControl hDist
      have hAlphaZero : alpha 0 = 0 := by
        simp [alpha]
      rw [hAlphaZero, Real.dist_eq, sub_zero] at hImage
      exact (le_abs_self (alpha beta)).trans_lt hImage

/-- Canonical positive volume-uniform posterior Dobrushin cutoff. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
    (s : ℝ)
    (hs : 8 < s) : ℝ :=
  Classical.choose
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
      s hs)

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_pos
    (s : ℝ)
    (hs : 8 < s) :
    0 <
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
        s hs :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
      s hs)).1

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_le_halfBarrierCutoff
    (s : ℝ)
    (hs : 8 < s) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
        s hs ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
        s :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
      s hs)).2.1

theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_coefficient_lt_one
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
        s beta < 1 :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
      s hs)).2.2 beta hbeta hbetaCutoff

/-- On the canonical positive cutoff, every finite-volume/rank literal
continuous-vacuum posterior carries strict Dobrushin data with the same scalar
coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinData
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 8 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hbetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff
          s hs)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorDobrushinMatrixData
      H N hN beta hbeta B := by
  have hHalfBarrier :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hbetaCutoff.trans
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_le_halfBarrierCutoff
        s hs)
  have hStrict :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformCoefficient
          s beta < 1 :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapUniformDobrushinCutoff_coefficient_lt_one
      s hs beta hbeta hbetaCutoff
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapDobrushinData
      H N hN s hs beta hbeta hHalfBarrier hStrict B

end

end MathlibAnalytic
end MGAP4D
