import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitarySingleLinkTVInfluence
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkFiberInvariance
import Mathlib.Tactic

/-!
# Sparse conditional-TV certificate for periodic SU(N) Wilson Gibbs laws

The previous layer proves the sharp active-neighbor one-link TV bound for the
actual compact periodic `SU(N)` Wilson source.  This file completes the sparse
finite-volume influence certificate without importing any historical finite-gauge
Dobrushin stack.

* If the changed source is the resampled target itself, exact off-target fiber
  invariance makes the two conditional densities identical, hence TV is zero.
* If target and a distinct source are not plaquette neighbors, their shared
  plaquette set is empty, so the current shared-plaquette TV theorem gives TV
  at most zero.
* Active neighbors are controlled by the already-canonical `q(beta)` bound.

Thus the sparse influence from the previous layer bounds the exact conditional
TV for every source link.  Under the explicit row threshold it also gives a
strict finite-volume Dobrushin row criterion.  No claim is made that the
factorial continuum coupling sequence satisfies that threshold, and no update
chain time is identified with physical OS Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Off-target fiber agreement makes the real normalized one-link Haar densities
identical. -/
theorem periodicHypercubicSpecialUnitary_singleLinkRealConditionalDensity_eq_of_agreeOffTarget
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (target : PeriodicHypercubicEdge n)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.AgreeOffLink A B target) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).singleLinkRealConditionalDensity A target =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkRealConditionalDensity B target := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  funext g
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkRealConditionalDensity
  rw [continuous_compact_oriented_singleLinkBoltzmannFactor_eq_of_agreeOffLink
      C A B target hAgree g,
    continuous_compact_oriented_singleLinkPartitionFunction_eq_of_agreeOffLink
      C A B target hAgree]

/-- Changing only the link that is itself being resampled leaves the exact
one-link conditional TV equal to zero. -/
theorem periodicHypercubicSpecialUnitary_diagonalSingleLinkConditionalTotalVariation_eq_zero
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (target : PeriodicHypercubicEdge n)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.AgreeOffLink A B target) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).singleLinkConditionalTotalVariation A B target = 0 := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  have hDensity :=
    periodicHypercubicSpecialUnitary_singleLinkRealConditionalDensity_eq_of_agreeOffTarget
      n N hN beta hBeta A B target hAgree
  change C.singleLinkConditionalTotalVariation A B target = 0
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalTotalVariation
  rw [hDensity]
  simp

/-- A distinct source outside the concrete active-neighbor set has no shared
plaquette with the target. -/
theorem periodicHypercubicSpecialUnitary_sharedPlaquettes_eq_empty_of_inactive
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n)
    (hInactive : source ∉ periodicHypercubicActiveNeighbors n target)
    (hNe : source ≠ target) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.sharedPlaquettes target source = ∅ := by
  have hConcrete :
      periodicHypercubicSharedPlaquettes n target source = ∅ := by
    classical
    ext p
    constructor
    · intro hp
      exfalso
      apply hInactive
      apply (periodicHypercubic_mem_activeNeighbors_iff_for_compactSU
        n target source).mpr
      have hp' := (periodicHypercubic_mem_sharedPlaquettes_iff
        n target source p).mp hp
      exact ⟨⟨p, hp'.1, hp'.2⟩, hNe⟩
    · simp
  rw [periodicHypercubicSpecialUnitary_sharedPlaquettes_eq_current
    n N hN beta hBeta target source]
  exact hConcrete

/-- A distinct inactive source has exact one-link conditional TV at most zero. -/
theorem periodicHypercubicSpecialUnitary_inactiveSingleLinkConditionalTotalVariation_le_zero
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (target source : PeriodicHypercubicEdge n)
    (hInactive : source ∉ periodicHypercubicActiveNeighbors n target)
    (hNe : source ≠ target)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.AgreeOffLink A B source) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).singleLinkConditionalTotalVariation A B target ≤ 0 := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  have hShared :=
    periodicHypercubicSpecialUnitary_sharedPlaquettes_eq_empty_of_inactive
      n N hN beta hBeta target source hInactive hNe
  have hTV :=
    continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_shared
      C 2 (by norm_num)
      (periodicHypercubicSpecialUnitary_plaquetteEnergy_le_two_current
        n N hN beta hBeta)
      A B target source hAgree
  rw [hShared] at hTV
  simpa using hTV

/-- The sparse active-neighbor influence is nonnegative. -/
theorem periodicHypercubicSpecialUnitarySparseActiveTVInfluence_nonneg
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n) :
    0 ≤ periodicHypercubicSpecialUnitarySparseActiveTVInfluence
      n beta target source := by
  classical
  unfold periodicHypercubicSpecialUnitarySparseActiveTVInfluence
  split_ifs
  · exact periodicHypercubicSpecialUnitaryActiveTVMajorant_nonneg beta hBeta
  · exact le_rfl

/-- The sparse influence has zero diagonal. -/
theorem periodicHypercubicSpecialUnitarySparseActiveTVInfluence_diagonal_zero
    (n : ℕ) [NeZero n]
    (beta : ℝ)
    (target : PeriodicHypercubicEdge n) :
    periodicHypercubicSpecialUnitarySparseActiveTVInfluence
      n beta target target = 0 := by
  classical
  have hInactive : target ∉ periodicHypercubicActiveNeighbors n target := by
    intro h
    exact
      ((periodicHypercubic_mem_activeNeighbors_iff_for_compactSU
        n target target).mp h).2 rfl
  simp [periodicHypercubicSpecialUnitarySparseActiveTVInfluence, hInactive]

/-- The sparse influence bounds the exact one-link conditional TV for every
source link.  This is the complete finite-volume one-site influence estimate. -/
theorem periodicHypercubicSpecialUnitary_singleLinkConditionalTotalVariation_le_sparseInfluence
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (target source : PeriodicHypercubicEdge n)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.AgreeOffLink A B source) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).singleLinkConditionalTotalVariation A B target ≤
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        n beta target source := by
  classical
  by_cases hActive : source ∈ periodicHypercubicActiveNeighbors n target
  · have hTV :=
      periodicHypercubicSpecialUnitary_activeSingleLinkConditionalTotalVariation_le
        n N hn hN beta hBeta A B target source hActive hAgree
    simpa [periodicHypercubicSpecialUnitarySparseActiveTVInfluence,
      periodicHypercubicSpecialUnitaryActiveTVMajorant, hActive] using hTV
  · by_cases hEq : source = target
    · subst source
      have hZero :=
        periodicHypercubicSpecialUnitary_diagonalSingleLinkConditionalTotalVariation_eq_zero
          n N hN beta hBeta A B target hAgree
      have hLe :
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta hBeta).singleLinkConditionalTotalVariation A B target ≤ 0 :=
        le_of_eq hZero
      simpa [periodicHypercubicSpecialUnitarySparseActiveTVInfluence,
        hActive] using hLe
    · have hTV :=
        periodicHypercubicSpecialUnitary_inactiveSingleLinkConditionalTotalVariation_le_zero
          n N hN beta hBeta A B target source hActive hEq hAgree
      simpa [periodicHypercubicSpecialUnitarySparseActiveTVInfluence,
        hActive] using hTV

/-- Under the explicit finite-volume threshold, the sparse influence both
majorizes every one-link conditional TV and has every row strictly below one. -/
theorem periodicHypercubicSpecialUnitary_sparseConditionalTVCertificate_of_threshold
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1) :
    (∀ (target source : PeriodicHypercubicEdge n)
      (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).base.Configuration),
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).base.AgreeOffLink A B source →
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).singleLinkConditionalTotalVariation A B target ≤
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence
          n beta target source) ∧
    (∀ target : PeriodicHypercubicEdge n,
      (∑ source : PeriodicHypercubicEdge n,
        periodicHypercubicSpecialUnitarySparseActiveTVInfluence
          n beta target source) < 1) := by
  constructor
  · intro target source A B hAgree
    exact
      periodicHypercubicSpecialUnitary_singleLinkConditionalTotalVariation_le_sparseInfluence
        n N hn hN beta hBeta A B target source hAgree
  · intro target
    exact
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence_rowSum_lt_one_of_threshold
        n beta hBeta hThreshold target

end

end MathlibAnalytic
end MGAP4D
