import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightWeightedCoefficient
import Mathlib.Tactic

/-!
# Canonical fixed-right high-temperature half barrier

The exact canonical weighted response coefficient is now an actual scalar
`M_can`, with `M_can(0) = 0`, and satisfies the conditional bootstrap
inequality `M_can <= Phi(M_can)` whenever its induced pin-free coefficient is
strictly below one.

This file isolates the next purely scalar part of the argument.  We fix the
numerical barrier `1/2` and prove two facts.

1. The elementary coefficient functions evaluated at the barrier are continuous
   at zero coupling, and at zero they satisfy
     `c_pf(0,s,1/2) = 1/2 < 1`
   and
     `Phi(0,s,1/2) = 0 < 1/2`.
   Hence there is a strictly positive coupling cutoff, depending on the chosen
   exponential scale `s` but not on the finite volume, below which both strict
   barrier inequalities hold.

2. At any coupling satisfying those two strict inequalities, the actual
   canonical coefficient cannot equal `1/2`: equality would activate the
   merged scalar bootstrap theorem and force `1/2 <= Phi(1/2) < 1/2`.

No continuity of `M_can` is assumed here.  Therefore this is a barrier
exclusion theorem, not yet the final continuation step.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Fixed numerical barrier for the canonical weighted response coefficient. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier :
    ℝ :=
  1 / 2

/-- Pin-free physical weighted coefficient evaluated at the fixed half
barrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
    (s beta : ℝ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
    beta s
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier

/-- Full canonical response bootstrap map evaluated at the fixed half
barrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
    (s beta : ℝ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
    beta s
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_zero :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      0 = 0 := by
  norm_num [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence_zero :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
      0 = 0 := by
  norm_num [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence]

/-- The coarse local background-update Harnack influence is continuous at the
decoupled point. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_zero :
    ContinuousAt
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
      0 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
  dsimp
  have hK :
      Continuous (fun beta : ℝ => (Real.exp (32 * beta)) ^ 2) := by
    fun_prop
  exact
    (continuous_const.mul
      ((hK.sub continuous_const).div
        (hK.add continuous_const)
        (fun beta => by
          dsimp
          have hsq : 0 < (Real.exp (32 * beta)) ^ 2 :=
            pow_pos (Real.exp_pos _) 2
          exact ne_of_gt (by linarith)))).continuousAt

/-- The fixed-right boundary-update Harnack influence is continuous at the
decoupled point. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence_zero :
    ContinuousAt
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
      0 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
  dsimp
  have hK :
      Continuous (fun beta : ℝ => (Real.exp (8 * beta)) ^ 2) := by
    fun_prop
  exact
    (continuous_const.mul
      ((hK.sub continuous_const).div
        (hK.add continuous_const)
        (fun beta => by
          dsimp
          have hsq : 0 < (Real.exp (8 * beta)) ^ 2 :=
            pow_pos (Real.exp_pos _) 2
          exact ne_of_gt (by linarith)))).continuousAt

/-- The pin-free coefficient at the half barrier is continuous at zero
coupling. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s) 0 := by
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
  have hEta : ContinuousAt eta 0 := by
    simpa [eta] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_zero
  have hExp : ContinuousAt (fun beta : ℝ => Real.exp (16 * beta)) 0 := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
  change ContinuousAt
    (fun beta : ℝ =>
      18 * eta beta * s ^ 2 +
        Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier) 0
  exact
    (((continuousAt_const.mul hEta).mul continuousAt_const).add
      (hExp.mul continuousAt_const))

/-- The full bootstrap map at the half barrier is continuous at zero coupling.
The reciprocal denominator is nonzero there because the pin-free coefficient
equals one half. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s) 0 := by
  let etaR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
  let c :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s
  have hEtaR : ContinuousAt etaR 0 := by
    simpa [etaR] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence_zero
  have hC : ContinuousAt c 0 := by
    simpa [c] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s
  have hExp : ContinuousAt (fun beta : ℝ => Real.exp (16 * beta)) 0 := by
    fun_prop
  have hCZero : c 0 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
    simp [
      c,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier]
  have hDenNe : 1 - c 0 ≠ 0 := by
    rw [hCZero]
    norm_num [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier]
  have hInv : ContinuousAt (fun beta : ℝ => (1 - c beta)⁻¹) 0 :=
    (continuousAt_const.sub hC).inv₀ hDenNe
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
  change ContinuousAt
    (fun beta : ℝ =>
      20 * s ^ 2 * Real.exp (16 * beta) * etaR beta +
        etaR beta * Real.exp (16 * beta) * (1 - c beta)⁻¹) 0
  exact
    (((continuousAt_const.mul hExp).mul hEtaR).add
      ((hEtaR.mul hExp).mul hInv))

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s 0 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
      s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient]

/-- Elementary zero-coupling continuity yields a strictly positive,
volume-independent interval on which both half-barrier inequalities hold. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
    (s : ℝ) :
    ∃ couplingCutoff : ℝ,
      0 < couplingCutoff ∧
      ∀ beta : ℝ,
        0 < beta → beta ≤ couplingCutoff →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
              s beta < 1 ∧
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
                s beta <
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
      s
  let F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
      s
  have hCContinuous : ContinuousAt C 0 := by
    simpa [C] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s
  have hFContinuous : ContinuousAt F 0 := by
    simpa [F] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s
  rw [Metric.continuousAt_iff] at hCContinuous hFContinuous
  obtain ⟨deltaC, hDeltaC, hControlC⟩ :=
    hCContinuous (1 / 2) (by norm_num)
  obtain ⟨deltaF, hDeltaF, hControlF⟩ :=
    hFContinuous (1 / 2) (by norm_num)
  let delta := min deltaC deltaF
  have hDelta : 0 < delta := by
    dsimp [delta]
    exact lt_min hDeltaC hDeltaF
  refine ⟨delta / 2, by positivity, ?_⟩
  intro beta hBeta hBetaCutoff
  have hCutLtDelta : delta / 2 < delta := by linarith
  have hBetaDelta : beta < delta :=
    lt_of_le_of_lt hBetaCutoff hCutLtDelta
  have hBetaDeltaC : beta < deltaC :=
    lt_of_lt_of_le hBetaDelta (min_le_left deltaC deltaF)
  have hBetaDeltaF : beta < deltaF :=
    lt_of_lt_of_le hBetaDelta (min_le_right deltaC deltaF)
  have hDistanceC : dist beta 0 < deltaC := by
    rw [Real.dist_eq]
    simp [abs_of_pos hBeta]
    exact hBetaDeltaC
  have hDistanceF : dist beta 0 < deltaF := by
    rw [Real.dist_eq]
    simp [abs_of_pos hBeta]
    exact hBetaDeltaF
  have hImageC := hControlC hDistanceC
  have hImageF := hControlF hDistanceF
  have hCAbs : |C beta - C 0| < 1 / 2 := by
    simpa [Real.dist_eq] using hImageC
  have hFAbs : |F beta - F 0| < 1 / 2 := by
    simpa [Real.dist_eq] using hImageF
  have hCUpper : C beta - C 0 < 1 / 2 :=
    lt_of_le_of_lt (le_abs_self (C beta - C 0)) hCAbs
  have hFUpper : F beta - F 0 < 1 / 2 :=
    lt_of_le_of_lt (le_abs_self (F beta - F 0)) hFAbs
  have hCZero :
      C 0 =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
    simp [C]
  have hFZero : F 0 = 0 := by
    simp [F]
  constructor
  · rw [hCZero] at hCUpper
    norm_num [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier] at hCUpper ⊢
    linarith
  · rw [hFZero] at hFUpper
    simpa [
      F,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier] using
      hFUpper

/-- Canonical elementary half-barrier cutoff for the chosen exponential
weight scale. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
    (s : ℝ) : ℝ :=
  Classical.choose
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
      s)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_pos
    (s : ℝ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
        s :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
      s)).1

/-- Throughout the selected elementary high-temperature interval, the
half-barrier has a strict pin-free denominator and the bootstrap map sends it
strictly inside itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_spec
    (s beta : ℝ)
    (hBeta : 0 < beta)
    (hBetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta < 1 ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
      s)).2
    beta hBeta hBetaCutoff

/-- If the elementary half-barrier inequalities hold at one coupling, the
actual canonical weighted response coefficient cannot sit exactly on the
barrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_ne_halfBarrier
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (hBarrierCoefficient :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        s beta < 1)
    (hBarrierMap :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center ≠
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
  intro hEq
  have hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
            H N hN beta hbeta s center) < 1 := by
    simpa [
      hEq,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient] using
      hBarrierCoefficient
  have hBootstrap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_le_bootstrap
      H N hN beta hbeta s hs center hCoefficientLtOne
  rw [hEq] at hBootstrap
  have hMap :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap] using
      hBootstrap
  exact (not_le_of_gt hBarrierMap) hMap

/-- Therefore, at every positive coupling below the selected volume-independent
cutoff, the exact canonical coefficient is excluded from the half barrier in
every finite volume and at every center. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_ne_halfBarrier_of_le_cutoff
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 ≤ s)
    (beta : ℝ)
    (hBeta : 0 < beta)
    (hBetaCutoff :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hBeta.le s center ≠
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier := by
  rcases
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_spec
      s beta hBeta hBetaCutoff with
    ⟨hCoefficient, hMap⟩
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_ne_halfBarrier
      H N hN beta hBeta.le s hs center hCoefficient hMap

end

end MathlibAnalytic
end MGAP4D
