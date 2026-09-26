import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureInfluence
import Mathlib.Tactic

/-!
# Volume-independent bootstrap envelope for the actual canonical coefficient

The exact canonical weighted response coefficient `M_can(H,N,center,beta,s)`
is finite-volume dependent, although PRs #4605--#4638 already prove

  * `M_can <= Phi(M_can)`;
  * `M_can < 1/2` on the canonical half-barrier interval.

The bootstrap map

  Phi(M)
    = 20 s^2 exp(16 beta) eta_R(beta)
      + eta_R(beta) exp(16 beta) / (1 - c_pf(M))

is monotone in `M` whenever the larger denominator remains positive.
Therefore

  M_can <= Phi(M_can) <= Phi(1/2).

The right endpoint `Phi(1/2)` is exactly the existing
`CanonicalFixedRightHalfBarrierBootstrapMap`: it is volume/rank/center
independent, continuous at beta=0, and vanishes exactly at beta=0.

This file packages the induced pin-free physical coefficient

  c_bar(s,beta) := c_pf(beta,s,Phi(1/2))

and proves that the actual canonical physical coefficient is bounded by
`c_bar`.  Unlike the older coarse half-barrier envelope
`c_pf(beta,s,1/2)`, the new envelope vanishes at beta=0.  This is the scalar
quantity needed to combine the PR #4838 volume-uniform reciprocal-shell mass
with a genuine small-coupling row contraction.

No response profile, probability law, cutoff, or finite-volume object is
redefined.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

local instance canonicalFixedRightBootstrapEnvelopeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The pin-free physical coefficient is monotone in the response coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient_mono_responseCoefficient
    (beta s responseCoefficient₁ responseCoefficient₂ : ℝ)
    (hLe : responseCoefficient₁ ≤ responseCoefficient₂) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient₁ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient₂ := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
  exact
    add_le_add_left
      (mul_le_mul_of_nonneg_left hLe (Real.exp_pos (16 * beta)).le)
      _

/-- On the region where the larger pin-free denominator is positive, the full
canonical bootstrap map is monotone in the response coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient_mono_responseCoefficient
    (beta s responseCoefficient₁ responseCoefficient₂ : ℝ)
    (hbeta : 0 ≤ beta)
    (hLe : responseCoefficient₁ ≤ responseCoefficient₂)
    (hCoefficient₂LtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient₂ < 1) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
        beta s responseCoefficient₁ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
        beta s responseCoefficient₂ := by
  let etaR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
      beta
  let c₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
      beta s responseCoefficient₁
  let c₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
      beta s responseCoefficient₂
  have hc₁₂ : c₁ ≤ c₂ := by
    simpa [c₁, c₂] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient_mono_responseCoefficient
        beta s responseCoefficient₁ responseCoefficient₂ hLe
  have hc₁LtOne : c₁ < 1 :=
    hc₁₂.trans_lt (by simpa [c₂] using hCoefficient₂LtOne)
  have hDen₁ : 0 < 1 - c₁ := sub_pos.mpr hc₁LtOne
  have hDen₂ : 0 < 1 - c₂ :=
    sub_pos.mpr (by simpa [c₂] using hCoefficient₂LtOne)
  have hInv :
      (1 - c₁)⁻¹ ≤ (1 - c₂)⁻¹ := by
    exact
      (inv_le_inv₀ hDen₁ hDen₂).2
        (by linarith [hc₁₂])
  have hEtaR :
      0 ≤ etaR := by
    simpa [etaR] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence_nonneg
        beta hbeta
  have hFactor :
      0 ≤ etaR * Real.exp (16 * beta) :=
    mul_nonneg hEtaR (Real.exp_pos _).le
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
  change
    20 * s ^ 2 * Real.exp (16 * beta) * etaR +
          etaR * Real.exp (16 * beta) * (1 - c₁)⁻¹ ≤
      20 * s ^ 2 * Real.exp (16 * beta) * etaR +
          etaR * Real.exp (16 * beta) * (1 - c₂)⁻¹
  exact
    add_le_add_left
      (mul_le_mul_of_nonneg_left hInv hFactor)
      _

/-- The actual exact canonical weighted response coefficient is bounded by the
existing volume-independent half-barrier bootstrap map. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_le_halfBarrierBootstrapMap
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
        H N hN beta hbeta s center ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s beta := by
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
      H N hN beta hbeta s center
  let barrier :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier
  have hMLt : M < barrier := by
    simpa [M, barrier] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_lt_halfBarrier_of_nonneg_le_cutoff
        H N hN s hs center beta hbeta hcut
  have hHalfCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s barrier < 1 := by
    simpa [
      barrier,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
        s beta hbeta hcut).2
  have hActualCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s M < 1 := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient_mono_responseCoefficient
        beta s M barrier hMLt.le).trans_lt hHalfCoefficientLtOne
  have hBootstrap :
      M ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
          beta s M := by
    simpa [M] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_le_bootstrap
        H N hN beta hbeta s hs center hActualCoefficientLtOne
  have hBootstrapMono :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
          beta s M ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient
          beta s barrier :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient_mono_responseCoefficient
      beta s M barrier hbeta hMLt.le hHalfCoefficientLtOne
  exact
    (hBootstrap.trans hBootstrapMono).trans_eq (by
      rfl)

/-- Volume-independent pin-free coefficient generated by the bootstrap image
of the half barrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
    (s beta : ℝ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
    beta s
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s beta)

/-- The bootstrap-envelope coefficient is nonnegative on the canonical
half-barrier interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient_nonneg
    (s beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
        s beta := by
  let barrier :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier
  have hHalfCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s barrier < 1 := by
    simpa [
      barrier,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_nonneg_lt_one
        s beta hbeta hcut).2
  have hMapNonneg :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseBootstrapCoefficient_nonneg
        beta s barrier hbeta
        (by
          dsimp [barrier]
          norm_num [
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier])
        hHalfCoefficientLtOne
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient_nonneg
      beta s
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s beta)
      hbeta hMapNonneg

/-- The new volume-independent envelope vanishes exactly at zero coupling. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
        s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient]

/-- The volume-independent envelope is continuous at the decoupled point. -/
theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
        s)
      0 := by
  let eta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
  let Mbar :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
      s
  have hEta : ContinuousAt eta 0 := by
    simpa [eta] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_zero
  have hMbar : ContinuousAt Mbar 0 := by
    simpa [Mbar] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
        s
  have hExp : ContinuousAt (fun beta : ℝ => Real.exp (16 * beta)) 0 := by
    fun_prop
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
  change
    ContinuousAt
      (fun beta : ℝ =>
        18 * eta beta * s ^ 2 +
          Real.exp (16 * beta) * Mbar beta)
      0
  exact
    (((continuousAt_const.mul hEta).mul continuousAt_const).add
      (hExp.mul hMbar))

/-- The actual finite-volume canonical pin-free coefficient is bounded by the
volume-independent bootstrap envelope. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightActualPinFreeCoefficient_le_bootstrapEnvelope
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 ≤ s)
    (center : PeriodicHypercubicEvenSpatialSliceLink H)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
          H N hN beta hbeta s center) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
        s beta := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient_mono_responseCoefficient
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient_le_halfBarrierBootstrapMap
      H N hN s hs center beta hbeta hcut

/-- The bootstrap envelope itself remains strictly below one on the canonical
half-barrier interval. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient_lt_one
    (s beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
        s beta < 1 := by
  by_cases hz : beta = 0
  · subst beta
    simp
  · have hbetaPos : 0 < beta :=
      lt_of_le_of_ne hbeta (Ne.symm hz)
    have hSpec :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_spec
        s beta hbetaPos hcut
    have hMapLe :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
            s beta ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier :=
      hSpec.2.le
    have hMono :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient_mono_responseCoefficient
        beta s
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierBootstrapMap
          s beta)
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier
        hMapLe
    have hHalf :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier < 1 := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient] using
        hSpec.1
    exact
      (by
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient] using hMono).trans_lt
        hHalf

end

end MGAP4D.MathlibAnalytic
