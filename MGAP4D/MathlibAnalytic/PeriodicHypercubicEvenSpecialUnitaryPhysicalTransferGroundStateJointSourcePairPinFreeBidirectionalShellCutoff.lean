import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairPinFreeOffDiagonalShellRow
import MGAP4D.MathlibAnalytic.FiniteNonnegativeInfluenceKernelBidirectionalSchurL2
import Mathlib.Tactic

/-!
# Volume-uniform bidirectional shell cutoff for the canonical pin-free kernel

PR #4838 gives a volume-independent off-diagonal reciprocal-weight mass
majorant for every fixed scale s > 8.  PR #4839 gives a volume/rank/center
independent physical coefficient envelope cbar(s,beta) which bounds the actual
canonical weighted coefficient and satisfies

  cbar(s,0) = 0.

This file combines those two ingredients.

Define

  shellMassBar(s)
    = 2 + 81 * (8/s) / (1 - 8/s),

and

  qShell(s,beta) = cbar(s,beta) * shellMassBar(s).

For fixed s > 8, qShell is continuous at beta=0 and qShell(s,0)=0.
Consequently there is a strictly positive coupling interval, chosen inside the
already-authoritative strict physical sweep interval, on which qShell < 1.

On that interval the ORIGINAL canonical pin-free physical-left kernel satisfies

  rowSum(target)    <= qShell(s,beta),
  columnSum(source) <= qShell(s,beta),

uniformly in H, N and the row/column index.  Therefore its L2 action obeys the
dimension-free Schur bound with coefficient qShell^2.

No response symmetry, source/target exchange, lattice-cardinality factor,
new response coefficient, or new physical law is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance pinFreeBidirectionalShellCutoffSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The positive-radius shell tail is nonnegative for s > 8. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant_nonneg
    (s : ℝ) (hs : 8 < s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant
        s := by
  let q : ℝ := 8 * s⁻¹
  have hsPos : 0 < s := by linarith
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact mul_nonneg (by norm_num) (inv_nonneg.mpr hsPos.le)
  have hq1 : q < 1 := by
    dsimp [q]
    simpa [div_eq_mul_inv] using (div_lt_one hsPos).2 hs
  have hInv0 : 0 ≤ (1 - q)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hq1.le)
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant
  change 0 ≤ 81 * q * (1 / (1 - q))
  rw [one_div]
  exact mul_nonneg (mul_nonneg (by norm_num) hq0) hInv0

/-- The explicit off-diagonal shell majorant is nonnegative for s > 8. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant_nonneg
    (s : ℝ) (hs : 8 < s) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
        s := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
  exact add_nonneg (by norm_num)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant_nonneg
      s hs)

/-- The off-diagonal shell majorant is at least one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant_one_le
    (s : ℝ) (hs : 8 < s) :
    1 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
        s := by
  have hTail :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant
          s :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeReciprocalExponentialWeightPositiveTailMajorant_nonneg
      s hs
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
  linarith

/-- Common volume-independent shell coefficient for the canonical pin-free
kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
    (s beta : ℝ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
      s beta *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
      s

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient_zero
    (s : ℝ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s 0 = 0 := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient]

theorem
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
    (s : ℝ) :
    ContinuousAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s)
      0 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
  exact
    (continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
      s).mul continuousAt_const

/-- A strictly positive coupling interval, inside the existing strict physical
sweep interval, on which the common pin-free shell coefficient is < 1. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
    (s : ℝ) (hs : 8 < s) :
    ∃ couplingCutoff : ℝ,
      0 < couplingCutoff ∧
      couplingCutoff ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s ∧
      ∀ beta : ℝ,
        0 ≤ beta →
        beta ≤ couplingCutoff →
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
            s beta < 1 := by
  let Q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
      s
  have hContinuous : ContinuousAt Q 0 := by
    simpa [Q] using
      continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ :=
    hContinuous 1 (by norm_num)
  let baseCutoff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
      s
  let couplingCutoff := min (delta / 2) baseCutoff
  have hBasePos : 0 < baseCutoff := by
    simpa [baseCutoff] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_pos
        s
  have hHalfDelta : 0 < delta / 2 := by positivity
  have hCutoffPos : 0 < couplingCutoff := by
    dsimp [couplingCutoff]
    exact lt_min hHalfDelta hBasePos
  refine ⟨couplingCutoff, hCutoffPos, ?_, ?_⟩
  · dsimp [couplingCutoff]
    exact min_le_right _ _
  · intro beta hbeta hbetaCut
    have hBetaHalfDelta :
        beta ≤ delta / 2 :=
      hbetaCut.trans (by
        dsimp [couplingCutoff]
        exact min_le_left _ _)
    have hBetaDelta : beta < delta := by
      linarith
    have hDistance : dist beta 0 < delta := by
      rw [Real.dist_eq]
      simp [abs_of_nonneg hbeta]
      exact hBetaDelta
    have hImage := hControl hDistance
    have hAbs : |Q beta - Q 0| < 1 := by
      simpa [Real.dist_eq] using hImage
    have hUpper : Q beta - Q 0 < 1 :=
      lt_of_le_of_lt (le_abs_self (Q beta - Q 0)) hAbs
    have hZero : Q 0 = 0 := by
      simp [Q]
    rw [hZero, sub_zero] at hUpper
    simpa [Q] using hUpper

/-- Canonical pin-free bidirectional-shell cutoff for a fixed scale s > 8. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
    (s : ℝ) (hs : 8 < s) : ℝ :=
  Classical.choose
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
      s hs)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_pos
    (s : ℝ) (hs : 8 < s) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
        s hs :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
      s hs)).1

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
    (s : ℝ) (hs : 8 < s) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
        s hs ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
        s :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
      s hs)).2.1

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_spec
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta < 1 :=
  (Classical.choose_spec
    (exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
      s hs)).2.2 beta hbeta hcut

/-- Actual canonical pin-free weighted columns are bounded by the bootstrap
envelope cbar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_exponentialWeightedColumn_le_bootstrapEnvelope
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 ≤ s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (center source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s center target) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
          s beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta
  let M :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioExponentialWeightedColumnCoefficient
      H N hN beta hbeta s center
  have hBase :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel_exponentialWeightedColumn_le
      H beta hbeta s hs center source
      R
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
      M
      (by
        simpa [R, M] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_exponentialWeightedColumnBound_exactCoefficient
            H N hN beta hbeta s hs center)
  have hCoeff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightActualPinFreeCoefficient_le_bootstrapEnvelope
      H N hN s hs center beta hbeta hcut
  have hWeight0 :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s center source :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
      H s (le_trans (by norm_num) hs) center source
  exact
    hBase.trans
      (mul_le_mul_of_nonneg_right hCoeff hWeight0)

/-- Pointwise reciprocal-weight decay with the beta-zero vanishing bootstrap
envelope, replacing the coarse half-barrier coefficient of PR #4837. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influence_le_bootstrapEnvelope_mul_inv_sourceWeight
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 1 ≤ s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
          s beta *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s source target)⁻¹ := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s source
  let cbar :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
      s beta
  have hColumn :
      (∑ x : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence x source * W x) ≤ cbar := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_exponentialWeightedColumn_le_bootstrapEnvelope
        H N hN s hs beta hbeta hcut source source
    have hSelf : W source = 1 := by
      simpa [W] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_self
          H s source
    simpa [K, W, cbar, hSelf] using h
  have hWeight0 :
      ∀ x : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ W x := by
    intro x
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_nonneg
        H s (le_trans (by norm_num) hs) source x
  have hEntry :
      K.influence target source * W target ≤
        ∑ x : PeriodicHypercubicEvenSpatialSliceLink H,
          K.influence x source * W x :=
    Finset.single_le_sum
      (fun x _ => mul_nonneg (K.influence_nonneg x source) (hWeight0 x))
      (Finset.mem_univ target)
  have hProd : K.influence target source * W target ≤ cbar :=
    hEntry.trans hColumn
  have hWeightPos : 0 < W target :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_pos
      H s (zero_lt_one.trans_le hs) source target
  have hDiv : K.influence target source ≤ cbar / W target :=
    (le_div_iff₀ hWeightPos).2 hProd
  simpa [K, W, cbar, div_eq_mul_inv] using hDiv

/-- Volume-uniform row bound by qShell. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_rowSum_le_bidirectionalShellCoefficient
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta := by
  classical
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let cbar :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
      s beta
  have hStrictCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
        s hs)
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hStrictCut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hcbar0 : 0 ≤ cbar := by
    simpa [cbar] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient_nonneg
        s beta hbeta hHalfCut
  have hDiag : K.influence target target = 0 :=
    K.influence_diagonal_zero target
  have hSplit :=
    Finset.sum_erase_add
      (s := (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
      (f := fun source => K.influence target source)
      (Finset.mem_univ target)
  have hSumErase :
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source) =
      ∑ source ∈
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
        K.influence target source := by
    simpa [hDiag] using hSplit.symm
  rw [hSumErase]
  calc
    (∑ source ∈
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
      K.influence target source) ≤
      ∑ source ∈
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).erase target,
        cbar *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s source target)⁻¹ := by
          apply Finset.sum_le_sum
          intro source hsource
          exact
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_influence_le_bootstrapEnvelope_mul_inv_sourceWeight
              H N hN s (by linarith) beta hbeta hHalfCut target source
    _ =
      cbar *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
          H s target := by
            unfold
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass
            rw [Finset.mul_sum]
    _ ≤
      cbar *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
          s :=
      mul_le_mul_of_nonneg_left
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMass_le_majorant
          H s hs target)
        hcbar0
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta := by
          rfl

/-- Volume-uniform column bound by the same qShell coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_columnSum_le_bidirectionalShellCoefficient
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
        H beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
          H N hN beta hbeta)).influence target source) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let W :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
      H s source
  let cbar :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient
      s beta
  have hStrictCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
        s hs)
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hStrictCut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hWeighted :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_exponentialWeightedColumn_le_bootstrapEnvelope
      H N hN s (by linarith) beta hbeta hHalfCut source source
  have hUnweightedWeighted :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source) ≤
      ∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source * W target := by
    apply Finset.sum_le_sum
    intro target htarget
    have hW1 : 1 ≤ W target := by
      simpa [W] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_one_le
          H s (by linarith) source target
    calc
      K.influence target source =
          K.influence target source * 1 := by ring
      _ ≤ K.influence target source * W target :=
        mul_le_mul_of_nonneg_left hW1 (K.influence_nonneg target source)
  have hSelf : W source = 1 := by
    simpa [W] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight_self
        H s source
  have hColumnCbar :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        K.influence target source) ≤ cbar := by
    exact hUnweightedWeighted.trans (by
      simpa [K, W, cbar, hSelf] using hWeighted)
  have hcbar0 : 0 ≤ cbar := by
    simpa [cbar] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient_nonneg
        s beta hbeta hHalfCut
  have hMass1 :
      1 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant
          s :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant_one_le
      s hs
  exact hColumnCbar.trans (by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
    simpa [cbar] using
      (mul_le_mul_of_nonneg_left hMass1 hcbar0))

/-- The canonical pin-free kernel has a volume-uniform L2 Schur action with
the common shell coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_action_sq_sum_le_bidirectionalShellCoefficient_sq
    (H N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (vector : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    (∑ target,
      (∑ source,
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
          H beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
            H N hN beta hbeta)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
            H N hN beta hbeta)).influence target source *
          vector source) ^ 2) ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta) ^ 2 *
        ∑ source, vector source ^ 2 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
        H N hN beta hbeta)
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
      s beta
  have hStrictCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
        s hs)
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hStrictCut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hq0 : 0 ≤ q := by
    simpa [
      q,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient] using
      mul_nonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient_nonneg
          s beta hbeta hHalfCut)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant_nonneg
          s hs)
  have hRow :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        ∑ source, K.influence target source ≤ q := by
    intro target
    simpa [K, q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_rowSum_le_bidirectionalShellCoefficient
        H N hN s hs beta hbeta hcut target
  have hColumn :
      ∀ source : PeriodicHypercubicEvenSpatialSliceLink H,
        ∑ target, K.influence target source ≤ q := by
    intro source
    simpa [K, q] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_columnSum_le_bidirectionalShellCoefficient
        H N hN s hs beta hbeta hcut source
  have hSchur :=
    FiniteNonnegativeSchur.action_sq_sum_le_row_mul_column
      K.influence K.influence_nonneg
      q q hq0 hRow hColumn vector
  simpa [K, q, pow_two] using hSchur

/-- The common shell coefficient is strictly contractive on its canonical
cutoff. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient_lt_one
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta < 1 :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_spec
    s hs beta hbeta hcut

end

end MGAP4D.MathlibAnalytic
