import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedRealNormLeakage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairPinFreeBidirectionalShellCutoff
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The exact ordered leakage envelope and its own uniform Schur cutoff

The coefficient from #4935 factors as
  k(source,target) = alpha(s,beta) * K_pin(target,source),
where alpha = sqrt(((2 : ENNReal)^(-1) * C_RMS(s,beta)).toReal).
The iid half-factor and the literal target,source order are retained.

We use k ITSELF as the new ordered leakage envelope. The old pin-free COLUMN
bound gives its row bound and the old ROW bound gives its column bound, both
with Q = alpha * qShell. This is not an assertion of kernel symmetry or of
compatibility with a differently normalized physical envelope.

On the strict physical interval alpha agrees with an elementary real formula.
That formula is continuous at zero and alpha(s,0)^2 = 4/3, whereas Q(s,0)=0.
A smaller strictly positive cutoff therefore gives 0 <= Q < 1, uniformly in
volume and rank. No old q_phys is silently reused. Actual terminal-profile
assembly, strict renewal contraction and the physical gap remain downstream.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStateSourceFixedPairEnergy

local notation "rmsCoefficient" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundSecondMeanRMSTargetMajorantCoefficient
local notation "cbar" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
local notation "strictCutoff" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
local notation "shellCoefficient" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
local notation "shellCutoff" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff

/-- The actual canonical pin-free kernel; this abbreviation does not transpose it. -/
abbrev jointLeakagePinFreeKernel (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledPhysicalLeftKernel
    H beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_nonneg
      H N hN beta hbeta)

/-- The common RMS multiplier, retaining the exact conditional-iid half-factor. -/
def jointLeakageRMSMultiplier (s beta : ℝ) : ℝ :=
  Real.sqrt (((2 : ℝ≥0∞)⁻¹ * rmsCoefficient s beta).toReal)

theorem jointLeakageRMSMultiplier_nonneg (s beta : ℝ) :
    0 ≤ jointLeakageRMSMultiplier s beta := Real.sqrt_nonneg _

/-- An algebraic factorization, not an estimate outside the physical cutoff.
Both ENNReal factors may be infinite here; toReal_mul is unconditional. -/
theorem jointLeakageNormCoefficient_eq_rmsMultiplier_mul_pinFree
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (s : ℝ) (source target : PeriodicHypercubicEvenSpatialSliceLink H) :
    jointLeakageNormCoefficient H N hN beta hbeta s source target =
      jointLeakageRMSMultiplier s beta *
        (jointLeakagePinFreeKernel H N hN beta hbeta).influence target source := by
  let K := jointLeakagePinFreeKernel H N hN beta hbeta
  change Real.sqrt
      (((2 : ℝ≥0∞)⁻¹ *
        (ENNReal.ofReal (K.influence target source ^ 2) * rmsCoefficient s beta)).toReal) =
    Real.sqrt (((2 : ℝ≥0∞)⁻¹ * rmsCoefficient s beta).toReal) *
      K.influence target source
  have hReorder :
      (2 : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal (K.influence target source ^ 2) * rmsCoefficient s beta) =
        ((2 : ℝ≥0∞)⁻¹ * rmsCoefficient s beta) *
          ENNReal.ofReal (K.influence target source ^ 2) := by ac_rfl
  rw [hReorder, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg _),
    Real.sqrt_mul ENNReal.toReal_nonneg,
    Real.sqrt_sq (K.influence_nonneg target source)]

/-- The real formula is defined on all real beta, for continuity at zero.
Its identification with the ENNReal coefficient below retains the cutoff. -/
def jointLeakageRMSMultiplierRealFormula (s beta : ℝ) : ℝ :=
  Real.sqrt ((1 / 2 : ℝ) *
    ((1 - cbar s beta ^ 2)⁻¹ * (Real.exp (32 * beta) ^ 2 + 1)))

theorem jointLeakageRMSMultiplier_eq_realFormula
    (s beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ strictCutoff s) :
    jointLeakageRMSMultiplier s beta = jointLeakageRMSMultiplierRealFormula s beta := by
  have hc : ENNReal.ofReal (cbar s beta ^ 2) < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient_sq_ofReal_lt_one_of_strictPhysicalSweepCutoff
      s beta hbeta hcut
  change Real.sqrt
      (((2 : ℝ≥0∞)⁻¹ * ((1 - ENNReal.ofReal (cbar s beta ^ 2))⁻¹ *
        (ENNReal.ofReal (Real.exp (32 * beta) ^ 2) + 1))).toReal) =
    Real.sqrt ((1 / 2 : ℝ) *
      ((1 - cbar s beta ^ 2)⁻¹ * (Real.exp (32 * beta) ^ 2 + 1)))
  apply congrArg Real.sqrt
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_inv,
    ENNReal.toReal_sub_of_le hc.le ENNReal.one_ne_top,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.one_ne_top]
  norm_num [ENNReal.toReal_ofReal (sq_nonneg (cbar s beta)),
    ENNReal.toReal_ofReal (sq_nonneg (Real.exp (32 * beta)))]

@[simp] theorem jointLeakageRMSMultiplierRealFormula_zero (s : ℝ) :
    jointLeakageRMSMultiplierRealFormula s 0 = Real.sqrt (4 / 3 : ℝ) := by
  norm_num [jointLeakageRMSMultiplierRealFormula,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier]

/-- The RMS multiplier is not an ignorable factor even at zero coupling. -/
theorem jointLeakageRMSMultiplier_zero_sq (s : ℝ) :
    jointLeakageRMSMultiplier s 0 ^ 2 = 4 / 3 := by
  rw [jointLeakageRMSMultiplier_eq_realFormula s 0 (by norm_num)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_pos s).le,
    jointLeakageRMSMultiplierRealFormula_zero, Real.sq_sqrt (by norm_num)]

theorem continuousAt_jointLeakageRMSMultiplierRealFormula (s : ℝ) :
    ContinuousAt (jointLeakageRMSMultiplierRealFormula s) 0 := by
  have hC : ContinuousAt (cbar s) 0 :=
    continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient s
  have hDenNe : 1 - cbar s 0 ^ 2 ≠ 0 := by
    norm_num [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureBarrier]
  have hInv : ContinuousAt (fun beta : ℝ => (1 - cbar s beta ^ 2)⁻¹) 0 :=
    (continuousAt_const.sub (hC.pow 2)).inv₀ hDenNe
  have hExp : ContinuousAt (fun beta : ℝ => Real.exp (32 * beta) ^ 2) 0 := by
    fun_prop
  exact (continuousAt_const.mul (hInv.mul (hExp.add continuousAt_const))).sqrt

/-- The new envelope has its own Schur coefficient; this is not q_phys. -/
def jointLeakageSchurCoefficient (s beta : ℝ) : ℝ :=
  jointLeakageRMSMultiplier s beta * shellCoefficient s beta

@[simp] theorem jointLeakageSchurCoefficient_zero (s : ℝ) :
    jointLeakageSchurCoefficient s 0 = 0 := by
  simp [jointLeakageSchurCoefficient]

theorem jointLeakageSchurCoefficient_nonneg
    (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ shellCutoff s hs) :
    0 ≤ jointLeakageSchurCoefficient s beta := by
  have hStrict : beta ≤ strictCutoff s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff s hs)
  have hHalf := hStrict.trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff s)
  apply mul_nonneg (jointLeakageRMSMultiplier_nonneg s beta)
  exact mul_nonneg
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightBootstrapEnvelopePinFreeCoefficient_nonneg
      s beta hbeta hHalf)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeOffDiagonalReciprocalExponentialWeightMassMajorant_nonneg s hs)

/-- A row of k(source,target) is a COLUMN of the original pin-free kernel. -/
theorem jointLeakageNormCoefficient_rowSum_le_schurCoefficient
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ shellCutoff s hs)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      jointLeakageNormCoefficient H N hN beta hbeta s source target) ≤
      jointLeakageSchurCoefficient s beta := by
  simp_rw [jointLeakageNormCoefficient_eq_rmsMultiplier_mul_pinFree]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_columnSum_le_bidirectionalShellCoefficient
      H N hN s hs beta hbeta hcut source)
    (jointLeakageRMSMultiplier_nonneg s beta)

/-- A column of k(source,target) is a ROW of the original pin-free kernel. -/
theorem jointLeakageNormCoefficient_columnSum_le_schurCoefficient
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ shellCutoff s hs)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      jointLeakageNormCoefficient H N hN beta hbeta s source target) ≤
      jointLeakageSchurCoefficient s beta := by
  simp_rw [jointLeakageNormCoefficient_eq_rmsMultiplier_mul_pinFree]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreePhysicalLeftKernel_rowSum_le_bidirectionalShellCoefficient
      H N hN s hs beta hbeta hcut target)
    (jointLeakageRMSMultiplier_nonneg s beta)

/-- The receiver's transpose convention, with no source-count constant. -/
theorem jointLeakageNormCoefficient_transpose_action_sq_sum_le
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ shellCutoff s hs)
    (v : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
        jointLeakageNormCoefficient H N hN beta hbeta s source target * v source) ^ 2) ≤
      jointLeakageSchurCoefficient s beta ^ 2 * ∑ source, v source ^ 2 := by
  have h := FiniteNonnegativeSchur.action_sq_sum_le_row_mul_column
    (fun target source => jointLeakageNormCoefficient H N hN beta hbeta s source target)
    (fun target source => jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source target)
    (jointLeakageSchurCoefficient s beta) (jointLeakageSchurCoefficient s beta)
    (jointLeakageSchurCoefficient_nonneg s hs beta hbeta hcut)
    (fun target => jointLeakageNormCoefficient_columnSum_le_schurCoefficient
      H N hN s hs beta hbeta hcut target)
    (fun source => jointLeakageNormCoefficient_rowSum_le_schurCoefficient
      H N hN s hs beta hbeta hcut source) v
  simpa only [pow_two] using h

/-- A positive cutoff depending only on s, for the new coefficient Q. -/
theorem exists_jointLeakageSchurCutoff (s : ℝ) (hs : 8 < s) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ shellCutoff s hs ∧
      ∀ beta : ℝ, 0 ≤ beta → beta ≤ cutoff → jointLeakageSchurCoefficient s beta < 1 := by
  let Q : ℝ → ℝ := fun beta =>
    jointLeakageRMSMultiplierRealFormula s beta * shellCoefficient s beta
  have hContinuous : ContinuousAt Q 0 :=
    (continuousAt_jointLeakageRMSMultiplierRealFormula s).mul
      (continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient s)
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ := hContinuous 1 (by norm_num)
  let cutoff := min (delta / 2) (shellCutoff s hs)
  have hCutPos : 0 < cutoff := lt_min (by positivity)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_pos s hs)
  have hCutShell : cutoff ≤ shellCutoff s hs := min_le_right _ _
  refine ⟨cutoff, hCutPos, hCutShell, ?_⟩
  intro beta hbeta hbetaCut
  have hBetaHalf : beta ≤ delta / 2 := hbetaCut.trans (min_le_left _ _)
  have hDistance : dist beta 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbeta]
    linarith
  have hAbs : |Q beta - Q 0| < 1 := by
    simpa only [Real.dist_eq] using hControl hDistance
  have hUpper : Q beta - Q 0 < 1 :=
    lt_of_le_of_lt (le_abs_self _) hAbs
  have hZero : Q 0 = 0 := by simp [Q]
  rw [hZero, sub_zero] at hUpper
  have hStrict : beta ≤ strictCutoff s :=
    (hbetaCut.trans hCutShell).trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff s hs)
  simpa only [Q, jointLeakageSchurCoefficient,
    jointLeakageRMSMultiplier_eq_realFormula s beta hbeta hStrict] using hUpper

/-- The cutoff is independent of H, N and the observable. -/
def jointLeakageSchurCutoff (s : ℝ) (hs : 8 < s) : ℝ :=
  Classical.choose (exists_jointLeakageSchurCutoff s hs)

theorem jointLeakageSchurCutoff_pos (s : ℝ) (hs : 8 < s) :
    0 < jointLeakageSchurCutoff s hs :=
  (Classical.choose_spec (exists_jointLeakageSchurCutoff s hs)).1

theorem jointLeakageSchurCutoff_le_shellCutoff (s : ℝ) (hs : 8 < s) :
    jointLeakageSchurCutoff s hs ≤ shellCutoff s hs :=
  (Classical.choose_spec (exists_jointLeakageSchurCutoff s hs)).2.1

theorem jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff (s : ℝ) (hs : 8 < s) :
    jointLeakageSchurCutoff s hs ≤ strictCutoff s :=
  (jointLeakageSchurCutoff_le_shellCutoff s hs).trans
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff s hs)

theorem jointLeakageSchurCoefficient_nonneg_lt_one
    (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageSchurCutoff s hs) :
    0 ≤ jointLeakageSchurCoefficient s beta ∧ jointLeakageSchurCoefficient s beta < 1 := by
  exact ⟨jointLeakageSchurCoefficient_nonneg s hs beta hbeta
      (hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)),
    (Classical.choose_spec (exists_jointLeakageSchurCutoff s hs)).2.2 beta hbeta hcut⟩

end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
