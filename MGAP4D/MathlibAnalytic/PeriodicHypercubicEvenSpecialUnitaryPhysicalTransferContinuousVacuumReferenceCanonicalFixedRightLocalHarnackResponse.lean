import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFixedRightKernelSectionHarnack
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightResponseProfile
import Mathlib.Tactic

/-!
# Canonical fixed-right local Harnack response

The fixed-right kernel-section law now has a volume-independent Harnack
comparison under one right-boundary update.  This file transports that law
comparison to the literal target-ratio response itself.

The target-ratio observable is bounded by `exp (16 * beta)`.  Scaling the
bounded-test Harnack comparison therefore gives

  ResponseAbs <= exp(16 beta) * eta_R(beta),

where `eta_R(beta)` is the fixed-right boundary-update Harnack influence from
the preceding theorem unit.  The same estimate then passes to the canonical
pointwise `sSup` response profile.

The coefficient vanishes at beta = 0 and is independent of the finite volume.
No weighted response coefficient, contraction hypothesis, covariance decay,
coercivity, or mass-gap input is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance canonicalFixedRightLocalHarnackResponseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- Mutual multiplicative domination gives the same sharp bounded-test
coefficient when integrability under both probability measures is supplied
explicitly. -/
private theorem probabilityMeasure_integrableBoundedTest_integral_difference_abs_le_of_pairwise_le_smul
    {α : Type*}
    [MeasurableSpace α]
    (μ ν : Measure α)
    [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (K : ℝ)
    (hK : 1 ≤ K)
    (hμν : μ ≤ ENNReal.ofReal K • ν)
    (hνμ : ν ≤ ENNReal.ofReal K • μ)
    (phi : α → ℝ)
    (hphiIntμ : Integrable phi μ)
    (hphiIntν : Integrable phi ν)
    (hphiBound : ∀ x, |phi x| ≤ 1) :
    |(∫ x, phi x ∂μ) - (∫ x, phi x ∂ν)| ≤
      2 * ((K - 1) / (K + 1)) := by
  have hKnonneg : 0 ≤ K := by linarith
  have hKtop : ENNReal.ofReal K ≠ ∞ := ENNReal.ofReal_ne_top
  let f : α → ℝ := fun x => (phi x + 1) / 2
  let g : α → ℝ := fun x => 1 - f x
  have hfNonneg : ∀ x, 0 ≤ f x := by
    intro x
    have hx := (abs_le.mp (hphiBound x)).1
    dsimp [f]
    linarith
  have hfLeOne : ∀ x, f x ≤ 1 := by
    intro x
    have hx := (abs_le.mp (hphiBound x)).2
    dsimp [f]
    linarith
  have hgNonneg : ∀ x, 0 ≤ g x := by
    intro x
    dsimp [g]
    exact sub_nonneg.mpr (hfLeOne x)
  have hfIntμ : Integrable f μ := by
    dsimp [f]
    exact (hphiIntμ.add (integrable_const (1 : ℝ))).div_const 2
  have hfIntν : Integrable f ν := by
    dsimp [f]
    exact (hphiIntν.add (integrable_const (1 : ℝ))).div_const 2
  have hgIntμ : Integrable g μ := by
    dsimp [g]
    exact (integrable_const (1 : ℝ)).sub hfIntμ
  have hgIntν : Integrable g ν := by
    dsimp [g]
    exact (integrable_const (1 : ℝ)).sub hfIntν
  have hFμν :
      (∫ x, f x ∂μ) ≤ K * ∫ x, f x ∂ν := by
    calc
      (∫ x, f x ∂μ) ≤ ∫ x, f x ∂(ENNReal.ofReal K • ν) := by
        exact integral_mono_measure hμν
          (Filter.Eventually.of_forall hfNonneg)
          (hfIntν.smul_measure hKtop)
      _ = K * ∫ x, f x ∂ν := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hFνμ :
      (∫ x, f x ∂ν) ≤ K * ∫ x, f x ∂μ := by
    calc
      (∫ x, f x ∂ν) ≤ ∫ x, f x ∂(ENNReal.ofReal K • μ) := by
        exact integral_mono_measure hνμ
          (Filter.Eventually.of_forall hfNonneg)
          (hfIntμ.smul_measure hKtop)
      _ = K * ∫ x, f x ∂μ := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hGμν :
      (∫ x, g x ∂μ) ≤ K * ∫ x, g x ∂ν := by
    calc
      (∫ x, g x ∂μ) ≤ ∫ x, g x ∂(ENNReal.ofReal K • ν) := by
        exact integral_mono_measure hμν
          (Filter.Eventually.of_forall hgNonneg)
          (hgIntν.smul_measure hKtop)
      _ = K * ∫ x, g x ∂ν := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hGνμ :
      (∫ x, g x ∂ν) ≤ K * ∫ x, g x ∂μ := by
    calc
      (∫ x, g x ∂ν) ≤ ∫ x, g x ∂(ENNReal.ofReal K • μ) := by
        exact integral_mono_measure hνμ
          (Filter.Eventually.of_forall hgNonneg)
          (hgIntμ.smul_measure hKtop)
      _ = K * ∫ x, g x ∂μ := by
        rw [integral_smul_measure]
        simp [ENNReal.toReal_ofReal hKnonneg, smul_eq_mul]
  have hGμ : (∫ x, g x ∂μ) = 1 - ∫ x, f x ∂μ := by
    dsimp [g]
    rw [integral_sub (integrable_const (1 : ℝ)) hfIntμ]
    simp
  have hGν : (∫ x, g x ∂ν) = 1 - ∫ x, f x ∂ν := by
    dsimp [g]
    rw [integral_sub (integrable_const (1 : ℝ)) hfIntν]
    simp
  rw [hGμ, hGν] at hGμν hGνμ
  have hden : 0 < K + 1 := by linarith
  have hUpper :
      (∫ x, f x ∂μ) - (∫ x, f x ∂ν) ≤
        (K - 1) / (K + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hFμν, hGνμ]
  have hUpperSwap :
      (∫ x, f x ∂ν) - (∫ x, f x ∂μ) ≤
        (K - 1) / (K + 1) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hFνμ, hGμν]
  have hAbsF :
      |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤
        (K - 1) / (K + 1) := by
    exact abs_le.mpr ⟨by linarith, hUpper⟩
  have hfμ :
      (∫ x, f x ∂μ) = ((∫ x, phi x ∂μ) + 1) / 2 := by
    dsimp [f]
    rw [integral_div, integral_add hphiIntμ (integrable_const (1 : ℝ))]
    simp
  have hfν :
      (∫ x, f x ∂ν) = ((∫ x, phi x ∂ν) + 1) / 2 := by
    dsimp [f]
    rw [integral_div, integral_add hphiIntν (integrable_const (1 : ℝ))]
    simp
  have hDiff :
      (∫ x, phi x ∂μ) - (∫ x, phi x ∂ν) =
        2 * ((∫ x, f x ∂μ) - (∫ x, f x ∂ν)) := by
    rw [hfμ, hfν]
    ring
  rw [hDiff, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left hAbsF (by norm_num)

/-- The fixed-right Harnack comparison extends to bounded tests for which
integrability under the two compared kernel-section laws is known directly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_update_right_integrableBoundedTest_difference_le_harnackInfluence
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (hphiH : Integrable phi
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta (Function.update C source h)))
    (hphiK : Integrable phi
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta (Function.update C source k)))
    (hphiBound : ∀ A, |phi A| ≤ 1) :
    |(∫ A, phi A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta (Function.update C source h)) -
      (∫ A, phi A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta (Function.update C source k))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
        beta := by
  let μHaar :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let wh : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun A =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN beta hbeta (Function.update C source h) A)
  let wk : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun A =>
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
          H N hN beta hbeta (Function.update C source k) A)
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
  let K : ℝ := (Real.exp (8 * beta)) ^ 2
  let μh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta (Function.update C source h)
  let μk :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta (Function.update C source k)
  letI : IsProbabilityMeasure μh := by
    dsimp [μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta (Function.update C source h)
  letI : IsProbabilityMeasure μk := by
    dsimp [μk]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta (Function.update C source k)
  have hwk : ∀ A, wh A ≤ R * wk A := by
    intro A
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_update_right_pairwise_harnack
        H N hN beta hbeta C source h k A).1
    dsimp [wh, wk, R]
    calc
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
            H N hN beta hbeta (Function.update C source h) A) ≤
        ENNReal.ofReal
          (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta (Function.update C source k) A) :=
        ENNReal.ofReal_le_ofReal hReal
      _ =
        ENNReal.ofReal (Real.exp (8 * beta)) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta (Function.update C source k) A) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hkw : ∀ A, wk A ≤ R * wh A := by
    intro A
    have hReal :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight_update_right_pairwise_harnack
        H N hN beta hbeta C source h k A).2
    dsimp [wh, wk, R]
    calc
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
            H N hN beta hbeta (Function.update C source k) A) ≤
        ENNReal.ofReal
          (Real.exp (8 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta (Function.update C source h) A) :=
        ENNReal.ofReal_le_ofReal hReal
      _ =
        ENNReal.ofReal (Real.exp (8 * beta)) *
          ENNReal.ofReal
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousWeight
              H N hN beta hbeta (Function.update C source h) A) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hR0 : R ≠ 0 := by
    exact ne_of_gt (by
      dsimp [R]
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hRtop : R ≠ ∞ := by
    dsimp [R]
    exact ENNReal.ofReal_ne_top
  have hPair :=
    doobWeightedMeasure_pairwise_le_mul_sq_of_pointwise_le_mul
      μHaar wh wk R hR0 hRtop hwk hkw
  have hScalar : R * R = ENNReal.ofReal K := by
    dsimp [R, K]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    ring
  rw [hScalar] at hPair
  have hLawH : μh = doobWeightedMeasure μHaar wh := by
    rfl
  have hLawK : μk = doobWeightedMeasure μHaar wk := by
    rfl
  have hμν : μh ≤ ENNReal.ofReal K • μk := by
    rw [hLawH, hLawK]
    exact hPair.1
  have hνμ : μk ≤ ENNReal.ofReal K • μh := by
    rw [hLawH, hLawK]
    exact hPair.2
  have hK : 1 ≤ K := by
    dsimp [K]
    have hExp : 1 ≤ Real.exp (8 * beta) :=
      Real.one_le_exp (mul_nonneg (by norm_num) hbeta)
    nlinarith [sq_nonneg (Real.exp (8 * beta) - 1)]
  have hBound :=
    probabilityMeasure_integrableBoundedTest_integral_difference_abs_le_of_pairwise_le_smul
      μh μk K hK hμν hνμ phi
      (by simpa [μh] using hphiH)
      (by simpa [μk] using hphiK)
      hphiBound
  simpa [
    μh, μk, K,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence] using
    hBound

/-- Every literal fixed-right target-ratio response is controlled by the
fixed-right boundary-update Harnack influence times the exact target-ratio
amplitude bound `exp(16 beta)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_exp_sixteen_mul_boundaryUpdateHarnackInfluence
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
          beta := by
  by_cases hEq : target = source
  · subst target
    have hNonneg :
        0 ≤
          Real.exp (16 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
              beta :=
      mul_nonneg (Real.exp_pos _).le
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence_nonneg
          beta hbeta)
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs] using hNonneg
  · have hSourceTarget : source ≠ target := Ne.symm hEq
    let C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
      Function.update B target g₂
    let μh :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta (Function.update C source h)
    let μk :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
        H N hN beta hbeta (Function.update C source k)
    let F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
      fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
    let M : ℝ := Real.exp (16 * beta)
    let phi : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
      fun A => F A / M
    letI : IsProbabilityMeasure μh := by
      dsimp [μh]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
          H N hN beta hbeta (Function.update C source h)
    letI : IsProbabilityMeasure μk := by
      dsimp [μk]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
          H N hN beta hbeta (Function.update C source k)
    have hIntH : Integrable F μh := by
      simpa [F] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_integrable
          H N hN beta hbeta B target g₁ g₂ μh
    have hIntK : Integrable F μk := by
      simpa [F] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_integrable
          H N hN beta hbeta B target g₁ g₂ μk
    have hMPos : 0 < M := by
      dsimp [M]
      positivity
    have hPhiH : Integrable phi μh := by
      dsimp [phi]
      exact hIntH.div_const M
    have hPhiK : Integrable phi μk := by
      dsimp [phi]
      exact hIntK.div_const M
    have hPhiBound : ∀ A, |phi A| ≤ 1 := by
      intro A
      have hFPos :
          0 <
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₂ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_pos
          H N beta A B target g₁ g₂
      have hFLe :
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₂ ≤
            M := by
        simpa [M] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_le_exp_sixteen
            H N hN beta hbeta A B target g₁ g₂
      change |F A / M| ≤ 1
      rw [abs_of_pos (div_pos (by simpa [F] using hFPos) hMPos)]
      exact (div_le_one hMPos).2 (by simpa [F] using hFLe)
    have hScaled :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_update_right_integrableBoundedTest_difference_le_harnackInfluence
        H N hN beta hbeta C source h k phi hPhiH hPhiK hPhiBound
    have hScaled' :
        |((∫ A, F A ∂μh) / M) - ((∫ A, F A ∂μk) / M)| ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
            beta := by
      simpa [phi, integral_div] using hScaled
    have hFinal :
        |(∫ A, F A ∂μh) - (∫ A, F A ∂μk)| ≤
          M *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
              beta := by
      have hScaleEq :
          |(∫ A, F A ∂μh) - (∫ A, F A ∂μk)| =
            M * |((∫ A, F A ∂μh) / M) - ((∫ A, F A ∂μk) / M)| := by
        rw [← abs_mul, abs_of_pos hMPos]
        congr 1
        field_simp [ne_of_gt hMPos]
        <;> ring
      rw [hScaleEq]
      exact mul_le_mul_of_nonneg_left hScaled' hMPos.le
    have hUpdateH :
        Function.update (Function.update B source h) target g₂ =
          Function.update C source h := by
      funext e
      by_cases heSource : e = source
      · subst e
        simp [C, hEq, hSourceTarget]
      · by_cases heTarget : e = target
        · subst e
          simp [C, heSource, hEq, hSourceTarget]
        · simp [C, heSource, heTarget]
    have hUpdateK :
        Function.update (Function.update B source k) target g₂ =
          Function.update C source k := by
      funext e
      by_cases heSource : e = source
      · subst e
        simp [C, hEq, hSourceTarget]
      · by_cases heTarget : e = target
        · subst e
          simp [C, heSource, hEq, hSourceTarget]
        · simp [C, heSource, heTarget]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
    rw [hUpdateH, hUpdateK]
    simpa [F, μh, μk, M] using hFinal

/-- The canonical actual-response profile inherits the same local Harnack
response bound pointwise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile_le_exp_sixteen_mul_boundaryUpdateHarnackInfluence
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
        H N hN beta hbeta target source ≤
      Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
          beta := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet
      H N hN beta hbeta target source
  have hBoundNonneg :
      0 ≤
        Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
            beta :=
    mul_nonneg (Real.exp_pos _).le
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence_nonneg
        beta hbeta)
  have hSup :
      sSup S ≤
        Real.exp (16 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabFixedRightKernelSectionBoundaryUpdateHarnackInfluence
            beta := by
    apply csSup_le
    · exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseValueSet_nonempty
          H N hN beta hbeta target source
    · intro x hx
      rcases hx with ⟨B, g₁, g₂, h, k, rfl⟩
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_exp_sixteen_mul_boundaryUpdateHarnackInfluence
          H N hN beta hbeta B target source g₁ g₂ h k
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightTargetRatioResponseProfile
  exact max_le hBoundNonneg hSup

end

end MathlibAnalytic
end MGAP4D
