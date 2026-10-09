import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHalfDensityLocalHarnack
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedPosteriorMeanTransferBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# P4-Q2-B: signed original physical normalized-mean one-link source integral

The actual frozen-beta physical transfer output is
  M_f(B) = ‖T_beta‖⁻¹ (∫ A, K_beta(A,B) f(A) dHaar(A)) / Ω_beta(B).

Unlike a positive-vacuum Harnack proof, no assumption f ≥ 0 is made:
the fine-scale right Krylov source is signed and produced at beta(n+1).

Local comparison of the ORIGINAL positive Wilson kernel K at beta(n)
and the strictly positive continuous vacuum Ω at beta(n) gives a
pointwise bound on the variation of the kernel QUOTIENT K/Ω.
We then multiply the DIFFERENCE by the genuine signed physical L²
source before taking the absolute value under its actual Haar integral.

This produces a concrete L¹ source coefficient:
  |M_f(B[e←g])-M_f(B)|
    ≤ ‖T_beta‖⁻¹ * (exp(16 beta)-1) / Ω_beta(B)
      * ∫ |f(A)| dHaar(A).

The source integral is finite by L² → L¹ on the genuine Haar probability,
and no finite-support hypothesis or positive-kernel inequality for a
signed source integral is made. No Dobrushin method is used.

The inverse vacuum and transfer norm remain explicit and may depend on
finite volume. There is no assertion of a volume-uniform Gram bound,
cross-scale compatibility or continuum mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4SignedMeanTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4SignedMeanCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4SignedMeanSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4SignedMeanMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4SignedMeanBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace GroundStatePosteriorJoint

/-- Pure real-algebra quotient estimate used only after the positivity
of the Wilson kernel and the continuous physical vacuum has been shown.
The bound tends to zero at R=1. -/
private theorem positiveKernelQuotient_difference_abs_le
    (k k' omega omega' R : ℝ)
    (hk : 0 ≤ k) (hk' : 0 ≤ k')
    (hkOne : k ≤ 1)
    (homega : 0 < omega) (homega' : 0 < omega')
    (hR : 1 ≤ R)
    (hKforward : k' ≤ R * k) (hKbackward : k ≤ R * k')
    (hOforward : omega' ≤ R * omega)
    (hObackward : omega ≤ R * omega') :
    |k' / omega' - k / omega| ≤ (R ^ 2 - 1) / omega := by
  let u := k' / omega'
  let v := k / omega
  have hRnonneg : 0 ≤ R := by linarith
  have hRtwo : 1 ≤ R ^ 2 := by nlinarith
  have hRminus : 0 ≤ R ^ 2 - 1 := by linarith
  have hUpper : u ≤ R ^ 2 * v := by
    have h : k' / omega' ≤ (R ^ 2 * k) / omega :=
      (div_le_div_iff₀ homega' homega).2 (by
        calc
          k' * omega ≤ (R * k) * omega :=
            mul_le_mul_of_nonneg_right hKforward homega.le
          _ ≤ (R * k) * (R * omega') :=
            mul_le_mul_of_nonneg_left hObackward (mul_nonneg hRnonneg hk)
          _ = (R ^ 2 * k) * omega' := by ring)
    simpa [u, v, mul_div_assoc] using h
  have hLower : v ≤ R ^ 2 * u := by
    have h : k / omega ≤ (R ^ 2 * k') / omega' :=
      (div_le_div_iff₀ homega homega').2 (by
        calc
          k * omega' ≤ (R * k') * omega' :=
            mul_le_mul_of_nonneg_right hKbackward homega'.le
          _ ≤ (R * k') * (R * omega) :=
            mul_le_mul_of_nonneg_left hOforward (mul_nonneg hRnonneg hk')
          _ = (R ^ 2 * k') * omega := by ring)
    simpa [u, v, mul_div_assoc] using h
  have hv : 0 ≤ v := div_nonneg hk homega.le
  have hvBound : v ≤ 1 / omega := by
    change k / omega ≤ 1 / omega
    apply (div_le_div_iff₀ homega homega).2
    have h := mul_le_mul_of_nonneg_right hkOne homega.le
    nlinarith
  have hForward : u - v ≤ (R ^ 2 - 1) * v := by
    nlinarith [hUpper]
  have hBackward : v - u ≤ (R ^ 2 - 1) * v := by
    by_cases hUV : u ≤ v
    · have h : v - u ≤ (R ^ 2 - 1) * u := by nlinarith [hLower]
      exact h.trans (mul_le_mul_of_nonneg_left hUV hRminus)
    · have hVU : v ≤ u := le_of_lt (lt_of_not_ge hUV)
      calc
        v - u ≤ 0 := sub_nonpos.mpr hVU
        _ ≤ (R ^ 2 - 1) * v := mul_nonneg hRminus hv
  have hAbs : |u - v| ≤ (R ^ 2 - 1) * v :=
    abs_le.mpr ⟨by linarith, hForward⟩
  calc
    |k' / omega' - k / omega| = |u - v| := rfl
    _ ≤ (R ^ 2 - 1) * v := hAbs
    _ ≤ (R ^ 2 - 1) * (1 / omega) :=
      mul_le_mul_of_nonneg_left hvBound hRminus
    _ = (R ^ 2 - 1) / omega := by ring

/-- A general signed-source integration lemma: comparison applies to
the DIFFERENCE of weights under the integral, not to the integral of
a nonpositive source. This is the only step at which |f| is introduced. -/
private theorem signedSource_integral_weight_difference_abs_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w w' f : α → ℝ) (c : ℝ)
    (hf : Integrable f μ)
    (hw : Integrable (fun x => w x * f x) μ)
    (hw' : Integrable (fun x => w' x * f x) μ)
    (hc : 0 ≤ c)
    (hOsc : ∀ x, |w' x - w x| ≤ c) :
    |(∫ x, w' x * f x ∂μ) - (∫ x, w x * f x ∂μ)| ≤
      c * ∫ x, ‖f x‖ ∂μ := by
  have hDiff :
      (∫ x, w' x * f x ∂μ) - (∫ x, w x * f x ∂μ) =
        ∫ x, (w' x - w x) * f x ∂μ := by
    rw [← integral_sub hw' hw]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hDom : Integrable (fun x => c * ‖f x‖) μ :=
    hf.norm.const_mul c
  have hNorm :
      ‖∫ x, (w' x - w x) * f x ∂μ‖ ≤
        ∫ x, c * ‖f x‖ ∂μ := by
    apply norm_integral_le_of_norm_le hDom
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hOsc x) (norm_nonneg _)
  calc
    |(∫ x, w' x * f x ∂μ) - (∫ x, w x * f x ∂μ)| =
        ‖∫ x, (w' x - w x) * f x ∂μ‖ := by
      rw [hDiff, Real.norm_eq_abs]
    _ ≤ ∫ x, c * ‖f x‖ ∂μ := hNorm
    _ = c * ∫ x, ‖f x‖ ∂μ := integral_const_mul _ _

/-- The physical normalized positive Wilson kernel section acts on
a signed Haar-L² source through a genuinely integrable product. -/
private theorem normalizedKernelSection_signedSource_integrable
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) :
    Integrable (fun A =>
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B) * f A)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta B
  have hOmega : 0 < omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  have hf : Integrable (fun A => f A) μ :=
    (Lp.memLp f).integrable (by norm_num)
  have hKContinuous :
      Continuous (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A B) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp₂ continuous_id continuous_const
  have hw :
      AEStronglyMeasurable
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A B / omega) μ :=
    (hKContinuous.div_const omega).aestronglyMeasurable
  have hb :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            H N beta A B / omega| ≤ omega⁻¹ := by
    intro A
    have hp :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta A B
    have hOne :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta A B
    have hK : periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B ≤ 1 := by simpa [abs_of_pos hp] using hOne
    rw [abs_of_pos (div_pos hp hOmega)]
    have h := (div_le_div_iff₀ hOmega hOmega).2 (by
      have hm := mul_le_mul_of_nonneg_right hK hOmega.le
      nlinarith)
    simpa only [one_div] using h
  have hWNonneg : 0 ≤ omega⁻¹ := (inv_pos.mpr hOmega).le
  have hDom : Integrable (fun A => omega⁻¹ * ‖f A‖) μ :=
    hf.norm.const_mul _
  have hProd : Integrable
      (fun A => (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta A B / omega) * f A) μ := by
    apply hDom.mono' (hw.mul hf.aestronglyMeasurable)
    filter_upwards with A
    rw [norm_mul, Real.norm_eq_abs, norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg hWNonneg, abs_of_nonneg (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right (hb A) (norm_nonneg _)
  simpa [omega, μ] using hProd

/-- The genuine signed source is controlled by the exact original
Wilson kernel / positive-vacuum quotient. The only source integral
used is its actual spatial-slice Haar L¹ norm, finite by L². -/
theorem normalizedPhysicalOneSlabVacuumReceiverBCF_rightLinkDifference_abs_le_signedSourceL1
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f
        (Function.update B e g) -
      normalizedPhysicalOneSlabVacuumReceiverBCF H N hN beta hbeta f B| ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
        (((Real.exp (8 * beta)) ^ 2 - 1) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta B) *
        (∫ A, ‖(f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) A‖
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let F : Lp ℝ 2 μ := f
  let Omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let K := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let R : ℝ := Real.exp (8 * beta)
  let B' := Function.update B e g
  let c : ℝ := (R ^ 2 - 1) / Omega B
  have hR : 1 ≤ R := by
    have hb : (0 : ℝ) ≤ 8 * beta := by nlinarith [hbeta]
    simpa [R] using
      (Real.exp_le_exp.mpr hb : Real.exp (0 : ℝ) ≤ Real.exp (8 * beta))
  have hOmega : 0 < Omega B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  have hOmega' : 0 < Omega B' :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B'
  have hOmegaForward : Omega B' ≤ R * Omega B := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta B e g (B e)
    simpa [Omega, B', R,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using h
  have hOmegaBackward : Omega B ≤ R * Omega B' := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
        H N hN beta hbeta B e (B e) g
    simpa [Omega, B', R,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using h
  have hc : 0 ≤ c := by
    apply div_nonneg
    · have : 1 ≤ R ^ 2 := by nlinarith [hR]
      linarith
    · exact hOmega.le
  have hKernelVariation (A :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      |K A B' / Omega B' - K A B / Omega B| ≤ c := by
    have hK : 0 < K A B :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta A B
    have hK' : 0 < K A B' :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H N beta A B'
    have hOne : K A B ≤ 1 := by
      have h := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H N hN beta hbeta A B
      simpa [K, abs_of_pos hK] using h
    have hKF : K A B' ≤ R * K A B := by
      have h :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
          H N hN beta hbeta A B e g (B e)
      simpa [K, R, B',
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using h
    have hKB : K A B ≤ R * K A B' := by
      have h :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuousVacuumReplaceLink_le_exp_eight_mul
          H N hN beta hbeta A B e (B e) g
      simpa [K, R, B',
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink] using h
    exact positiveKernelQuotient_difference_abs_le
      (K A B) (K A B') (Omega B) (Omega B') R
      hK.le hK'.le hOne hOmega hOmega' hR
      hKF hKB hOmegaForward hOmegaBackward
  have hf : Integrable (fun A => F A) μ :=
    (Lp.memLp F).integrable (by norm_num)
  have hInt : Integrable (fun A => (K A B / Omega B) * F A) μ := by
    simpa [K, Omega, F, μ] using
      normalizedKernelSection_signedSource_integrable H N hN beta hbeta B F
  have hInt' : Integrable (fun A => (K A B' / Omega B') * F A) μ := by
    simpa [K, Omega, F, μ] using
      normalizedKernelSection_signedSource_integrable H N hN beta hbeta B' F
  have hSigned :
      |(∫ A, (K A B' / Omega B') * F A ∂μ) -
        (∫ A, (K A B / Omega B) * F A ∂μ)| ≤
      c * ∫ A, ‖F A‖ ∂μ :=
    signedSource_integral_weight_difference_abs_le μ
      (fun A => K A B / Omega B) (fun A => K A B' / Omega B') F c
      hf hInt hInt' hc hKernelVariation
  have hConvert (X :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      l * decomposableOneSliceTransferIntegral H N beta F X / Omega X =
        l * (∫ A, (K A X / Omega X) * F A ∂μ) := by
    have hK :
        (∫ A, (K A X / Omega X) * F A ∂μ) =
        (∫ A, K A X * F A ∂μ) / Omega X := by
      calc
        (∫ A, (K A X / Omega X) * F A ∂μ) =
            ∫ A, (Omega X)⁻¹ * (K A X * F A) ∂μ := by
          apply integral_congr_ae
          filter_upwards with A
          ring
        _ = (Omega X)⁻¹ * ∫ A, K A X * F A ∂μ := integral_const_mul _ _
        _ = (∫ A, K A X * F A ∂μ) / Omega X := by ring
    change l * (∫ A, K A X * F A ∂μ) / Omega X = _
    rw [hK]
    ring
  have hl : 0 ≤ l :=
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)).le
  change |l * decomposableOneSliceTransferIntegral H N beta F B' / Omega B' -
    l * decomposableOneSliceTransferIntegral H N beta F B / Omega B| ≤
    l * c * (∫ A, ‖F A‖ ∂μ)
  rw [hConvert B', hConvert B, ← mul_sub, abs_mul, abs_of_nonneg hl]
  exact mul_le_mul_of_nonneg_left hSigned hl

/-- The signed beta(n+1)-evolved right Krylov combination is the
source of the FROZEN-beta(n) actual physical transfer, not a surrogate
positive observable or an independently chosen conditional law. -/
theorem fineRightKrylovOriginalVacuumMeanJointBCF_rightLinkDifference_abs_le_signedSourceL1
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
        (halfExtent (n + 1)) 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
        (halfExtent (n + 1)) 2)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    |fineRightKrylovOriginalVacuumMeanJointBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a (z.1, Function.update z.2 e g) -
      fineRightKrylovOriginalVacuumMeanJointBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a z| ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)‖⁻¹ *
        (((Real.exp (8 * beta n)) ^ 2 - 1) /
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) z.2) *
        (∫ A, ‖((∑ j : Fin (r + 1), a j •
          physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (j : ℕ)) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent (n + 1)) 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
            (halfExtent (n + 1)) 2)) A‖
          ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
            (halfExtent (n + 1)) 2)) := by
  simpa only [fineRightKrylovOriginalVacuumMeanJointBCF,
    normalizedPhysicalOneSlabVacuumMeanJointBCF] using
    (normalizedPhysicalOneSlabVacuumReceiverBCF_rightLinkDifference_abs_le_signedSourceL1
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)) z.2 e g)

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
