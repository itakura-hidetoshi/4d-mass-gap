import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferKernelUnitNormDensityModulusV5_PZ37AEI
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationDiagnostic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEJ — literal original Wilson action controls the physical transfer norm

For every finite H, positive SU(N) rank and nonnegative Wilson coupling beta,
the original one-slab action obeys a global finite-volume bound
  A_H <= 2 * (length spatial plaquettes + length spatial crossing links).
Consequently the actual literal one-slab Wilson kernel obeys
  exp(-beta * globalActionBudget H) <= K_H(A,B) <= 1.

The lower bound is transferred through the ACTUAL Haar L2 matrix coefficient
on the genuine Gauss-law constant unit vector. Together with AEI's genuine
unnormalized physical operator U=1 this gives a TWO-SIDED finite-volume norm
certificate. No spectral gap, H-uniform norm floor, numerical finite net,
replacement transfer law or continuum mass gap is assumed or asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AEJ_group (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4Q2PZ37AEJ_compact (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4Q2PZ37AEJ_countable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4Q2PZ37AEJ_measurable (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4Q2PZ37AEJ_borel (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4Q2PZ37AEJ_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The ACTUAL unnormalized physical Gauss-law transfer norm is at least
the explicit positive lower bound of the literal Wilson one-slab kernel.
The constant-one Haar vector lies in the real physical Hilbert subspace,
so this is not an ambient-only assertion. -/
theorem p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let v := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let k := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
    H beta
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  have hK :
      ∀ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        k ≤ periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2 := by
    intro p
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_le_kernel
      H N hN beta hbeta p.1 p.2
  have hKernelIntegrable :
      Integrable (fun p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2) μ := by
    simpa only [μ] using
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_integrable
        H N hN beta hbeta
  have hIntegral :
      k ≤ ∫ p :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta p.1 p.2 ∂μ := by
    have hMono :=
      integral_mono (integrable_const k) hKernelIntegrable hK
    have hConst :
        (∫ _ :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          k ∂μ) = k := by simp
    exact hConst ▸ hMono
  have hPair : k ≤ inner ℝ (T v) v := by
    change k ≤ inner ℝ
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H N hN beta hbeta
        (Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ)))
      (Lp.const 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) (1 : ℝ))
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairing_const_one_eq_integral]
    exact hIntegral
  have hv : ‖v‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  have hApply : ‖T v‖ ≤ ‖T‖ * ‖v‖ :=
    ContinuousLinearMap.le_opNorm T v
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta =
        k := rfl
    _ ≤ inner ℝ (T v) v := hPair
    _ ≤ ‖T v‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖v‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right hApply (norm_nonneg v)
    _ = ‖T‖ := by rw [hv]; ring

/-- Genuine unnormalized physical transfer, arbitrary rank and finite volume:
explicit strictly positive lower and upper unit norm bounds. -/
theorem p4Q2PZ37AEJ_originalPhysicalTransfer_explicitTwoSidedNorm
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ∧
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ∧
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ ≤ 1 := by
  exact ⟨
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos
      H beta,
    p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
      H N hN beta hbeta,
    p4Q2PZ37AEI_originalPhysicalTransfer_norm_le_one
      H N hN beta hbeta⟩

/-- Quantitative reciprocal bound for the ORIGINAL unnormalized physical
transfer. Its volume dependence is explicit in the ACTUAL Wilson action. -/
theorem p4Q2PZ37AEJ_originalPhysicalTransfer_inverseNorm_le_expAction
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ ≤
      Real.exp (beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) := by
  have hLower :=
    p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
      H N hN beta hbeta
  have hk :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H beta
  have ht : 0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    hk.trans_le hLower
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
        H beta)⁻¹ := (inv_le_inv₀ hk ht).2 hLower
    _ = Real.exp (beta *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) := by
      unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      rw [Real.exp_neg, inv_inv]


/-- Nonnegative density-error budgets are monotone under a larger
inverse-transfer bound, with the SAME positive rho floor. -/
theorem p4Q2PZ37AEJ_realDoubleDivision_monotone
    (a b m delta : ℝ)
    (hm : 0 < m) (hdelta : 0 ≤ delta) (hab : a ≤ b) :
    ((a / m) * delta) / m ≤ ((b / m) * delta) / m := by
  have hDiv : a / m ≤ b / m :=
    (div_le_div_iff_of_pos_right hm).2 hab
  have hMul : (a / m) * delta ≤ (b / m) * delta :=
    mul_le_mul_of_nonneg_right hDiv hdelta
  exact (div_le_div_iff_of_pos_right hm).2 hMul

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "rho" => continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Tnorm" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "actionBudget" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "E" => Real.exp (b0 * actionBudget)
local notation "N" => p4Q2PZ37AEF_originalCenteredCovarianceNumerator H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H

/-- Actual SU(2) fixed-coupling Perron/transfer norm: no replacement
physical Hilbert carrier or non-original normalization is used. -/
theorem p4Q2PZ37AEJ_originalFixedCouplingTransfer_explicitTwoSidedNorm :
    0 < k ∧ k ≤ Tnorm ∧ Tnorm ≤ 1 := by
  exact p4Q2PZ37AEJ_originalPhysicalTransfer_explicitTwoSidedNorm
    H 2 (by norm_num) b0 hb0

/-- The true inverse unnormalized SU(2) transfer norm has a completely
explicit finite-volume budget computed from the literal Wilson action. -/
theorem p4Q2PZ37AEJ_originalFixedCouplingTransfer_inverseNorm_le_expAction :
    Tnorm⁻¹ ≤ E := by
  exact p4Q2PZ37AEJ_originalPhysicalTransfer_inverseNorm_le_expAction
    H 2 (by norm_num) b0 hb0

/-- The exact original q=‖T‖⁻¹/rho has a finite-volume explicit
oscillation estimate, assuming only a certified real rho lower floor
and an actual rho error modulus. The transfer norm is no longer a
separate numerical input. -/
theorem p4Q2PZ37AEJ_originalDensity_explicitActionModulus
    (m delta R : ℝ)
    (hm : 0 < m) (hdelta : 0 ≤ delta)
    (hRhoLower : ∀ z : Pair, m ≤ rho z)
    (hRhoMod : ∀ z w : Pair, D z w < R →
      |rho z - rho w| ≤ delta) :
    ∀ z w : Pair, D z w < R →
      |q b0 hb0 z - q b0 hb0 w| ≤
        ((E / m) * delta) / m := by
  have hPrev :=
    p4Q2PZ37AEI_originalDensity_variation_fromTrueSqrtDensity
      H m delta R hm hRhoLower hRhoMod
  have hBound :=
    p4Q2PZ37AEJ_realDoubleDivision_monotone
      Tnorm⁻¹ E m delta hm hdelta
      (p4Q2PZ37AEJ_originalFixedCouplingTransfer_inverseNorm_le_expAction H)
  intro z w hzw
  exact (hPrev z w hzw).trans hBound


/-- A TRUE two-sided sample table on an ORIGINAL SU(2) boundary-pair
D_H net makes the q modulus numerically explicit in the already
defined finite-H Wilson action budget, without a transfer norm input. -/
theorem p4Q2PZ37AEJ_originalFiniteNet_explicitDensityModulus
    (s : Finset Pair) (r epsilon m R : ℝ)
    (heps : 0 < epsilon) (hm : epsilon < m) (hRle : R ≤ r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hRhoMod : ∀ z w : Pair, D z w < r →
      |rho z - rho w| < epsilon)
    (hSampleLower : ∀ a ∈ s, m ≤ rho a) :
    ∀ z w : Pair, D z w < R →
      |q b0 hb0 z - q b0 hb0 w| ≤
        ((E / (m - epsilon)) * epsilon) / (m - epsilon) := by
  have hPos : 0 < m - epsilon := sub_pos.mpr hm
  have hRhoFloor : ∀ z : Pair, m - epsilon ≤ rho z := fun z =>
    (p4Q2PZ37AEI_originalFiniteNet_sampleLower_givesGlobalRhoFloor
      H s r epsilon m hNet hRhoMod hSampleLower z).le
  have hOsc : ∀ z w : Pair, D z w < R →
      |rho z - rho w| ≤ epsilon := by
    intro z w hzw
    exact (hRhoMod z w (lt_of_lt_of_le hzw hRle)).le
  exact p4Q2PZ37AEJ_originalDensity_explicitActionModulus
    H (m - epsilon) epsilon R hPos heps.le hRhoFloor hOsc

/-- True finite-net lower rho samples also furnish a genuine upper
bound on the SAME original JQ Perron density, using the explicit
Wilson-action inverse transfer budget. -/
theorem p4Q2PZ37AEJ_originalFiniteNet_explicitDensityUpper
    (s : Finset Pair) (r epsilon m : ℝ)
    (hm : epsilon < m)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hRhoMod : ∀ z w : Pair, D z w < r →
      |rho z - rho w| < epsilon)
    (hSampleLower : ∀ a ∈ s, m ≤ rho a) :
    ∀ z : Pair, q b0 hb0 z ≤ E / (m - epsilon) := by
  have hPos : 0 < m - epsilon := sub_pos.mpr hm
  have hRhoFloor : ∀ z : Pair, m - epsilon ≤ rho z := fun z =>
    (p4Q2PZ37AEI_originalFiniteNet_sampleLower_givesGlobalRhoFloor
      H s r epsilon m hNet hRhoMod hSampleLower z).le
  have hInvT : Tnorm⁻¹ ≤ E :=
    p4Q2PZ37AEJ_originalFixedCouplingTransfer_inverseNorm_le_expAction H
  intro z
  rw [p4Q2PZ37AEG_originalDensity_exactVacuumCancellation H z]
  have hRho : 0 < rho z :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 z
  have hRhoInv : (rho z)⁻¹ ≤ (m - epsilon)⁻¹ :=
    (inv_le_inv₀ hPos hRho).2 (hRhoFloor z)
  calc
    Tnorm⁻¹ / rho z = Tnorm⁻¹ * (rho z)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ E * (rho z)⁻¹ :=
      mul_le_mul_of_nonneg_right hInvT (inv_nonneg.mpr hRho.le)
    _ ≤ E * (m - epsilon)⁻¹ :=
      mul_le_mul_of_nonneg_left hRhoInv (Real.exp_nonneg _)
    _ = E / (m - epsilon) := by rw [div_eq_mul_inv]

/-- Conditional TRUE joint rho upper/lower samples give a two-sided
global Perron density interval. The transfer-norm bounds themselves
are unconditional finite-volume Wilson physics. -/
theorem p4Q2PZ37AEJ_originalFiniteNet_explicitTwoSidedDensity
    (s : Finset Pair) (r epsilon m M : ℝ)
    (heps : 0 < epsilon) (hm : epsilon < m)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hRhoMod : ∀ z w : Pair, D z w < r →
      |rho z - rho w| < epsilon)
    (hSampleLower : ∀ a ∈ s, m ≤ rho a)
    (hSampleUpper : ∀ a ∈ s, rho a ≤ M) :
    0 < (1 : ℝ) / (M + epsilon) ∧
      ∀ z : Pair,
        (1 : ℝ) / (M + epsilon) ≤ q b0 hb0 z ∧
        q b0 hb0 z ≤ E / (m - epsilon) := by
  obtain ⟨hPositive, hLower⟩ :=
    p4Q2PZ37AEI_originalFiniteNet_unitNorm_densityFloor
      H s r epsilon M heps hNet hRhoMod hSampleUpper
  have hUpper :=
    p4Q2PZ37AEJ_originalFiniteNet_explicitDensityUpper
      H s r epsilon m hm hNet hRhoMod hSampleLower
  exact ⟨hPositive, fun z => ⟨hLower z, hUpper z⟩⟩


/-- The true physical Wilson numerator/covariance oscillation, now
with BOTH transfer-norm and q-modulus certificates reduced to literal
Wilson action and TRUE rho sample bounds. Numerator majorants and
moduli remain explicit, uncomputed physical verification obligations. -/
theorem p4Q2PZ37AEJ_originalFiniteNet_explicitCovarianceModulus
    (e : Link) (s : Finset Pair)
    (r epsilon m M R Nmax dN : ℝ)
    (heps : 0 < epsilon) (hm : epsilon < m) (hRle : R ≤ r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hRhoMod : ∀ z w : Pair, D z w < r →
      |rho z - rho w| < epsilon)
    (hSampleLower : ∀ a ∈ s, m ≤ rho a)
    (hSampleUpper : ∀ a ∈ s, rho a ≤ M)
    (hNmax : ∀ z : Pair, |N e z| ≤ Nmax)
    (hNmod : ∀ z w : Pair, D z w < R →
      |N e z - N e w| ≤ dN) :
    ∀ z w : Pair, D z w < R →
      |C b0 hb0 e z - C b0 hb0 e w| ≤
        (dN + (Nmax / ((1 : ℝ) / (M + epsilon))) *
          ((E / (m - epsilon)) * epsilon / (m - epsilon))) /
          ((1 : ℝ) / (M + epsilon)) := by
  have hQmod :=
    p4Q2PZ37AEJ_originalFiniteNet_explicitDensityModulus
      H s r epsilon m R heps hm hRle hNet hRhoMod hSampleLower
  have hAEH :=
    p4Q2PZ37AEH_originalCertifiedNet_givesCovarianceModulus
      H e s r epsilon M 1 R Nmax dN
      ((E / (m - epsilon)) * epsilon / (m - epsilon))
      heps hNet hRhoMod hSampleUpper
      (p4Q2PZ37AEI_originalFixedCouplingTransfer_norm_in_pos_unit H).2
      hNmax hNmod hQmod
  simpa only [one_mul] using hAEH

/-- Exact original SU(2) gauge-opposite two-ball Haar second-moment
floor using the genuine Wilson action in the density-error budget.
The positive amplitude-vs-error margin is explicitly required; no
GI threshold or continuum gap is inferred from the bound. -/
theorem p4Q2PZ37AEJ_originalFiniteNet_explicitDoubleMomentFloor
    (e : Link) (a : Pair) (s : Finset Pair)
    (r epsilon m M R Nmax dN : ℝ)
    (heps : 0 < epsilon) (hm : epsilon < m)
    (hR : 0 < R) (hRle : R ≤ r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hRhoMod : ∀ z w : Pair, D z w < r →
      |rho z - rho w| < epsilon)
    (hSampleLower : ∀ x ∈ s, m ≤ rho x)
    (hSampleUpper : ∀ x ∈ s, rho x ≤ M)
    (hNmax : ∀ z : Pair, |N e z| ≤ Nmax)
    (hNmod : ∀ z w : Pair, D z w < R →
      |N e z - N e w| ≤ dN)
    (hAmp :
      (dN + (Nmax / ((1 : ℝ) / (M + epsilon))) *
        ((E / (m - epsilon)) * epsilon / (m - epsilon))) /
        ((1 : ℝ) / (M + epsilon)) < C b0 hb0 e a) :
    (C b0 hb0 e a -
      (dN + (Nmax / ((1 : ℝ) / (M + epsilon))) *
        ((E / (m - epsilon)) * epsilon / (m - epsilon))) /
        ((1 : ℝ) / (M + epsilon))) ^ 2 *
        (2 * (min (R / (2 * (Fintype.card Link : ℝ) + 1)) 2 / 4) ^
          (8 * Fintype.card Link)) ≤ S b0 hb0 e := by
  have hQmod :=
    p4Q2PZ37AEJ_originalFiniteNet_explicitDensityModulus
      H s r epsilon m R heps hm hRle hNet hRhoMod hSampleLower
  have hAEH :=
    p4Q2PZ37AEH_originalCertifiedNet_givesDoubleMomentFloor
      H e a s r epsilon M 1 R Nmax dN
      ((E / (m - epsilon)) * epsilon / (m - epsilon))
      heps hR hNet hRhoMod hSampleUpper
      (p4Q2PZ37AEI_originalFixedCouplingTransfer_norm_in_pos_unit H).2
      hNmax hNmod hQmod
      (by simpa only [one_mul] using hAmp)
  simpa only [one_mul] using hAEH

end GroundStatePosteriorJoint

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEJ_originalPhysicalTransfer_norm_ge_WilsonActionFloor
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEJ_originalPhysicalTransfer_explicitTwoSidedNorm
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEJ_originalPhysicalTransfer_inverseNorm_le_expAction

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEJ_realDoubleDivision_monotone
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEJ_originalFixedCouplingTransfer_explicitTwoSidedNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEJ_originalFixedCouplingTransfer_inverseNorm_le_expAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEJ_originalDensity_explicitActionModulus

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEJ_originalFiniteNet_explicitDensityModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEJ_originalFiniteNet_explicitDensityUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEJ_originalFiniteNet_explicitTwoSidedDensity

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEJ_originalFiniteNet_explicitCovarianceModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEJ_originalFiniteNet_explicitDoubleMomentFloor
