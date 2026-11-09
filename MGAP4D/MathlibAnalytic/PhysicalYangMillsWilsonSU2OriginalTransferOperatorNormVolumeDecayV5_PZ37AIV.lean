import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferUniformVolumeVanishingV5_PZ37AIU
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFiberDistortion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumKernelHarnack
import MGAP4D.MathlibAnalytic.RealL2ExternalTensor
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIV — original transfer operator norms and normalization scale

Preserve the ORIGINAL complete SU(2) Wilson action, both endpoint spatial
halfweights, genuine normalized Haar, signed ZW physical source, AIG's original
margin and strict negative region, all assumptions/results/roots, pinned Lean
and mathlib, and the unchanged heartbeat budgets.

AIU bounds the image of one original signed source. This leaf instead bounds
the EXISTING ambient Haar L2 operator R and its EXISTING Gauss-law physical
restriction P. For beta>=0, the original full kernel obeys
  integral |K_beta|^2 d(mu_H product mu_H) <= Zcross_H(2*beta),
so ||P|| <= ||R|| <= ||K_beta||_L2 <= sqrt(Zcross_H(2*beta)).
The doubled coupling arises only from squaring the original kernel at beta.

The existing strictly positive continuous physical top eigenvector and its
EXACT original-kernel integral equation yield the additional sandwich
  exp(-2*beta*p_H) * Zcross_H(beta) <= ||P|| <= Zcross_H(beta).
Both a.e. representative bridges and the left/right Haar conventions are
handled explicitly. No normalized operator is substituted for the original.

With AIU's rho(beta)=-log z(beta)>0 at every beta>0, these give scalar limits
of BOTH operator norms to zero as H grows at FIXED positive beta, uniform
control of the ambient unit ball, and no positive volume-uniform raw physical
norm floor. Different H retain their original different Hilbert spaces.
The already-existing inverse-norm normalization scale lies between
  exp(rho(beta)*p_H) and exp((2*beta+rho(beta))*p_H),
and tends to +infinity. The already-existing normalized physical operator
still has norm exactly one. At beta0=log(3/2)/64,
  ||P|| <= exp(-(H+1)^3/16),
  ||P||^(-1) >= exp((H+1)^3/16).

No common-Hilbert-space operator limit, normalized coercivity or gap,
negative eigenvalue, fixed-H all-positive-coupling full-margin half-Haar
extension, Hamiltonian spectral gap, or continuum four-dimensional Yang-Mills
mass gap is inferred. AIU's original negative-region results remain intact.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIV_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIV_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIV_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIV_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIV_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local instance p4Q2PZ37AIV_probability : IsProbabilityMeasure
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

local instance p4Q2PZ37AIV_pair_probability : IsProbabilityMeasure
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure]
  infer_instance

/-- The complete action retains both nonnegative spatial half-actions.
The original crossing action is therefore a pointwise lower bound. -/
theorem p4Q2PZ37AIV_originalCrossingAction_le_fullSlabAction
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B := by
  have hA := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
    H 2 (by norm_num : 0 < (2 : ℕ)) A
  have hB := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
    H 2 (by norm_num : 0 < (2 : ℕ)) B
  unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
  linarith only [hA, hB]

/-- Exact squaring identity for the unchanged complete Boltzmann kernel.
This identity is valid at every real coupling. -/
theorem p4Q2PZ37AIV_originalKernel_sq_eq_doubledCoupling
    (beta : ℝ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta A B) ^ 2 =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 (2 * beta) A B := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    pow_two, ← Real.exp_add]
  congr 1
  ring

/-- At nonnegative coupling the original kernel square is bounded by the
actual crossing kernel at twice that coupling. The two spatial halfweights
are accounted for by their nonnegative original actions. -/
theorem p4Q2PZ37AIV_originalKernel_sq_le_doubledCrossing
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta A B) ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 (2 * beta) A B := by
  rw [p4Q2PZ37AIV_originalKernel_sq_eq_doubledCoupling H beta A B,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_eq_boltzmann]
  apply Real.exp_le_exp.mpr
  have hScaled := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIV_originalCrossingAction_le_fullSlabAction H A B)
    (show 0 ≤ 2 * beta by positivity)
  nlinarith only [hScaled]

/-- Joint integrability concerns the actual crossing kernel and genuine
product Haar. Compact continuity supplies the full Fubini hypothesis. -/
theorem p4Q2PZ37AIV_originalCrossingKernel_pair_integrable (beta : ℝ) :
    Integrable
      (fun P :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
          H 2 beta P.1 P.2)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel_continuous
    H 2 beta).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The pair-Haar crossing integral equals the genuine original partition.
Fubini integrates the RIGHT boundary first, matching AIF's proved identity;
no unproved interchange of left and right Haar conventions is used. -/
theorem p4Q2PZ37AIV_originalCrossingKernel_pair_integral (beta : ℝ) :
    (∫ P :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 beta P.1 P.2
      ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) =
      p4Q2PZ37AIF_originalCrossingPartition H beta := by
  change (∫ P :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
      H 2 beta P.1 P.2
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).prod
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) = _
  rw [integral_prod _ (p4Q2PZ37AIV_originalCrossingKernel_pair_integrable H beta)]
  simp_rw [p4Q2PZ37AIF_originalCrossingKernel_haarIntegral H beta]
  simp only [integral_const, probReal_univ, one_smul]

/-- Genuine pair-Haar squared-kernel control. This is an upper estimate
for the original full operator's Hilbert--Schmidt kernel, independent of
the sign or the choice of an input physical L2 vector. -/
theorem p4Q2PZ37AIV_originalKernelPair_normSqIntegral_le_crossingPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ P :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta P.1 P.2‖ ^ 2
      ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) ≤
      p4Q2PZ37AIF_originalCrossingPartition H (2 * beta) := by
  calc
    _ ≤ ∫ P :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 (2 * beta) P.1 P.2
      ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 := by
      apply integral_mono
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pair_norm_sq_integrable
          H 2 (by norm_num : 0 < (2 : ℕ)) beta hbeta)
        (p4Q2PZ37AIV_originalCrossingKernel_pair_integrable H (2 * beta))
      intro P
      simpa only [Real.norm_eq_abs, sq_abs] using
        p4Q2PZ37AIV_originalKernel_sq_le_doubledCrossing H beta hbeta P.1 P.2
    _ = _ := p4Q2PZ37AIV_originalCrossingKernel_pair_integral H (2 * beta)

/-- The existing pair-Haar L2 kernel vector has exactly the squared integral
of the literal full Wilson kernel as its norm square. The a.e. representative
bridge is used explicitly, so no pointwise choice of an L2 representative is
silently substituted for the physical kernel. -/
theorem p4Q2PZ37AIV_originalKernelPairL2_normSq_eq_integral
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H 2 (by norm_num) beta hbeta‖ ^ 2 =
      ∫ P :
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta P.1 P.2‖ ^ 2
        ∂periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2 := by
  rw [realL2_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H 2 (by norm_num) beta hbeta] with P hP
  rw [hP]

/-- The genuine doubled-coupling crossing partition controls the norm square
of the original full Wilson kernel in pair Haar L2. -/
theorem p4Q2PZ37AIV_originalKernelPairL2_normSq_le_crossingPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H 2 (by norm_num) beta hbeta‖ ^ 2 ≤
      p4Q2PZ37AIF_originalCrossingPartition H (2 * beta) := by
  rw [p4Q2PZ37AIV_originalKernelPairL2_normSq_eq_integral H beta hbeta]
  exact p4Q2PZ37AIV_originalKernelPair_normSqIntegral_le_crossingPartition
    H beta hbeta

/-- Taking a square root preserves the actual kernel's nonnegative norm.
The partition is the existing AIF crossing partition; no normalized transfer
or alternative kernel is introduced. -/
theorem p4Q2PZ37AIV_originalKernelPairL2_norm_le_sqrtCrossingPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H 2 (by norm_num) beta hbeta‖ ≤
      Real.sqrt (p4Q2PZ37AIF_originalCrossingPartition H (2 * beta)) := by
  have hRoot := Real.sqrt_le_sqrt
    (p4Q2PZ37AIV_originalKernelPairL2_normSq_le_crossingPartition H beta hbeta)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using hRoot

/-- The actual Fréchet--Riesz Haar L2 transfer obeys the same decaying bound.
This controls every input vector through an operator-norm estimate, beyond
AIU's estimate for the single original signed source image. -/
theorem p4Q2PZ37AIV_originalAmbientTransfer_norm_le_sqrtCrossingPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖ ≤
      Real.sqrt (p4Q2PZ37AIF_originalCrossingPartition H (2 * beta)) :=
  (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_norm_le
    H 2 (by norm_num) beta hbeta).trans
      (p4Q2PZ37AIV_originalKernelPairL2_norm_le_sqrtCrossingPartition H beta hbeta)

/-- Restrict the unchanged ambient operator to its existing Gauss-law
physical Hilbert space. Restriction cannot increase its norm. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_sqrtCrossingPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖ ≤
      Real.sqrt (p4Q2PZ37AIF_originalCrossingPartition H (2 * beta)) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_le_ambient
    H 2 (by norm_num) beta hbeta).trans
      (p4Q2PZ37AIV_originalAmbientTransfer_norm_le_sqrtCrossingPartition H beta hbeta)

/-- At every finite volume and every strictly positive coupling, the
genuine partition yields a strict improvement over LX's bound by one.
This concerns the original unnormalized physical transfer. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_norm_lt_one
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta.le‖ < 1 := by
  have hPartition : p4Q2PZ37AIF_originalCrossingPartition H (2 * beta) < 1 :=
    p4Q2PZ37AIP_originalCrossingPartition_lt_one H (2 * beta)
      (mul_pos (by norm_num) hbeta)
  have hRoot :
      Real.sqrt (p4Q2PZ37AIF_originalCrossingPartition H (2 * beta)) < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt
      (p4Q2PZ37AIF_originalCrossingPartition_pos H (2 * beta)).le hPartition
  exact (p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_sqrtCrossingPartition
    H beta hbeta.le).trans_lt hRoot

/-- Abstract compact positive-eigenfunction comparison with a uniform upper
row mass. Keeping the scalar eigenvalue abstract separates extrema and
integration from the concrete physical operator's typeclass reductions. -/
theorem p4Q2PZ37AIV_compactPositiveEigenfunction_le_uniformRowMass
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X]
    (mu : Measure X) (K : X → X → ℝ) (v : X → ℝ) (lambda c : ℝ)
    (hv : Continuous v) (hvPos : ∀ A : X, 0 < v A)
    (hKNonneg : ∀ A B : X, 0 ≤ K A B)
    (hKInt : ∀ B : X, Integrable (fun A : X => K A B) mu)
    (hvKInt : ∀ B : X, Integrable (fun A : X => v A * K A B) mu)
    (hEigen : ∀ B : X, lambda * v B = ∫ A : X, v A * K A B ∂mu)
    (hRow : ∀ B : X, (∫ A : X, K A B ∂mu) ≤ c) : lambda ≤ c := by
  obtain ⟨B, _, hMax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hv.continuousOn
  have hWeighted : lambda * v B ≤ c * v B := by
    calc
      lambda * v B = ∫ A : X, v A * K A B ∂mu := hEigen B
      _ ≤ ∫ A : X, v B * K A B ∂mu :=
        integral_mono (hvKInt B) ((hKInt B).const_mul (v B))
          (fun A => mul_le_mul_of_nonneg_right (hMax (Set.mem_univ A)) (hKNonneg A B))
      _ = v B * (∫ A : X, K A B ∂mu) := integral_const_mul _ _
      _ ≤ v B * c := mul_le_mul_of_nonneg_left (hRow B) (hvPos B).le
      _ = c * v B := mul_comm _ _
  exact (mul_le_mul_iff_left₀ (hvPos B)).mp hWeighted

/-- The corresponding abstract lower comparison uses the positive attained
minimum. No volume-uniform lower bound on the eigenfunction is assumed. -/
theorem p4Q2PZ37AIV_uniformRowMass_le_compactPositiveEigenfunction
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X]
    (mu : Measure X) (K : X → X → ℝ) (v : X → ℝ) (lambda c : ℝ)
    (hv : Continuous v) (hvPos : ∀ A : X, 0 < v A)
    (hKNonneg : ∀ A B : X, 0 ≤ K A B)
    (hKInt : ∀ B : X, Integrable (fun A : X => K A B) mu)
    (hvKInt : ∀ B : X, Integrable (fun A : X => v A * K A B) mu)
    (hEigen : ∀ B : X, lambda * v B = ∫ A : X, v A * K A B ∂mu)
    (hRow : ∀ B : X, c ≤ ∫ A : X, K A B ∂mu) : c ≤ lambda := by
  obtain ⟨B, _, hMin⟩ :=
    isCompact_univ.exists_isMinOn Set.univ_nonempty hv.continuousOn
  have hWeighted : v B * c ≤ v B * lambda := by
    calc
      v B * c ≤ v B * (∫ A : X, K A B ∂mu) :=
        mul_le_mul_of_nonneg_left (hRow B) (hvPos B).le
      _ = ∫ A : X, v B * K A B ∂mu := (integral_const_mul _ _).symm
      _ ≤ ∫ A : X, v A * K A B ∂mu :=
        integral_mono ((hKInt B).const_mul (v B)) (hvKInt B)
          (fun A => mul_le_mul_of_nonneg_right (hMin (Set.mem_univ A)) (hKNonneg A B))
      _ = lambda * v B := (hEigen B).symm
      _ = v B * lambda := mul_comm _ _
  exact (mul_le_mul_iff_right₀ (hvPos B)).mp hWeighted

section PZ37AIVPhysicalNormBounds

variable (H : ℕ)

local notation "CfgAIV" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muAIV" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pAIV" => p4Q2PZ37AFZ_plaquetteCount H
local notation "WAIV" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "KAIV" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "KCAIV" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "ZAIV" => p4Q2PZ37AIF_originalCrossingPartition H

/-- A fully typed insertion into the existing jointly continuous full
kernel fixes both product types before composition is elaborated. -/
theorem p4Q2PZ37AIV_originalFullKernel_leftContinuous
    (beta : ℝ) (B : CfgAIV) :
    Continuous (fun A : CfgAIV => KAIV beta A B) := by
  have hInsert : Continuous (fun A : CfgAIV => (A, B)) :=
    (continuous_id : Continuous (fun A : CfgAIV => A)).prodMk
      (continuous_const : Continuous (fun _ : CfgAIV => B))
  have hJoint : Continuous (fun P : CfgAIV × CfgAIV => KAIV beta P.1 P.2) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous H 2 beta
  have hKernel := Continuous.comp'
    (f := fun A : CfgAIV => (A, B))
    (g := fun P : CfgAIV × CfgAIV => KAIV beta P.1 P.2) hJoint hInsert
  change Continuous (fun A : CfgAIV => KAIV beta A B) at hKernel
  exact hKernel

/-- Both ORIGINAL spatial halfweights have this explicit finite-volume floor.
The complete spatial Wilson action is bounded by twice its original count. -/
theorem p4Q2PZ37AIV_originalSpatialHalfweight_ge_expFloor
    (beta : ℝ) (hbeta : 0 ≤ beta) (A : CfgAIV) :
    Real.exp (-(beta * pAIV)) ≤ Real.exp (-(beta / 2) * WAIV A) := by
  have hW : WAIV A ≤ 2 * pAIV :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_le_two_mul_length
      H 2 (by norm_num) A
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hW hbeta]

/-- The complete ORIGINAL kernel is bounded above by its crossing factor,
after separately bounding both unchanged endpoint halfweights by one. -/
theorem p4Q2PZ37AIV_originalFullKernel_le_crossingKernel
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : CfgAIV) :
    KAIV beta A B ≤ KCAIV beta A B := by
  have hA := p4Q2PZ37AIU_originalSpatialHalfweight_le_one H beta hbeta A
  have hB := p4Q2PZ37AIU_originalSpatialHalfweight_le_one H beta hbeta B
  have hKC := (p4Q2PZ37AIN_originalCrossingKernel_pos H beta A B).le
  change Real.exp (-(beta / 2) * WAIV A) * KCAIV beta A B *
    Real.exp (-(beta / 2) * WAIV B) ≤ KCAIV beta A B
  calc
    _ ≤ (1 * KCAIV beta A B) * Real.exp (-(beta / 2) * WAIV B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hA hKC) (Real.exp_pos _).le
    _ ≤ (1 * KCAIV beta A B) * 1 :=
      mul_le_mul_of_nonneg_left hB (by simpa only [one_mul] using hKC)
    _ = KCAIV beta A B := by ring

/-- The original complete kernel retains a crossing-factor lower bound,
with the explicit product of the two ORIGINAL endpoint halfweight floors. -/
theorem p4Q2PZ37AIV_originalFullKernel_ge_halfweightFloorCrossing
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : CfgAIV) :
    Real.exp (-(2 * beta * pAIV)) * KCAIV beta A B ≤ KAIV beta A B := by
  have hA := p4Q2PZ37AIV_originalSpatialHalfweight_ge_expFloor H beta hbeta A
  have hB := p4Q2PZ37AIV_originalSpatialHalfweight_ge_expFloor H beta hbeta B
  have hKC := (p4Q2PZ37AIN_originalCrossingKernel_pos H beta A B).le
  have hExp : Real.exp (-(beta * pAIV)) * Real.exp (-(beta * pAIV)) =
      Real.exp (-(2 * beta * pAIV)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  change Real.exp (-(2 * beta * pAIV)) * KCAIV beta A B ≤
    Real.exp (-(beta / 2) * WAIV A) * KCAIV beta A B *
      Real.exp (-(beta / 2) * WAIV B)
  calc
    _ = (Real.exp (-(beta * pAIV)) * KCAIV beta A B) *
        Real.exp (-(beta * pAIV)) := by rw [← hExp]; ring
    _ ≤ (Real.exp (-(beta / 2) * WAIV A) * KCAIV beta A B) *
        Real.exp (-(beta * pAIV)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hA hKC) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left hB
      (mul_nonneg (Real.exp_pos _).le hKC)

/-- Upper row-mass estimate for the full ORIGINAL kernel with genuine Haar.
AIU's left crossing mass already contains the explicit symmetry bridge. -/
theorem p4Q2PZ37AIV_originalFullKernel_leftHaarIntegral_le_crossingPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : CfgAIV) :
    (∫ A : CfgAIV, KAIV beta A B ∂muAIV) ≤ ZAIV beta := by
  have hK : Continuous (fun A : CfgAIV => KAIV beta A B) :=
    p4Q2PZ37AIV_originalFullKernel_leftContinuous H beta B
  have hKC := p4Q2PZ37AIN_originalCrossingKernel_leftContinuous H beta B
  calc
    _ ≤ ∫ A : CfgAIV, KCAIV beta A B ∂muAIV :=
      integral_mono
        (hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hKC.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (fun A => p4Q2PZ37AIV_originalFullKernel_le_crossingKernel H beta hbeta A B)
    _ = ZAIV beta := p4Q2PZ37AIU_originalCrossingKernel_leftHaarIntegral H beta hbeta B

/-- Lower row-mass estimate retaining the genuine crossing partition and
both original spatial halfweights. No new kernel or Haar law is defined. -/
theorem p4Q2PZ37AIV_originalFullKernel_leftHaarIntegral_ge_halfweightFloorCrossingPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : CfgAIV) :
    Real.exp (-(2 * beta * pAIV)) * ZAIV beta ≤
      ∫ A : CfgAIV, KAIV beta A B ∂muAIV := by
  have hK : Continuous (fun A : CfgAIV => KAIV beta A B) :=
    p4Q2PZ37AIV_originalFullKernel_leftContinuous H beta B
  have hKC := p4Q2PZ37AIN_originalCrossingKernel_leftContinuous H beta B
  calc
    _ = ∫ A : CfgAIV, Real.exp (-(2 * beta * pAIV)) * KCAIV beta A B ∂muAIV := by
      rw [integral_const_mul,
        p4Q2PZ37AIU_originalCrossingKernel_leftHaarIntegral H beta hbeta B]
    _ ≤ _ := integral_mono
      ((continuous_const.mul hKC).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fun A => p4Q2PZ37AIV_originalFullKernel_ge_halfweightFloorCrossing H beta hbeta A B)

/-- The existing physical top eigenvector is used through its existing
continuous representative on BOTH sides of the true-kernel equation.
The passage from the Haar-L2 class under the integral is explicitly a.e. -/
theorem p4Q2PZ37AIV_originalContinuousVacuum_eigenIntegral
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : CfgAIV) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (by norm_num) beta hbeta B =
      ∫ A : CfgAIV,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 (by norm_num) beta hbeta A * KAIV beta A B ∂muAIV := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_topNorm_mul_eq_integral_kernel]
  apply integral_congr_ae
  filter_upwards
    [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_ae_eq_existing
      H 2 (by norm_num) beta hbeta] with A hA
  rw [hA]

/-- The norm of the EXISTING physical gauge-invariant Haar-L2 transfer is
at most the genuine crossing partition. The positive continuous top
eigenvector attains its maximum on the original compact boundary space. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_crossingPartition
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖ ≤ ZAIV beta := by
  let v : CfgAIV → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H 2 (by norm_num) beta hbeta
  have hv : Continuous v :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H 2 (by norm_num) beta hbeta
  have hKInt (B : CfgAIV) : Integrable (fun A : CfgAIV => KAIV beta A B) muAIV :=
    (p4Q2PZ37AIV_originalFullKernel_leftContinuous H beta B).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hvKInt (B : CfgAIV) : Integrable (fun A : CfgAIV => v A * KAIV beta A B) muAIV :=
    (hv.mul (p4Q2PZ37AIV_originalFullKernel_leftContinuous H beta B)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact p4Q2PZ37AIV_compactPositiveEigenfunction_le_uniformRowMass
    (X := CfgAIV) muAIV (KAIV beta) v
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖ (ZAIV beta)
    hv
    (fun A =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H 2 (by norm_num) beta hbeta A)
    (fun A B =>
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H 2 beta A B).le)
    hKInt hvKInt
    (fun B => p4Q2PZ37AIV_originalContinuousVacuum_eigenIntegral H beta hbeta B)
    (fun B =>
      p4Q2PZ37AIV_originalFullKernel_leftHaarIntegral_le_crossingPartition H beta hbeta B)

/-- The norm of the SAME physical transfer also retains a genuine
crossing-partition lower bound. The existing positive continuous top
eigenvector attains a positive minimum at this finite original volume. -/
theorem p4Q2PZ37AIV_originalCrossingPartition_mul_halfweightFloor_le_physicalTransferNorm
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(2 * beta * pAIV)) * ZAIV beta ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ := by
  let v : CfgAIV → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H 2 (by norm_num) beta hbeta
  have hv : Continuous v :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H 2 (by norm_num) beta hbeta
  have hKInt (B : CfgAIV) : Integrable (fun A : CfgAIV => KAIV beta A B) muAIV :=
    (p4Q2PZ37AIV_originalFullKernel_leftContinuous H beta B).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hvKInt (B : CfgAIV) : Integrable (fun A : CfgAIV => v A * KAIV beta A B) muAIV :=
    (hv.mul (p4Q2PZ37AIV_originalFullKernel_leftContinuous H beta B)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact p4Q2PZ37AIV_uniformRowMass_le_compactPositiveEigenfunction
    (X := CfgAIV) muAIV (KAIV beta) v
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) beta hbeta‖ (Real.exp (-(2 * beta * pAIV)) * ZAIV beta)
    hv
    (fun A =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H 2 (by norm_num) beta hbeta A)
    (fun A B =>
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H 2 beta A B).le)
    hKInt hvKInt
    (fun B => p4Q2PZ37AIV_originalContinuousVacuum_eigenIntegral H beta hbeta B)
    (fun B =>
      p4Q2PZ37AIV_originalFullKernel_leftHaarIntegral_ge_halfweightFloorCrossingPartition
        H beta hbeta B)

end PZ37AIVPhysicalNormBounds

section PZ37AIVVolumeConsequences

open Filter
open scoped Topology

local notation "pAIV" => p4Q2PZ37AFZ_plaquetteCount
local notation "rhoAIV" => p4Q2PZ37AIU_originalPartitionDecayRate
local notation "dAIV" => p4Q2PZ37AIU_explicitPartitionDecayRate
local notation "TAIV" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
local notation "PAIV" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
local notation "NAIV" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator

/-- The exact original partition rate bounds the physical operator norm.
The operator is the existing Gauss-law restriction of the full Wilson transfer. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_exactRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖PAIV H 2 (by norm_num) beta hbeta‖ ≤
      Real.exp (-(rhoAIV beta * pAIV H)) := by
  have h := p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_crossingPartition H beta hbeta
  rwa [p4Q2PZ37AIU_originalCrossingPartition_eq_exp_rate H beta] at h

/-- Retain both spatial halfweights in the lower bound. Together with the
upper bound this quantifies the original finite-volume physical norm. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_norm_ge_exactRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-((2 * beta + rhoAIV beta) * pAIV H)) ≤
      ‖PAIV H 2 (by norm_num) beta hbeta‖ := by
  have h :=
    p4Q2PZ37AIV_originalCrossingPartition_mul_halfweightFloor_le_physicalTransferNorm
      H beta hbeta
  rw [p4Q2PZ37AIU_originalCrossingPartition_eq_exp_rate H beta,
    ← Real.exp_add] at h
  have hShape : -(2 * beta * pAIV H) + -(rhoAIV beta * pAIV H) =
      -((2 * beta + rhoAIV beta) * pAIV H) := by ring
  rwa [hShape] at h

/-- A completely elementary positive rate controls the same physical norm.
This statement includes beta=0; positivity of the rate needs beta>0. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_explicitRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖PAIV H 2 (by norm_num) beta hbeta‖ ≤
      Real.exp (-(dAIV beta * pAIV H)) :=
  (p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_crossingPartition H beta hbeta).trans
    (p4Q2PZ37AIU_originalCrossingPartition_le_explicitRate H beta hbeta)

/-- The actual ambient operator is controlled at the doubled-coupling
partition rate, without restricting its input to the physical subspace. -/
theorem p4Q2PZ37AIV_originalAmbientTransfer_norm_le_exactRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖TAIV H 2 (by norm_num) beta hbeta‖ ≤
      Real.exp (-((rhoAIV (2 * beta) / 2) * pAIV H)) := by
  have h := p4Q2PZ37AIV_originalAmbientTransfer_norm_le_sqrtCrossingPartition
    H beta hbeta
  rw [p4Q2PZ37AIU_originalCrossingPartition_eq_exp_rate H (2 * beta),
    ← Real.exp_half] at h
  have hShape : -(rhoAIV (2 * beta) * pAIV H) / 2 =
      -((rhoAIV (2 * beta) / 2) * pAIV H) := by ring
  rwa [hShape] at h

/-- A positive scalar rate decays along the original count. The assertion
is in the real numbers and does not identify Hilbert spaces at different H. -/
theorem p4Q2PZ37AIV_originalExponentialVolume_tendsto_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun H : ℕ => Real.exp (-(a * pAIV H))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (p4Q2PZ37AIT_originalCount_tendsto_atTop.const_mul_atTop ha)

/-- Fixed positive coupling, growing original volume: the real sequence
of ambient operator norms tends to zero. No common operator space is claimed. -/
theorem p4Q2PZ37AIV_originalAmbientTransfer_norm_tendsto_zero
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun H : ℕ => ‖TAIV H 2 (by norm_num) beta hbeta.le‖)
      atTop (𝓝 0) := by
  have hRate : 0 < rhoAIV (2 * beta) / 2 :=
    div_pos (p4Q2PZ37AIU_originalPartitionDecayRate_pos (2 * beta)
      (mul_pos (by norm_num) hbeta)) (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (p4Q2PZ37AIV_originalExponentialVolume_tendsto_zero
      (rhoAIV (2 * beta) / 2) hRate)
    (fun H => ContinuousLinearMap.opNorm_nonneg
      (TAIV H 2 (by norm_num) beta hbeta.le))
    (fun H => p4Q2PZ37AIV_originalAmbientTransfer_norm_le_exactRate H beta hbeta.le)

/-- The same scalar norm limit holds on the existing physical Hilbert
spaces. This strengthens the earlier estimate for one signed source image. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_norm_tendsto_zero
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun H : ℕ => ‖PAIV H 2 (by norm_num) beta hbeta.le‖)
      atTop (𝓝 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (p4Q2PZ37AIV_originalExponentialVolume_tendsto_zero (rhoAIV beta)
      (p4Q2PZ37AIU_originalPartitionDecayRate_pos beta hbeta))
    (fun H => ContinuousLinearMap.opNorm_nonneg
      (PAIV H 2 (by norm_num) beta hbeta.le))
    (fun H => p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_exactRate H beta hbeta.le)

/-- Uniform over every original ambient Haar L2 vector in the unit ball,
with a volume cutoff depending only on the fixed beta and eta. -/
theorem p4Q2PZ37AIV_originalAmbientTransfer_unitBall_small_eventually
    (beta : ℝ) (hbeta : 0 < beta) (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ H : ℕ, N ≤ H →
      ∀ f : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2),
        ‖f‖ ≤ 1 → ‖TAIV H 2 (by norm_num) beta hbeta.le f‖ < eta := by
  have hSmall : ∀ᶠ H : ℕ in atTop,
      ‖TAIV H 2 (by norm_num) beta hbeta.le‖ < eta :=
    (p4Q2PZ37AIV_originalAmbientTransfer_norm_tendsto_zero beta hbeta).eventually
      (gt_mem_nhds heta)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSmall
  refine ⟨N, fun H hH f hf => ?_⟩
  calc
    ‖TAIV H 2 (by norm_num) beta hbeta.le f‖ ≤
        ‖TAIV H 2 (by norm_num) beta hbeta.le‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ f
    _ ≤ ‖TAIV H 2 (by norm_num) beta hbeta.le‖ * 1 :=
      mul_le_mul_of_nonneg_left hf
        (ContinuousLinearMap.opNorm_nonneg (TAIV H 2 (by norm_num) beta hbeta.le))
    _ < eta := by simpa only [mul_one] using hN H hH

/-- The physical operator norms cannot have a positive volume-uniform
floor at a fixed positive coupling. Each finite-volume norm remains positive. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_no_uniformPositiveNormFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    ¬ ∃ eta : ℝ, 0 < eta ∧ ∀ H : ℕ,
      eta ≤ ‖PAIV H 2 (by norm_num) beta hbeta.le‖ := by
  rintro ⟨eta, heta, hFloor⟩
  have hSmall : ∀ᶠ H : ℕ in atTop,
      ‖PAIV H 2 (by norm_num) beta hbeta.le‖ < eta :=
    (p4Q2PZ37AIV_originalPhysicalTransfer_norm_tendsto_zero beta hbeta).eventually
      (gt_mem_nhds heta)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSmall
  exact (not_lt_of_ge (hFloor N)) (hN N le_rfl)

/-- The inverse of the ORIGINAL physical norm is the scale already used
by the existing normalized transfer. Its lower bound grows with volume. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_inverseNorm_ge_exactRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (rhoAIV beta * pAIV H) ≤
      ‖PAIV H 2 (by norm_num) beta hbeta‖⁻¹ := by
  have hNorm := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    H 2 (by norm_num) beta hbeta
  have h := (inv_le_inv₀ (Real.exp_pos (-(rhoAIV beta * pAIV H))) hNorm).2
    (p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_exactRate H beta hbeta)
  simpa only [Real.exp_neg, inv_inv] using h

/-- Both original spatial halfweights also give an upper bound on the
existing inverse normalization scale; no replacement normalization is defined. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_inverseNorm_le_exactRate
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖PAIV H 2 (by norm_num) beta hbeta‖⁻¹ ≤
      Real.exp ((2 * beta + rhoAIV beta) * pAIV H) := by
  have hNorm := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    H 2 (by norm_num) beta hbeta
  have h := (inv_le_inv₀ hNorm
    (Real.exp_pos (-((2 * beta + rhoAIV beta) * pAIV H)))).2
    (p4Q2PZ37AIV_originalPhysicalTransfer_norm_ge_exactRate H beta hbeta)
  simpa only [Real.exp_neg, inv_inv] using h

/-- Fix beta>0 before taking H to infinity. The scale of the already
defined physical norm normalization is unbounded and tends to +infinity. -/
theorem p4Q2PZ37AIV_originalPhysicalTransfer_inverseNorm_tendsto_atTop
    (beta : ℝ) (hbeta : 0 < beta) :
    Tendsto (fun H : ℕ => ‖PAIV H 2 (by norm_num) beta hbeta.le‖⁻¹)
      atTop atTop := by
  have hExp : Tendsto (fun H : ℕ => Real.exp (rhoAIV beta * pAIV H))
      atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (p4Q2PZ37AIT_originalCount_tendsto_atTop.const_mul_atTop
        (p4Q2PZ37AIU_originalPartitionDecayRate_pos beta hbeta))
  apply tendsto_atTop_atTop.mpr
  intro R
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hExp R
  exact ⟨N, fun H hH => (hN H hH).trans
    (p4Q2PZ37AIV_originalPhysicalTransfer_inverseNorm_ge_exactRate H beta hbeta.le)⟩

/-- Raw norm decay and growth of its inverse coexist with norm one for
the EXISTING normalized physical transfer, at one common volume cutoff. -/
theorem p4Q2PZ37AIV_originalRawDecay_and_existingNormalization_eventually
    (beta : ℝ) (hbeta : 0 < beta) (eta : ℝ) (heta : 0 < eta) (R : ℝ) :
    ∃ N : ℕ, ∀ H : ℕ, N ≤ H →
      0 < ‖PAIV H 2 (by norm_num) beta hbeta.le‖ ∧
      ‖PAIV H 2 (by norm_num) beta hbeta.le‖ < eta ∧
      R ≤ ‖PAIV H 2 (by norm_num) beta hbeta.le‖⁻¹ ∧
      ‖NAIV H 2 (by norm_num) beta hbeta.le‖ = 1 := by
  have hSmall : ∀ᶠ H : ℕ in atTop,
      ‖PAIV H 2 (by norm_num) beta hbeta.le‖ < eta :=
    (p4Q2PZ37AIV_originalPhysicalTransfer_norm_tendsto_zero beta hbeta).eventually
      (gt_mem_nhds heta)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hSmall
  obtain ⟨N₂, hN₂⟩ := tendsto_atTop_atTop.mp
    (p4Q2PZ37AIV_originalPhysicalTransfer_inverseNorm_tendsto_atTop beta hbeta) R
  refine ⟨max N₁ N₂, fun H hH => ?_⟩
  exact ⟨periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le,
    hN₁ H ((le_max_left _ _).trans hH),
    hN₂ H ((le_max_right _ _).trans hH),
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
      H 2 (by norm_num) beta hbeta.le⟩

/-- An explicit original fixed-coupling bound has no polynomial source
prefactor because it controls the actual physical operator norm. -/
theorem p4Q2PZ37AIV_originalFixedCoupling_physicalNorm_le_explicitVolumeBound
    (H : ℕ) :
    ‖PAIV H 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
      p4Q2PZ37ADC_fixedCoupling_pos.le‖ ≤
      Real.exp (-(((H : ℝ) + 1) ^ 3 / 16)) := by
  have hRate : ((H : ℝ) + 1) ^ 3 / 16 ≤
      dAIV p4Q2PZ37ADC_fixedCoupling * pAIV H := by
    calc
      ((H : ℝ) + 1) ^ 3 / 16 = (1 / 384 : ℝ) * pAIV H := by
        rw [p4Q2PZ37AIB_plaquetteCount_exact H]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        p4Q2PZ37AIU_originalFixedCoupling_explicitRate_ge_oneDiv384
        (p4Q2PZ37AHN_count_pos H).le
  exact (p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_explicitRate H
    p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le).trans
    (Real.exp_le_exp.mpr (neg_le_neg hRate))

/-- At the same unchanged beta0, the existing inverse norm scale is at
least exp((H+1)^3/16). It cannot be ignored in a normalized-volume analysis. -/
theorem p4Q2PZ37AIV_originalFixedCoupling_inverseNorm_ge_explicitVolumeBound
    (H : ℕ) :
    Real.exp (((H : ℝ) + 1) ^ 3 / 16) ≤
      ‖PAIV H 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
        p4Q2PZ37ADC_fixedCoupling_pos.le‖⁻¹ := by
  have hNorm := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    H 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
  have h := (inv_le_inv₀ (Real.exp_pos (-(((H : ℝ) + 1) ^ 3 / 16))) hNorm).2
    (p4Q2PZ37AIV_originalFixedCoupling_physicalNorm_le_explicitVolumeBound H)
  simpa only [Real.exp_neg, inv_inv] using h

end PZ37AIVVolumeConsequences

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalCrossingAction_le_fullSlabAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalKernel_sq_eq_doubledCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalKernel_sq_le_doubledCrossing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalCrossingKernel_pair_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalCrossingKernel_pair_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalKernelPair_normSqIntegral_le_crossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalKernelPairL2_normSq_eq_integral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalKernelPairL2_normSq_le_crossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalKernelPairL2_norm_le_sqrtCrossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalAmbientTransfer_norm_le_sqrtCrossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_sqrtCrossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_norm_lt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_compactPositiveEigenfunction_le_uniformRowMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_uniformRowMass_le_compactPositiveEigenfunction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalFullKernel_leftContinuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalSpatialHalfweight_ge_expFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalFullKernel_le_crossingKernel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalFullKernel_ge_halfweightFloorCrossing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalFullKernel_leftHaarIntegral_le_crossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalFullKernel_leftHaarIntegral_ge_halfweightFloorCrossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalContinuousVacuum_eigenIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_crossingPartition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalCrossingPartition_mul_halfweightFloor_le_physicalTransferNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_exactRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_norm_ge_exactRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_norm_le_explicitRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalAmbientTransfer_norm_le_exactRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalExponentialVolume_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalAmbientTransfer_norm_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_norm_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalAmbientTransfer_unitBall_small_eventually
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_no_uniformPositiveNormFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_inverseNorm_ge_exactRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_inverseNorm_le_exactRate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalPhysicalTransfer_inverseNorm_tendsto_atTop
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalRawDecay_and_existingNormalization_eventually
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalFixedCoupling_physicalNorm_le_explicitVolumeBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIV_originalFixedCoupling_inverseNorm_ge_explicitVolumeBound
