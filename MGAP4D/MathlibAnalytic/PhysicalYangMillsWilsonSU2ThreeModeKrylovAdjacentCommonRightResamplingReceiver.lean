import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentSingleDefectFactorization
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-!
# Common-right posterior resampling receiver for the actual adjacent orbit

PR #5240 factors every actual one-link defect as

  D_(n,r,k)(e,z,u) = L_(n,r,k)(z.left) * R_(n,r)(e,z,u),

with a right defect independent of the mode k.

This file turns that exact factorization into a quantitative receiver.

* a bounded one-slab Wilson kernel maps every L2 input to a pointwise scalar
  bounded by the input L2 norm;
* the one-slice SU(2) Gram--Schmidt physical modes have norm one;
* the normalized physical one-slice transfer has norm one, so every actual
  left orbit factor has norm at most one;
* therefore |L_(n,r,k)| <= 1 pointwise;
* the common right defect is packaged as the ordinary posterior resampling
  difference of one bounded-continuous joint observable;
* hence each original Q_e is bounded, with coefficient one, by the same
  mode-independent posterior resampling energy.

The exact 1/12 normalization is retained.  No seed-covariance/source-coordinate
norm identification and no hard-support assumption are used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3CommonRightReceiverTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3CommonRightReceiverCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3CommonRightReceiverSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3CommonRightReceiverMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3CommonRightReceiverBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3CommonRightReceiverSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3CommonRightReceiverSpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- On a probability space, the L1 norm of an L2 representative is no larger
than its L2 norm.  This is the exact exponent-monotonicity theorem from
mathlib, specialized to p=1 and q=2. -/
theorem realL2_integral_norm_le_norm_probability
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ ‖f‖ := by
  have hmono :
      eLpNorm (fun x => f x) 1 μ ≤ eLpNorm (fun x => f x) 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (f := fun x => f x) (μ := μ)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.aestronglyMeasurable f)
  have hreal :
      (eLpNorm (fun x => f x) 1 μ).toReal ≤
        (eLpNorm (fun x => f x) 2 μ).toReal :=
    ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hmono
  calc
    (∫ x, ‖f x‖ ∂μ) =
        lpNorm (fun x => f x) 1 μ :=
      (lpNorm_one_eq_integral_norm (Lp.aestronglyMeasurable f)).symm
    _ = (eLpNorm (fun x => f x) 1 μ).toReal :=
      (toReal_eLpNorm (p := (1 : ℝ≥0∞)) (Lp.aestronglyMeasurable f)).symm
    _ ≤ (eLpNorm (fun x => f x) 2 μ).toReal := hreal
    _ = ‖f‖ := by
      simpa only using (Lp.norm_def f).symm

namespace GroundStatePosteriorJoint

section GeneralCarrier

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "mu" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
local notation "SliceL2" => Lp ℝ 2 mu
local notation "PhysicalSlice" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta
local notation "SqrtD" =>
  continuousJointSqrtDensity H N hN beta hbeta
local notation "lam" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖

include hN hbeta in
/-- A one-slice Wilson-kernel fiber integral is pointwise bounded by the L2
norm of its input, with no volume factor. -/
theorem decomposableOneSliceTransferIntegral_abs_le_norm
    (f : SliceL2) (B : Cfg) :
    |decomposableOneSliceTransferIntegral H N beta f B| ≤ ‖f‖ := by
  have hfInt : Integrable (fun A => f A) mu :=
    memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent (by norm_num))
  have hInt :
      ‖∫ A, K A B * f A ∂mu‖ ≤ ∫ A, ‖f A‖ ∂mu := by
    apply norm_integral_le_of_norm_le hfInt.norm
    filter_upwards with A
    rw [norm_mul, Real.norm_eq_abs]
    calc
      |K A B| * ‖f A‖ ≤ 1 * ‖f A‖ :=
        mul_le_mul_of_nonneg_right
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
            H N hN beta hbeta A B)
          (norm_nonneg (f A))
      _ = ‖f A‖ := one_mul _
  have hL1 :
      (∫ A, ‖f A‖ ∂mu) ≤ ‖f‖ :=
    realL2_integral_norm_le_norm_probability f
  simpa [decomposableOneSliceTransferIntegral, Real.norm_eq_abs] using
    hInt.trans hL1

include hN hbeta in
/-- Continuity of the one-slice fiber integral for an arbitrary L2 input.
Compactness is not used for the domination step. -/
theorem decomposableOneSliceTransferIntegral_continuous
    (f : SliceL2) :
    Continuous (decomposableOneSliceTransferIntegral H N beta f) := by
  have hf : Integrable (fun A => f A) mu :=
    memLp_one_iff_integrable.1 ((Lp.memLp f).mono_exponent (by norm_num))
  have hK :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta
  apply continuous_of_dominated (bound := fun A => ‖f A‖)
  · intro B
    exact
      ((hK.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f))
  · intro B
    exact Eventually.of_forall fun A => by
      rw [norm_mul, Real.norm_eq_abs]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
            H N hN beta hbeta A B)
          (norm_nonneg (f A))
  · exact hf.norm
  · exact Eventually.of_forall fun A =>
      (hK.comp
        ((continuous_const : Continuous (fun _B : Cfg => A)).prodMk
          (continuous_id : Continuous (fun B : Cfg => B)))).mul
        (continuous_const : Continuous (fun _B : Cfg => f A))

/-- The common right output factor from #5240 is a bounded-continuous joint
observable. -/
def decomposableRightOutputBCF
    (g : PhysicalSlice) : BoundedContinuousFunction Joint ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨decomposableRightOutputFactor H N hN beta hbeta g, by
      unfold decomposableRightOutputFactor
      have hInt :
          Continuous (fun z : Joint =>
            decomposableOneSliceTransferIntegral H N beta
              (g : SliceL2) z.2) :=
        (decomposableOneSliceTransferIntegral_continuous
          H N hN beta hbeta (g : SliceL2)).comp
          (continuous_snd : Continuous (fun z : Joint => z.2))
      exact
        (continuous_const.mul hInt).div
          (continuousJointSqrtDensity_continuous H N hN beta hbeta)
          (fun z =>
            (continuousJointSqrtDensity_pos H N hN beta hbeta z).ne')⟩

@[simp] theorem decomposableRightOutputBCF_apply
    (g : PhysicalSlice) (z : Joint) :
    decomposableRightOutputBCF H N hN beta hbeta g z =
      decomposableRightOutputFactor H N hN beta hbeta g z :=
  rfl

/-- The complete right defect from #5240 is exactly the ordinary one-link
difference of the new bounded-continuous right observable. -/
theorem decomposableRightLinkDifferenceFactor_eq_outputBCF_sub_update
    (g : PhysicalSlice) (e : Link) (z : Joint) (u : GaugeT) :
    decomposableRightLinkDifferenceFactor H N hN beta hbeta g e z u =
      decomposableRightOutputBCF H N hN beta hbeta g z -
        decomposableRightOutputBCF H N hN beta hbeta g
          (z.1, Function.update z.2 e u) := by
  change
    decomposableRightLinkDifferenceFactor H N hN beta hbeta g e z u =
      decomposableRightOutputFactor H N hN beta hbeta g z -
        decomposableRightOutputFactor H N hN beta hbeta g
          (z.1, Function.update z.2 e u)
  unfold
    decomposableRightLinkDifferenceFactor
    decomposableRightSourceResponseFactor
  have hOut :=
    (outputRightLinkTilt_pos H N hN beta hbeta z e u).ne'
  field_simp [hOut]
  ring

end GeneralCarrier

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "GaugeT" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "SliceL2" =>
  Lp ℝ 2
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2)
local notation "PhysicalSlice" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "Orbit" =>
  physicalYangMillsSU2AdjacentFinePairOrbitVector
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)

/-- Each one-slice physical SU(2) Gram--Schmidt mode has norm one. -/
theorem primarySpatialSliceGramSchmidtPhysicalL2_norm
    (k : Fin 3) :
    ‖periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
        Hn k.1‖ = 1 := by
  have hPair :
      ‖periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2
          Hn k.1‖ = 1 :=
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_orthonormal
      Hn).norm_eq_one k.1
  rw [
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_eq_physicalDecomposable
      Hn k.1
  ] at hPair
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairDecomposableL2 at hPair
  let mu :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2
  change
    ‖realL2ExternalTensor
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          Hn k.1 : Lp ℝ 2 mu)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          Hn 2 : Lp ℝ 2 mu)‖ = 1 at hPair
  have hPairNorm :
      ‖(periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
          Hn k.1 : Lp ℝ 2 mu)‖ *
        ‖(periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          Hn 2 : Lp ℝ 2 mu)‖ = 1 := by
    calc
      _ = ‖realL2ExternalTensor
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
            Hn k.1 : Lp ℝ 2 mu)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            Hn 2 : Lp ℝ 2 mu)‖ :=
        (realL2ExternalTensor_norm
          (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
            Hn k.1 : Lp ℝ 2 mu)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            Hn 2 : Lp ℝ 2 mu)).symm
      _ = 1 := hPair
  have hOneAmbient :
      ‖(periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          Hn 2 : Lp ℝ 2 mu)‖ = 1 := by
    simpa only [Submodule.norm_coe] using
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm Hn 2
  rw [hOneAmbient, mul_one] at hPairNorm
  simpa only [Submodule.norm_coe] using hPairNorm

/-- The mode-dependent first-slice orbit factor stays in the unit L2 ball. -/
theorem fineOrbitLeftFactor_norm_le_one
    (k : Fin 3) :
    ‖physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k‖ ≤ 1 := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      Hn 2 Pos (beta (n + 1)) (hbeta (n + 1))
  let f :=
    periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtPhysicalL2
      Hn k.1
  have hS : ‖S‖ = 1 := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        Hn 2 Pos (beta (n + 1)) (hbeta (n + 1))
  have hf : ‖f‖ = 1 := by
    simpa [f] using
      primarySpatialSliceGramSchmidtPhysicalL2_norm
        (halfExtent := halfExtent) n k
  change ‖(S ^ r) f‖ ≤ 1
  induction r with
  | zero =>
      simpa [hf]
  | succ m ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      calc
        ‖S ((S ^ m) f)‖ ≤ ‖S‖ * ‖(S ^ m) f‖ :=
          ContinuousLinearMap.le_opNorm S ((S ^ m) f)
        _ = ‖(S ^ m) f‖ := by rw [hS, one_mul]
        _ ≤ 1 := ih

/-- Hence the literal first-slice scalar appearing in #5240 is pointwise at
most one in absolute value. -/
theorem fineOrbitLeftAmplitude_abs_le_one
    (k : Fin 3) (A : Cfg) :
    |decomposableOneSliceTransferIntegral Hn 2 (beta n)
        (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k : SliceL2) A| ≤ 1 := by
  exact
    (decomposableOneSliceTransferIntegral_abs_le_norm
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k : SliceL2) A).trans
      (by
        simpa only [Submodule.norm_coe] using
          fineOrbitLeftFactor_norm_le_one
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k)

/-- The bounded-continuous common-right observable carried by all three modes
at fixed n and r. -/
def fineOrbitCommonRightBCF :
    BoundedContinuousFunction Joint ℝ :=
  decomposableRightOutputBCF
    Hn 2 Pos (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r)

/-- The common right defect is literally the one-link difference of the
mode-independent common-right BCF. -/
theorem fineOrbitRightLinkDifferenceFactor_eq_commonRightBCF_sub_update
    (e : Link) (z : Joint) (u : GaugeT) :
    fineOrbitRightLinkDifferenceFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e z u =
      fineOrbitCommonRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r z -
        fineOrbitCommonRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r (z.1, Function.update z.2 e u) := by
  unfold fineOrbitRightLinkDifferenceFactor fineOrbitCommonRightBCF
  exact
    decomposableRightLinkDifferenceFactor_eq_outputBCF_sub_update
      Hn 2 Pos (beta n) (hbeta n)
      (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r)
      e z u

/-- Pointwise, the original signed defect square is bounded by the common-right
BCF one-link difference square with coefficient one. -/
theorem fineOrbit_jointTransferLinkDifference_sq_le_commonRightBCF
    (k : Fin 3) (e : Link) (z : Joint) (u : GaugeT) :
    (jointTransferLinkDifference Hn 2 Pos (beta n) (hbeta n)
        (Orbit n r k) e z u) ^ 2 ≤
      (fineOrbitCommonRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r z -
        fineOrbitCommonRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r (z.1, Function.update z.2 e u)) ^ 2 := by
  rw [
    fineOrbit_jointTransferLinkDifference_sq_eq_left_sq_mul_commonRight_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k e z u,
    fineOrbitRightLinkDifferenceFactor_eq_commonRightBCF_sub_update
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e z u
  ]
  have hAbs :=
    fineOrbitLeftAmplitude_abs_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k z.1
  have hSq :
      (decomposableOneSliceTransferIntegral Hn 2 (beta n)
          (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r k : SliceL2) z.1) ^ 2 ≤ 1 := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) hAbs 2
    simpa only [sq_abs, one_pow] using hp
  exact
    (mul_le_mul_of_nonneg_right hSq
      (sq_nonneg
        (fineOrbitCommonRightBCF
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r z -
          fineOrbitCommonRightBCF
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r (z.1, Function.update z.2 e u)))).trans_eq
      (one_mul _)

/-- Fiberwise original resampling square is controlled by the common-right
posterior resampling square. -/
theorem fineOrbit_linkResamplingSquare_le_commonRight
    (k : Fin 3) (e : Link) (z : Joint) :
    (∫ u,
      (jointTransferLinkDifference Hn 2 Pos (beta n) (hbeta n)
        (Orbit n r k) e z u) ^ 2
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalMeasure
        Hn 2 Pos (beta n) (hbeta n) z.1 z.2 e) ≤
      posteriorResamplingSquare Hn 2 Pos (beta n) (hbeta n) e
        (fineOrbitCommonRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) z := by
  unfold posteriorResamplingSquare
  apply integral_mono
  · exact
      jointTransferLinkDifference_sq_posterior_integrable
        Hn 2 Pos (beta n) (hbeta n) (Orbit n r k) e z
  · exact
      posteriorResamplingDifferenceSquare_integrable
        Hn 2 Pos (beta n) (hbeta n) e
        (fineOrbitCommonRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) z
  · intro u
    exact
      fineOrbit_jointTransferLinkDifference_sq_le_commonRightBCF
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k e z u

/-- The ORIGINAL one-link Q_e is bounded by one mode-independent posterior
resampling energy. -/
theorem fineOrbit_jointTransferLinkResamplingEnergy_le_commonRight
    (k : Fin 3) (e : Link) :
    jointTransferLinkResamplingEnergy Hn 2 Pos (beta n) (hbeta n)
        (Orbit n r k) e ≤
      posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n) e
        (fineOrbitCommonRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) := by
  unfold jointTransferLinkResamplingEnergy posteriorResamplingEnergy
  apply integral_mono
  · exact
      jointTransferLinkResamplingSquare_integrable
        Hn 2 Pos (beta n) (hbeta n) (Orbit n r k) e
  · exact
      posteriorResamplingSquare_integrable
        Hn 2 Pos (beta n) (hbeta n) e
        (fineOrbitCommonRightBCF
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r)
  · intro z
    exact
      fineOrbit_linkResamplingSquare_le_commonRight
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k e z

/-- Exact 1/12 normalization retained after replacing every actual modewise
Q_e by the common-right posterior resampling receiver. -/
theorem fineFrozenInitialEnergy_le_commonRightResampling
    (k : Fin 3) :
    sixColorInitialResidualEnergy Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFineFrozenStepGroundStateJointVector
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k) ≤
      (1 / 12 : ℝ) * ∑ e : Link,
        posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n) e
          (fineOrbitCommonRightBCF
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r) := by
  rw [
    fineFrozenInitialEnergy_eq_resampling
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  ]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro e _he
    exact
      fineOrbit_jointTransferLinkResamplingEnergy_le_commonRight
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k e
  · norm_num

end ActualAdjacentOrbit

end GroundStatePosteriorJoint

end

end MathlibAnalytic
end MGAP4D
