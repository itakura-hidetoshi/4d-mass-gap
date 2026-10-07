import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentGramSchmidtSeedSourceTiltCovariance
import MGAP4D.MathlibAnalytic.FinitePositiveWeightBidirectionalInfluenceKernelResponse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Strict posterior random-scan contraction of the covariance terminal remainder

PR #5246 leaves the exact finite covariance telescope with one explicit terminal
remainder

  Cov(L_source, R^M O).

The posterior influence carrier used there is deliberately non-strict, so this
remainder cannot be discarded without an additional hypothesis.  This file
adds exactly that missing hypothesis and nothing stronger: a nonnegative
uniform row coefficient strictly below one.

The literal posterior influence matrix is first packaged as the existing
finite nonnegative influence kernel.  Its target update, uniform random-scan
update, and every finite iterate are definitionally the same as the posterior
variation definitions.  Hence the existing finite-kernel theorem gives

  Tot(U^M v) <= q^M Tot(v),

where

  q = |E|^{-1} (|E| - 1 + rho).

We then prove directly on the actual posterior probability measure that
covariance is bounded by the sup norm of the left bounded-continuous observable
times the global oscillation, and that global oscillation is bounded by the
total link variation.  Therefore

  |Cov(L_source, R^M O)|
    <= ||L_source|| q^M Tot(v),

and the terminal covariance tends to zero when rho < 1.

Finally the finite-resolvent theorem from PR #5246 is combined with this
geometric terminal bound and specialized to the four-link Gram--Schmidt seed
profile from PR #5245.

No strict row bound is inferred from non-strict data.  No posterior covariance
is identified with an L2 coordinate norm, no positive-depth hard support is
asserted, and no heat-bath-time / Euclidean-time identification is made.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped BigOperators ENNReal InnerProductSpace InnerProduct

noncomputable section

local instance p3PosteriorTerminalTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3PosteriorTerminalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3PosteriorTerminalSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3PosteriorTerminalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3PosteriorTerminalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3PosteriorTerminalSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The literal posterior non-strict influence matrix viewed as the generic
finite nonnegative influence kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B) :
    FiniteNonnegativeInfluenceKernelData
      (PeriodicHypercubicEvenSpatialSliceLink H) where
  influence := D.influence
  influence_nonneg := D.influence_nonneg
  influence_diagonal_zero := D.influence_diagonal_zero

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel_influence
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel D).influence
        target source =
      D.influence target source :=
  rfl

/-- One literal posterior target update is exactly the generic influence-kernel
target update. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation_eq_kernel
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
        D variation target source =
      finiteInfluenceKernelUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel D)
        variation target source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
    finiteInfluenceKernelUpdatedVariation
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel
  rfl

/-- Uniform posterior random-scan updating is exactly generic kernel
random-scan updating. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_eq_kernel
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        D variation source =
      finiteInfluenceKernelRandomScanUpdatedVariation
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel D)
        variation source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
    finiteInfluenceKernelRandomScanUpdatedVariation
  apply congrArg ((Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro target _htarget
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation_eq_kernel
      D variation target source

/-- Every finite posterior random-scan variation iterate is exactly the
corresponding generic influence-kernel iterate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_eq_kernel
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (M : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
        D variation M =
      finiteInfluenceKernelRandomScanVariationIterate
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel D)
        variation M := by
  induction M with
  | zero =>
      rfl
  | succ M ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_succ,
        finiteInfluenceKernelRandomScanVariationIterate_succ,
        ih]
      funext source
      exact
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_eq_kernel
          D
          (finiteInfluenceKernelRandomScanVariationIterate
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel D)
            variation M)
          source

/-- An explicit uniform posterior row coefficient gives the standard finite
power contraction of total random-scan variation.  Strictness is not needed
for this finite inequality. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_total_le_rate_pow_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target source) ≤ rowCoefficient)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (M : ℕ) :
    finiteProductVariationTotal
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D variation M) ≤
      finiteInfluenceKernelReciprocalRandomScanRate
          (PeriodicHypercubicEvenSpatialSliceLink H) rowCoefficient ^ M *
        finiteProductVariationTotal variation := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel D
  have hRowsK :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        finiteInfluenceKernelRowSum K target ≤ rowCoefficient := by
    intro target
    simpa [K, finiteInfluenceKernelRowSum,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorInfluenceKernel] using
      hRowSum target
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_eq_kernel
      D variation M]
  exact
    finiteInfluenceKernelRandomScanVariationIterate_total_le_rate_pow_mul
      K hEdge rowCoefficient hRowNonneg hRowsK
      variation hVariationNonneg M

/-- Replace finitely many posterior spatial-slice coordinates of A by those of
C. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
    {H N : ℕ}
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (s : Finset (PeriodicHypercubicEvenSpatialSliceLink H)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N := by
  classical
  exact fun e => if e ∈ s then C e else A e

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks_empty
    {H N : ℕ}
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
        A C ∅ = A := by
  funext e
  simp [periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks]

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks_univ
    {H N : ℕ}
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
        A C Finset.univ = C := by
  classical
  funext e
  simp [periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks]

/-- A posterior link-variation bound controls global oscillation by its total
link variation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariation_globalOscillation_le_total
    {H N : ℕ}
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ)
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
        H N F)
    (A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |F A - F C| ≤ finiteProductVariationTotal P.variation := by
  classical
  have hSplice :
      ∀ s : Finset (PeriodicHypercubicEvenSpatialSliceLink H),
        |F
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
              A C s) -
          F A| ≤
          ∑ e ∈ s, P.variation e := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert source s hsource ih =>
        have hAgree :
            PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
              (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
                A C (insert source s))
              (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
                A C s)
              source := by
          intro e he
          simp [
            periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks,
            he]
        calc
          |F
                (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
                  A C (insert source s)) -
              F A| ≤
            |F
                (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
                  A C (insert source s)) -
              F
                (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
                  A C s)| +
            |F
                (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorReplaceLinks
                  A C s) -
              F A| :=
            abs_sub_le _ _ _
          _ ≤ P.variation source + ∑ e ∈ s, P.variation e := by
            exact add_le_add
              (P.variation_bound source _ _ hAgree)
              ih
          _ = ∑ e ∈ insert source s, P.variation e := by
            simp [Finset.sum_insert, hsource]
  have hAll :=
    hSplice
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
  simpa [finiteProductVariationTotal, abs_sub_comm] using hAll

/-- A global oscillation bound centers a bounded-continuous observable around
its actual posterior mean with the same radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_abs_sub_mean_le_of_globalOscillation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (R : ℝ)
    (hOsc :
      ∀ A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |O A - O C| ≤ R)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |O A -
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B O| ≤ R := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  have hOInt : Integrable (fun C => O C) mu :=
    O.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hConstInt : Integrable
      (fun _C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        O A) mu :=
    integrable_const (O A)
  have hDiffInt :
      Integrable (fun C => O A - O C) mu :=
    hConstInt.sub' hOInt
  have hAbsDiffInt :
      Integrable (fun C => |O A - O C|) mu := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hRInt :
      Integrable
        (fun _C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          R) mu :=
    integrable_const R
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  change |O A - ∫ C, O C ∂mu| ≤ R
  calc
    |O A - ∫ C, O C ∂mu| =
        |(∫ _C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
              O A ∂mu) -
          ∫ C, O C ∂mu| := by simp
    _ = |∫ C, O A - O C ∂mu| := by
      rw [integral_sub hConstInt hOInt]
    _ ≤ ∫ C, |O A - O C| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤
        ∫ _C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          R ∂mu := by
      apply integral_mono hAbsDiffInt hRInt
      intro C
      exact hOsc A C
    _ = R := by simp

/-- On the actual posterior probability measure, global oscillation of the
right observable controls covariance by the sup norm of the left observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_abs_le_norm_mul_globalOscillation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (R : ℝ)
    (hOsc :
      ∀ A C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |O A - O C| ≤ R) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F O| ≤
      ‖F‖ * R := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  let mO : ℝ :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
      H N hN beta hbeta B O
  have hFOInt :
      Integrable (fun A => F A * O A) mu :=
    (F.continuous.mul O.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFmInt :
      Integrable (fun A => F A * mO) mu :=
    (F.continuous.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCenteredProductInt :
      Integrable (fun A => F A * (O A - mO)) mu :=
    (F.continuous.mul (O.continuous.sub continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbsCenteredProductInt :
      Integrable (fun A => |F A * (O A - mO)|) mu := by
    simpa [Real.norm_eq_abs] using hCenteredProductInt.norm
  have hConstInt :
      Integrable
        (fun _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          ‖F‖ * R) mu :=
    integrable_const (‖F‖ * R)
  have hCentered :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |O A - mO| ≤ R := by
    intro A
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_abs_sub_mean_le_of_globalOscillation
        H N hN beta hbeta B O R hOsc A
  have hPointwise :
      ∀ A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        |F A * (O A - mO)| ≤ ‖F‖ * R := by
    intro A
    rw [abs_mul]
    exact
      mul_le_mul
        (by simpa [Real.norm_eq_abs] using F.norm_coe_le_norm A)
        (hCentered A)
        (abs_nonneg _)
        (norm_nonneg _)
  have hCenteredIntegral :
      (∫ A, F A * (O A - mO) ∂mu) =
        (∫ A, F A * O A ∂mu) - (∫ A, F A ∂mu) * mO := by
    simp_rw [mul_sub]
    rw [integral_sub hFOInt hFmInt, integral_mul_const]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  change
    |(∫ A, F A * O A ∂mu) - (∫ A, F A ∂mu) * mO| ≤ ‖F‖ * R
  rw [← hCenteredIntegral]
  calc
    |∫ A, F A * (O A - mO) ∂mu| ≤
        ∫ A, |F A * (O A - mO)| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤
        ∫ _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          ‖F‖ * R ∂mu := by
      apply integral_mono hAbsCenteredProductInt hConstInt
      intro A
      exact hPointwise A
    _ = ‖F‖ * R := by simp

/-- Posterior covariance is controlled by total centered link variation of the
right observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_abs_le_norm_mul_totalVariation
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ)
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B F O| ≤
      ‖F‖ * finiteProductVariationTotal P.variation := by
  apply
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_abs_le_norm_mul_globalOscillation
      H N hN beta hbeta B F O
      (finiteProductVariationTotal P.variation)
  intro A C
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariation_globalOscillation_le_total
      (fun X => O X) P.toPeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
      A C

/-- Under a uniform nonnegative posterior row bound, the terminal covariance in
the finite telescope is controlled by the matching random-scan power. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScan_terminal_covariance_abs_le_rate_pow_mul_totalVariation
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    {O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ}
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient)
    (M : ℕ) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        (((P.toRandomScanCenteredState).randomScanIterate D M).observable)| ≤
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue‖ *
        (finiteInfluenceKernelReciprocalRandomScanRate
            (PeriodicHypercubicEvenSpatialSliceLink H) rowCoefficient ^ M *
          finiteProductVariationTotal P.variation) := by
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  let S :=
    (P.toRandomScanCenteredState).randomScanIterate D M
  have hCov :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance_abs_le_norm_mul_totalVariation
      H N hN beta hbeta B L S.observable S.profile
  have hProfile :
      S.profile.variation =
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D P.variation M := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanCenteredState_iterate_variation_eq
        P D M
  rw [hProfile] at hCov
  have hTotal :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_total_le_rate_pow_mul
      D hEdge rowCoefficient hRowNonneg hRowSum
      P.variation P.variation_nonneg M
  exact
    hCov.trans
      (mul_le_mul_of_nonneg_left hTotal (norm_nonneg L))

/-- Combining PR #5246 with terminal contraction gives a fully explicit finite
resolvent plus geometric-tail bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_abs_le_finiteResolvent_add_geometricTail
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    {O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ}
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient)
    (M : ℕ) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue)
        O| ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
          D P.variation M source +
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue‖ *
        (finiteInfluenceKernelReciprocalRandomScanRate
            (PeriodicHypercubicEvenSpatialSliceLink H) rowCoefficient ^ M *
          finiteProductVariationTotal P.variation) := by
  have hFinite :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_abs_le_finiteResolvent_add_terminal
      source sourceValue P D hEdge M
  have hTail :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScan_terminal_covariance_abs_le_rate_pow_mul_totalVariation
      source sourceValue P D hEdge rowCoefficient hRowNonneg hRowSum M
  exact hFinite.trans (add_le_add_left hTail _)

/-- Under an explicit strict posterior row coefficient, the terminal covariance
remainder tends to zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScan_terminal_covariance_tendsto_zero
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    {O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ}
    (P :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCenteredVariationProfile
        H N O)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient) :
    Tendsto
      (fun M : ℕ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H N beta B source sourceValue)
          (((P.toRandomScanCenteredState).randomScanIterate D M).observable))
      atTop (nhds 0) := by
  let q :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (PeriodicHypercubicEvenSpatialSliceLink H) rowCoefficient
  let total := finiteProductVariationTotal P.variation
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  have hqNonneg : 0 ≤ q := by
    dsimp [q]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_nonneg
        hEdge rowCoefficient hRowNonneg
  have hqLtOne : q < 1 := by
    dsimp [q]
    exact
      finiteInfluenceKernelReciprocalRandomScanRate_lt_one
        hEdge rowCoefficient hRowLtOne
  have hPow : Tendsto (fun M : ℕ => q ^ M) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hqNonneg hqLtOne
  have hEnvelope :
      Tendsto
        (fun M : ℕ => ‖L‖ * (q ^ M * total))
        atTop (nhds 0) := by
    have hRight :
        Tendsto (fun M : ℕ => q ^ M * total) atTop (nhds 0) := by
      simpa using hPow.mul_const total
    simpa using tendsto_const_nhds.mul hRight
  have hBound (M : ℕ) :
      |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B L
          (((P.toRandomScanCenteredState).randomScanIterate D M).observable)| ≤
        ‖L‖ * (q ^ M * total) := by
    simpa [q, total, L] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScan_terminal_covariance_abs_le_rate_pow_mul_totalVariation
        source sourceValue P D hEdge rowCoefficient hRowNonneg hRowSum M
  have hAbs :
      Tendsto
        (fun M : ℕ =>
          |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H N hN beta hbeta B L
            (((P.toRandomScanCenteredState).randomScanIterate D M).observable)|)
        atTop (nhds 0) := by
    exact squeeze_zero'
      (Filter.Eventually.of_forall fun M => abs_nonneg _)
      (Filter.Eventually.of_forall hBound)
      hEnvelope
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  simpa [Real.norm_eq_abs, L] using hAbs

/-- Gram--Schmidt seed specialization of the finite-resolvent plus geometric
terminal bound. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_localFactor_covariance_abs_le_finiteResolvent_add_geometricTail
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient)
    (M : ℕ) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)
        (periodicHypercubicEvenPrimarySpatialSliceWilsonEnergyGramSchmidtBoundedObservable
          H mode)| ≤
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta / 2) *
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
          D
          (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
            H mode).variation
          M source +
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue‖ *
        (finiteInfluenceKernelReciprocalRandomScanRate
            (PeriodicHypercubicEvenSpatialSliceLink H) rowCoefficient ^ M *
          finiteProductVariationTotal
            (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
              H mode).variation) := by
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_covariance_abs_le_finiteResolvent_add_geometricTail
      source sourceValue
      (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
        H mode)
      D hEdge rowCoefficient hRowNonneg hRowSum M

/-- Under the same explicit strict row bound, the Gram--Schmidt seed terminal
covariance tends to zero. -/
theorem
    physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosterior_terminal_covariance_tendsto_zero
    (H mode : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowLtOne : rowCoefficient < 1)
    (hRowSum :
      ∀ target : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ remote : PeriodicHypercubicEvenSpatialSliceLink H,
          D.influence target remote) ≤ rowCoefficient) :
    Tendsto
      (fun M : ℕ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H 2 beta B source sourceValue)
          ((((physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
              H mode).toRandomScanCenteredState).randomScanIterate D M).observable))
      atTop (nhds 0) := by
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosterior_localFactor_randomScan_terminal_covariance_tendsto_zero
      source sourceValue
      (physicalYangMillsSU2PrimaryPlaquetteGramSchmidtPosteriorCenteredVariationProfile
        H mode)
      D hEdge rowCoefficient hRowNonneg hRowLtOne hRowSum

end

end MathlibAnalytic
end MGAP4D
