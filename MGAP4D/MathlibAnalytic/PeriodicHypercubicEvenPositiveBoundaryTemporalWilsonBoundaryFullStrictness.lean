import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedStrictness
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureNonnegSMulMomentStrictness
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureWeightedGramStrictness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

noncomputable section

private theorem positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive :
    0 < (2 : ℕ) := by
  norm_num

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance positiveBoundaryTemporalWilsonBoundaryFullStrictnessTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance positiveBoundaryTemporalWilsonBoundaryFullStrictnessCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance positiveBoundaryTemporalWilsonBoundaryFullStrictnessSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance positiveBoundaryTemporalWilsonBoundaryFullStrictnessMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance positiveBoundaryTemporalWilsonBoundaryFullStrictnessBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance positiveBoundaryTemporalWilsonBoundaryFullStrictnessSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

private theorem periodicHypercubicEvenBoundaryFiberedIdentityStepValue_continuous
    {H : ℕ}
    (s : PeriodicHypercubicBoundaryStep (PeriodicHypercubicEvenSideLength H)) :
    Continuous fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
      periodicHypercubicStepValue
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble
          b (fun _ => 1) (fun _ => 1)) s := by
  let P := periodicHypercubicEvenEdgeOrbitPartition H
  cases hside : P.side s.edge with
  | positive =>
      cases horientation : s.orientation with
      | forward =>
          simpa [P, periodicHypercubicStepValue,
            FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
            hside, horientation] using
            (continuous_const : Continuous
              (fun _ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
                (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))
      | backward =>
          simpa [P, periodicHypercubicStepValue,
            FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
            hside, horientation] using
            (continuous_const : Continuous
              (fun _ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
                (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))
  | negative =>
      cases horientation : s.orientation with
      | forward =>
          simpa [P, periodicHypercubicStepValue,
            FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
            hside, horientation] using
            (continuous_const : Continuous
              (fun _ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
                (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))
      | backward =>
          simpa [P, periodicHypercubicStepValue,
            FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
            hside, horientation] using
            (continuous_const : Continuous
              (fun _ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
                (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)))
  | fixed =>
      let e : P.FixedEdge := ⟨s.edge, hside⟩
      have hcoord : Continuous fun b : P.BoundaryConfiguration
          (Matrix.specialUnitaryGroup (Fin 2) ℂ) => b e :=
        continuous_apply e
      cases horientation : s.orientation with
      | forward =>
          simpa [P, e, periodicHypercubicStepValue,
            FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
            hside, horientation] using hcoord
      | backward =>
          simpa [P, e, periodicHypercubicStepValue,
            FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
            hside, horientation] using continuous_inv.comp hcoord

/-- Every canonical shared-boundary leg occurring in the literal positive-
boundary temporal Wilson product is a continuous function of the physical
shared-boundary configuration. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg_continuous
    (H : ℕ)
    (p : PeriodicHypercubicEvenPlaquette H) :
    Continuous fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
      periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg b p := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg
  unfold periodicHypercubicEvenPositiveBoundaryTemporalBoundaryLeg
  by_cases hbase : (p.1 0).val = 0
  · simp only [if_pos hbase]
    exact continuous_inv.comp
      (periodicHypercubicEvenBoundaryFiberedIdentityStepValue_continuous
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 3))
  · simp only [if_neg hbase]
    exact continuous_inv.comp
      (periodicHypercubicEvenBoundaryFiberedIdentityStepValue_continuous
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p 1))

/-- The complete literal positive-boundary temporal Wilson kernel is continuous
on the product of two actual shared-boundary configuration spaces. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel_continuous
    (H : ℕ)
    (beta : ℝ) :
    Continuous fun q :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel
        H beta q.1 q.2 := by
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel
  apply continuous_finset_prod
  intro p _hp
  exact (continuous_specialUnitaryWilsonRelativeKernel 2 beta).comp₂
    ((periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg_continuous H p).comp
      continuous_fst)
    ((periodicHypercubicEvenPositiveBoundaryTemporalFiberedBoundaryLeg_continuous H p).comp
      continuous_snd)

/-- The full literal positive-boundary Wilson kernel has diagonal value one. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel_self
    (H : ℕ)
    (beta : ℝ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel H beta b b = 1 := by
  classical
  unfold periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel
  apply Finset.prod_eq_one
  intro p _hp
  exact specialUnitaryWilsonRelativeKernel_self
    2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta _

/-- Hilbert feature of the exact Schur-PSD complement after the protected
four-edge positive-degree component has been removed from the full literal
positive-boundary Wilson kernel. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedRemainderFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
      (fun b c =>
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel H beta b c -
          (Real.exp (-beta)) ^
              (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
            specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
              (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c)) :=
  (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel_sub_protectedFourEdgeSelectedDegree_positiveSemidefiniteCertificate
    H beta hbeta n).toHilbertFeature

/-- The protected selected degree as an explicit Hilbert summand, including the
actual degree-zero scalar contributed by every literal residual plaquette. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedSelectedDegreeFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
      (fun b c =>
        (Real.exp (-beta)) ^
            (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card *
          specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel beta n
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H b)
            (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWord H c)) := by
  let r := (Real.exp (-beta)) ^
    (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card
  let S := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
    H beta hbeta n
  have hr : 0 ≤ r :=
    (periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualDegreeZeroScalar_pos H beta).le
  simpa [r, S, specialUnitaryTwoCyclicFourEdgeWilsonSelectedDegreeKernel] using
    RealHilbertKernelFeature.nonnegSMul r hr S

/-- Moore--Aronszajn direct-sum realization of the **entire** literal positive-
boundary temporal Wilson kernel, with the protected positive-degree four-edge
sector retained as the right Hilbert summand.

We deliberately leave the kernel in its raw `(full - protected) + protected`
form.  The equality with the literal full kernel is proved separately below;
this keeps the feature space definitionally equal to the direct sum and avoids
dependent casts when applying generic noncancellation lemmas. -/
noncomputable def periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :=
  RealHilbertKernelFeature.add
    (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedRemainderFeature
      H beta hbeta n)
    (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedSelectedDegreeFeature
      H beta hbeta n)

/-- The raw direct-sum feature kernel is exactly the literal complete positive-
boundary Wilson kernel. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_kernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
      H beta hbeta n).kernel_eq_inner b c =
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel H beta b c := by
  rw [(periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
    H beta hbeta n).kernel_eq_inner]
  simp [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature]

/-- The full decomposition feature is continuous because its raw direct-sum
kernel simplifies exactly to the actual finite product of continuous Wilson
relative kernels. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_continuous
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    Continuous
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
        H beta hbeta n).feature := by
  apply RealHilbertKernelFeature.continuous_feature_of_continuous_kernel
    (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
      H beta hbeta n)
  simpa [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature] using
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel_continuous H beta

/-- Every full-decomposition feature vector has unit norm. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_norm
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    ‖(periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
        H beta hbeta n).feature b‖ = 1 := by
  apply RealHilbertKernelFeature.feature_norm_eq_one
  intro d
  simpa [periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature] using
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel_self H beta d

/-- Polynomial-weighted full positive-boundary Wilson feature vectors are
Bochner integrable in the actual interacting boundary marginal. -/
theorem periodicHypercubicEvenBoundaryMarginalWeightedPositiveBoundaryWilsonFullDecompositionFeature_integrable
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (n : ℕ) :
    Integrable
      (fun b =>
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
          (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
            H beta hbeta n).feature b)
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta) := by
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let C := periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
    H beta hbeta n
  have hContinuous : Continuous (fun b => p b • C.feature b) :=
    p.continuous.smul
      (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_continuous
        H beta hbeta n)
  refine Integrable.of_bound hContinuous.aestronglyMeasurable ‖p‖ ?_
  filter_upwards [] with b
  rw [norm_smul,
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_norm]
  simpa [p] using p.norm_coe_le_norm b

/-- A cyclic dual probe detecting degree `n` remains nonzero in the explicitly
protected selected summand after every residual plaquette contributes its
actual degree-zero Wilson factor. -/
theorem periodicHypercubicEvenBoundaryMarginal_protectedPositiveBoundaryWilsonSelectedDegreeFeature_integral_ne_zero_of_cyclicDualProbe
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k n : ℕ)
    (c : Fin (k + 1) → ℝ)
    (q :
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
        H n).FeatureHilbert)
    (hq :
      (∫ b,
        inner ℝ q
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
              H n).feature b)
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta.le)) ≠ 0) :
    (∫ b,
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
        (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedSelectedDegreeFeature
          H beta hbeta.le n).feature b
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta.le)) ≠ 0 := by
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta.le
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let S₀ := periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryFourEdgeWilsonSelectedDegreeFeature
    H beta hbeta.le n
  let r := (Real.exp (-beta)) ^
    (periodicHypercubicEvenPositiveBoundaryTemporalResidualPlaquettes H).card
  have hr : 0 < r :=
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonResidualDegreeZeroScalar_pos H beta
  have hBase : (∫ b, p b • S₀.feature b ∂μ) ≠ 0 := by
    simpa [μ, p, S₀] using
      periodicHypercubicEvenBoundaryMarginal_selectedFourEdgeWilsonDegreeFeature_integral_ne_zero_of_cyclicDualProbe
        H beta hbeta k n c q hq
  have hScaled : Real.sqrt r • (∫ b, p b • S₀.feature b ∂μ) ≠ 0 :=
    smul_ne_zero (ne_of_gt (Real.sqrt_pos.2 hr)) hBase
  have hEq :=
    RealHilbertKernelFeature.nonnegSMul_weighted_integral_eq_sqrt_smul
      S₀ μ p r hr.le
  simpa [μ, p, S₀, r,
    periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedSelectedDegreeFeature] using
    hEq.trans_ne hScaled

/-- Weighted inner products in the full direct-sum feature are exactly the
literal full positive-boundary temporal Wilson kernel. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_weighted_inner_eq_fullKernel
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ)
    (a : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 → ℝ)
    (b c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    inner ℝ
        (a b •
          (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
            H beta hbeta n).feature b)
        (a c •
          (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
            H beta hbeta n).feature c) =
      a b * a c *
        periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel H beta b c := by
  let C := periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
    H beta hbeta n
  rw [real_inner_smul_left, real_inner_smul_right]
  rw [← C.kernel_eq_inner]
  simp [C, periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature]
  ring

/-- Main full-sector strictness theorem.  Every centered nonzero normalized-
trace boundary polynomial at positive coupling has a positive Fock degree whose
protected component forces strict positivity of the **complete literal**
positive-boundary temporal Wilson Gram form.

All residual plaquettes remain present through their actual degree-zero Fock
sector, and all complementary multi-degree terms remain in the Schur-PSD
remainder.  Strictness is therefore protected without a cancellation or
marginal-transport-defect assumption. -/
theorem periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_fullPositiveBoundaryWilsonGram_strict
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1),
      0 < (i : ℕ) ∧
      ∃ q :
        (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
          H (i : ℕ)).FeatureHilbert,
        (∫ b,
          inner ℝ q
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
              (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryDegreeFeature
                H (i : ℕ)).feature b)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta.le)) ≠ 0 ∧
        0 < ∫ b₁, ∫ b₂,
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₁ *
            periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b₂ *
            periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel
              H beta b₁ b₂
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta.le)
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta.le) := by
  rcases
    periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomial_exists_positiveDegree_protectedPositiveBoundaryWilsonSelectedGram_strict
      H beta hbeta k c hc hzero with
    ⟨i, hi, q, hq, _hProtectedStrict⟩
  let n := (i : ℕ)
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 positiveBoundaryTemporalWilsonBoundaryFullStrictnessTwoRankPositive beta hbeta.le
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let R := periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedRemainderFeature
    H beta hbeta.le n
  let S := periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryProtectedSelectedDegreeFeature
    H beta hbeta.le n
  let C := periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
    H beta hbeta.le n
  have hIntegrable : Integrable (fun b => p b • C.feature b) μ := by
    simpa [C, p, μ] using
      periodicHypercubicEvenBoundaryMarginalWeightedPositiveBoundaryWilsonFullDecompositionFeature_integrable
        H beta hbeta.le k c n
  have hSelectedMoment : (∫ b, p b • S.feature b ∂μ) ≠ 0 := by
    simpa [S, p, μ, n] using
      periodicHypercubicEvenBoundaryMarginal_protectedPositiveBoundaryWilsonSelectedDegreeFeature_integral_ne_zero_of_cyclicDualProbe
        H beta hbeta k n c q hq
  have hFullMoment : (∫ b, p b • C.feature b ∂μ) ≠ 0 := by
    have hAdd := RealHilbertKernelFeature.add_weighted_integral_ne_zero_of_right
      R S μ p
      (by
        simpa [C, R, S,
          periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature] using
          hIntegrable)
      hSelectedMoment
    simpa [C, R, S,
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature] using hAdd
  have hGram :
      0 < ∫ b₁, ∫ b₂,
        inner ℝ
          (p b₁ •
            (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
              H beta hbeta.le n).feature b₁)
          (p b₂ •
            (periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature
              H beta hbeta.le n).feature b₂) ∂μ ∂μ := by
    change 0 < ∫ b₁, ∫ b₂,
      inner ℝ (p b₁ • C.feature b₁) (p b₂ • C.feature b₂) ∂μ ∂μ
    exact C.weighted_inner_doubleIntegral_pos_of_integral_ne_zero
      μ p hIntegrable hFullMoment
  refine ⟨i, hi, q, hq, ?_⟩
  have hGramKernel :
      0 < ∫ b₁, ∫ b₂,
        p b₁ * p b₂ *
          periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullKernel
            H beta b₁ b₂ ∂μ ∂μ := by
    simpa only [
      periodicHypercubicEvenPositiveBoundaryTemporalWilsonBoundaryFullDecompositionFeature_weighted_inner_eq_fullKernel] using
      hGram
  simpa [p, μ, n] using hGramKernel

end

end MathlibAnalytic
end MGAP4D
