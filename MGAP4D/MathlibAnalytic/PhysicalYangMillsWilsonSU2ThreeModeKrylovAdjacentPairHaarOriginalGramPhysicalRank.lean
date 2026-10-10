import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalInnerRankNullity
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# P4-Q2-AF2: rank of the genuine original Wilson frozen posterior Gram

The exact original full-spatial-link frozen-Wilson Gram matrix is the
Gram matrix of the authentic physical all-link synthesis vectors.
There is no substitute Gram, covariance proxy, altered posterior or transfer.

For any finite real Hilbert family, the Gram matrix and its linear
synthesis have identical kernels. Their ranks therefore coincide,
including all exact linear dependencies.

This is a finite-depth, finite-volume rank theorem; no depth-uniform
positive singular-value lower bound or continuum mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter Matrix
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2900000
set_option synthInstance.maxHeartbeats 850000

/-- Gram multiplication is precisely the family of inner products
against the actual finite synthesized vector. -/
theorem p4Q2AF_realFiniteGram_mulVec_apply
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : ι → ℝ) (i : ι) :
    ((Matrix.gram ℝ v) *ᵥ a) i =
      ⟪v i, (p4Q2AD_realFiniteSynthesis v) a⟫_ℝ := by
  classical
  change (∑ j : ι, ⟪v i, v j⟫_ℝ * a j) =
    ⟪v i, ∑ j : ι, a j • v j⟫_ℝ
  simp only [inner_sum, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Exactly the same coefficient kernel for the true Gram and its
underlying physical synthesis (including dependent families). -/
theorem p4Q2AF_realFiniteGram_mem_ker_iff
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) (a : ι → ℝ) :
    a ∈ (Matrix.gram ℝ v).mulVecLin.ker ↔
      a ∈ (p4Q2AD_realFiniteSynthesis v).ker := by
  classical
  let T := p4Q2AD_realFiniteSynthesis v
  have hGram : star a ⬝ᵥ ((Matrix.gram ℝ v) *ᵥ a) =
      ‖T a‖ ^ 2 := by
    have h := Matrix.star_dotProduct_gram_mulVec v a a
    change star a ⬝ᵥ ((Matrix.gram ℝ v) *ᵥ a) =
      ⟪T a, T a⟫_ℝ at h
    rwa [real_inner_self_eq_norm_sq] at h
  constructor
  · intro ha
    have hM : (Matrix.gram ℝ v) *ᵥ a = 0 := by
      simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using ha
    have hz : ‖T a‖ ^ 2 = 0 := by
      rw [hM, dotProduct_zero] at hGram
      exact hGram.symm
    have hZero : ‖T a‖ = 0 := by
      nlinarith [norm_nonneg (T a)]
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp hZero)
  · intro ha
    have hTa : T a = 0 := LinearMap.mem_ker.mp ha
    apply LinearMap.mem_ker.mpr
    change (Matrix.gram ℝ v) *ᵥ a = 0
    funext i
    rw [p4Q2AF_realFiniteGram_mulVec_apply, hTa, inner_zero_right]
    rfl

/-- Matrix rank equals genuine physical image dimension; the proof
works even when the finite Hilbert family has exact dependencies. -/
theorem p4Q2AF_realFiniteGram_rank_eq_physical_finrank
    {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ι → E) :
    (Matrix.gram ℝ v).rank =
      Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range := by
  classical
  let T := p4Q2AD_realFiniteSynthesis v
  let M := Matrix.gram ℝ v
  have hKer : M.mulVecLin.ker = T.ker := by
    ext a
    exact p4Q2AF_realFiniteGram_mem_ker_iff v a
  have hM : Module.finrank ℝ M.mulVecLin.range +
      Module.finrank ℝ M.mulVecLin.ker =
        Module.finrank ℝ (ι → ℝ) :=
    M.mulVecLin.finrank_range_add_finrank_ker
  have hT : Module.finrank ℝ T.range +
      Module.finrank ℝ T.ker =
        Module.finrank ℝ (ι → ℝ) :=
    T.finrank_range_add_finrank_ker
  rw [hKer] at hM
  change Module.finrank ℝ M.mulVecLin.range =
    Module.finrank ℝ T.range
  omega

local instance p4AF2Group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AF2Compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AF2SecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AF2Measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AF2Borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AF2LinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AF2Complete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- The original all-link posterior Gram is literally the Gram
matrix of the original frozen-Wilson physical innovation vectors. -/
theorem fineRightKrylov_originalGram_eq_physicalInnovationGram
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :
    let H := halfExtent (n+1)
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let V (j : Fin (r+1)) :=
      WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)))
    fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r = Matrix.gram ℝ V := by
  classical
  let H := halfExtent (n+1)
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let V (j : Fin (r+1)) :=
    WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
      I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)))
  change fineRightKrylovPairHaarResidualGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r = Matrix.gram ℝ V
  ext i j
  simp only [fineRightKrylovPairHaarResidualGram,
    pairHaarSpatialLinkResidualGram, Matrix.sum_apply,
    Matrix.gram_apply, PiLp.inner_apply]
  rfl

/-- Exact original-Wilson posterior Gram matrix rank equals the
number of independent physical full-link modes at each finite n,r. -/
theorem fineRightKrylov_originalGram_rank_eq_physicalImage_finrank
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r).rank =
      Module.finrank ℝ
        (fineRightKrylov_originalPhysicalFullLinkSynthesis
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r).range := by
  let H := halfExtent (n+1)
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let V (j : Fin (r+1)) :=
    WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
      I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)))
  have hGram :
      fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r = Matrix.gram ℝ V :=
    fineRightKrylov_originalGram_eq_physicalInnovationGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  rw [hGram]
  exact p4Q2AF_realFiniteGram_rank_eq_physical_finrank V

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
