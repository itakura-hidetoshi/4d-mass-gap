import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryVacuumMomentPositivity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfAnalysisOperator
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance wilsonBoundaryAnalysisNonzeroSideLength (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance wilsonBoundaryAnalysisNonzeroTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonBoundaryAnalysisNonzeroCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonBoundaryAnalysisNonzeroSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonBoundaryAnalysisNonzeroMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonBoundaryAnalysisNonzeroBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance wilsonBoundaryAnalysisNonzeroBoundaryFinite (H N : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance wilsonBoundaryAnalysisNonzeroOpenHalfFinite (H N : ℕ) :
    IsFiniteMeasure (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

local instance wilsonBoundaryAnalysisNonzeroBoundaryNeZero (H N : ℕ) :
    NeZero (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  unfold periodicHypercubicEvenBoundaryHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure
  infer_instance

local instance wilsonBoundaryAnalysisNonzeroOpenHalfNeZero (H N : ℕ) :
    NeZero (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  unfold periodicHypercubicEvenOpenHalfHaarMeasure
  unfold FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure
  infer_instance

local instance wilsonBoundaryAnalysisNonzeroProductNeZero (H N : ℕ) :
    NeZero ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
      (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H N
  let ν := periodicHypercubicEvenOpenHalfHaarMeasure H N
  refine ⟨Measure.measure_univ_ne_zero.mp ?_⟩
  rw [← Set.univ_prod_univ, Measure.prod_prod]
  exact mul_ne_zero
    (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ))
    (Measure.measure_univ_ne_zero.mpr (NeZero.ne ν))

/-- Continuous constant-one vector on the actual shared-boundary compact space. -/
noncomputable def periodicHypercubicEvenBoundaryConstantOneContinuous
    (H N : ℕ) :
    C(PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N, ℝ) :=
  { toFun := fun _ => 1
    continuous_toFun := continuous_const }

/-- Continuous constant-one vector on the actual positive open-half compact
configuration space. -/
noncomputable def periodicHypercubicEvenOpenHalfConstantOneContinuous
    (H N : ℕ) :
    C(PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N, ℝ) :=
  { toFun := fun _ => 1
    continuous_toFun := continuous_const }

/-- Constant-one shared-boundary vector in actual boundary Haar `L²`. -/
noncomputable def periodicHypercubicEvenBoundaryConstantOneL2
    (H N : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N) :=
  ContinuousMap.toLp (E := ℝ) 2
    (periodicHypercubicEvenBoundaryHaarMeasure H N) ℝ
    (periodicHypercubicEvenBoundaryConstantOneContinuous H N)

/-- Constant-one positive-open-half vector in actual open-half Haar `L²`. -/
noncomputable def periodicHypercubicEvenOpenHalfConstantOneL2
    (H N : ℕ) :
    Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N) :=
  ContinuousMap.toLp (E := ℝ) 2
    (periodicHypercubicEvenOpenHalfHaarMeasure H N) ℝ
    (periodicHypercubicEvenOpenHalfConstantOneContinuous H N)

/-- The physical completed-positive boundary/open-half Gram feature is
integrable, not only square-integrable, on the normalized compact product Haar
space. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2)
      ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let bound : ℝ := Real.sqrt (C.base.partitionFunction⁻¹)
  refine Integrable.of_bound
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
      H N hN beta hbeta).aestronglyMeasurable bound ?_
  filter_upwards [] with p
  have hnonneg :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
      H N hN beta hbeta p.1 p.2
  have hle :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
      H N hN beta hbeta p.1 p.2
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa [bound, C] using hle

/-- The integral of the actual completed-positive Gram feature over complete
boundary × positive-open-half Haar space is strictly positive. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_integral_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < ∫ p :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta p.1 p.2
      ∂((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  rw [integral_pos_iff_support_of_nonneg]
  · have hsupport :
        Function.support
            (fun p :
              PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
              periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
                H N hN beta hbeta p.1 p.2) = Set.univ := by
      ext p
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact ne_of_gt
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pos
          H N hN beta hbeta p.1 p.2)
    rw [hsupport]
    have hne :
        ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N)) Set.univ ≠ 0 :=
      Measure.measure_univ_ne_zero.mpr
        (NeZero.ne ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N)))
    exact lt_of_le_of_ne (zero_le _) hne.symm
  · intro p
    exact le_of_lt
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pos
        H N hN beta hbeta p.1 p.2)
  · exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_integrable
      H N hN beta hbeta

/-- The Hilbert--Schmidt pairing of the actual Wilson kernel against constant
one in both variables is exactly its ordinary product-Haar integral. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pairing_constantOne
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta)
        (periodicHypercubicEvenBoundaryConstantOneL2 H N)
        (periodicHypercubicEvenOpenHalfConstantOneL2 H N) =
      ∫ p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2
        ∂((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
          (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  let μ := periodicHypercubicEvenBoundaryHaarMeasure H N
  let ν := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let f := periodicHypercubicEvenBoundaryConstantOneL2 H N
  let g := periodicHypercubicEvenOpenHalfConstantOneL2 H N
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H N hN beta hbeta
  have hK :
      K =ᵐ[μ.prod ν]
        fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2 := by
    change
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
          H N hN beta hbeta =ᵐ[μ.prod ν]
        fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2
    simpa [μ, ν, periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
        H N hN beta hbeta).coeFn_toLp
  have hf :
      f =ᵐ[μ] fun _ => (1 : ℝ) := by
    simpa [f, periodicHypercubicEvenBoundaryConstantOneL2,
      periodicHypercubicEvenBoundaryConstantOneContinuous] using
      (ContinuousMap.coeFn_toLp
        (p := (2 : ENNReal)) (𝕜 := ℝ) μ
        (periodicHypercubicEvenBoundaryConstantOneContinuous H N))
  have hg :
      g =ᵐ[ν] fun _ => (1 : ℝ) := by
    simpa [g, periodicHypercubicEvenOpenHalfConstantOneL2,
      periodicHypercubicEvenOpenHalfConstantOneContinuous] using
      (ContinuousMap.coeFn_toLp
        (p := (2 : ENNReal)) (𝕜 := ℝ) ν
        (periodicHypercubicEvenOpenHalfConstantOneContinuous H N))
  have hfProd :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N => f p.1) =ᵐ[μ.prod ν]
        fun _ => (1 : ℝ) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq hf
  have hgProd :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N => g p.2) =ᵐ[μ.prod ν]
        fun _ => (1 : ℝ) := by
    simpa [Function.comp_def] using
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq hg
  have hTensor :
      realL2ExternalTensor f g =ᵐ[μ.prod ν] fun _ => (1 : ℝ) := by
    filter_upwards [realL2ExternalTensor_coeFn f g, hfProd, hgProd] with p ht hfp hgp
    rw [ht]
    simp only [realL2ExternalTensorFunction, hfp, hgp, one_mul]
  unfold realL2HilbertSchmidtKernelPairing
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hK, hTensor] with p hkp htp
  rw [hkp, htp]
  simp [periodicHypercubicEven_real_inner_eq_mul]

/-- The actual physical Wilson analysis matrix coefficient between constant-one
boundary and open-half vectors is strictly positive. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_constantOne_inner_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryConstantOneL2 H N))
      (periodicHypercubicEvenOpenHalfConstantOneL2 H N) := by
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner]
  rw [periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_pairing_constantOne]
  exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_integral_pos
    H N hN beta hbeta

/-- The actual physical Wilson boundary analysis sends the constant-one
boundary vector to a nonzero open-half `L²` vector. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_constantOne_ne_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryConstantOneL2 H N) ≠ 0 := by
  intro hzero
  have hpos :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_constantOne_inner_pos
      H N hN beta hbeta
  rw [hzero] at hpos
  simpa using hpos

/-- The actual compact Wilson boundary-to-open-half analysis operator is
nonzero.  No cancellation, rank, or marginal-transport assumption is used. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_ne_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
      H N hN beta hbeta ≠ 0 := by
  intro hzero
  have happly :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_constantOne_ne_zero
      H N hN beta hbeta
  apply happly
  simp [hzero]

/-- The actual `A†A` Wilson boundary Gram factor has a strictly positive
quadratic form on the constant-one boundary vector. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_constantOne_inner_self_pos
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < inner ℝ
      (periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H N hN beta hbeta
        (periodicHypercubicEvenBoundaryConstantOneL2 H N))
      (periodicHypercubicEvenBoundaryConstantOneL2 H N) := by
  rw [periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_inner_self]
  exact sq_pos_of_pos
    (norm_pos_iff.mpr
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_constantOne_ne_zero
        H N hN beta hbeta))

/-- Consequently the canonical actual Wilson boundary Gram factor `A†A` is
nonzero. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_ne_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
      H N hN beta hbeta ≠ 0 := by
  intro hzero
  have hpos :=
    periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator_constantOne_inner_self_pos
      H N hN beta hbeta
  rw [hzero] at hpos
  simpa using hpos

end

end MathlibAnalytic
end MGAP4D
