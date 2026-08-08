import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryHilbertSchmidtOperatorPositive
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfAnalysisOperator
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtGramFactorizationOperator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H N : ℕ) :
    SFinite (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenBoundaryHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
  infer_instance

local instance (H N : ℕ) :
    SFinite (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  dsimp [periodicHypercubicEvenOpenHalfHaarMeasure,
    FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
  infer_instance

/-- The canonical scalar section obtained by integrating the actual compact
Wilson Gram feature against a complete boundary-Haar `L²` vector. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) : ℝ :=
  ∫ b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta b x * f b
    ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)

/-- The physical feature kernel used by rectangular Riesz analysis has the
expected completed-positive-Gram representative almost everywhere. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (fun p =>
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
        H N hN beta hbeta p) =ᵐ[
      (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)]
      (fun p => periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta p.1 p.2) := by
  let hmem :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
      H N hN beta hbeta
  simpa [periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2,
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2,
    periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
      hmem.coeFn_toLp

/-- The analysis section is a.e.-strongly measurable on open-half Haar space. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection_aestronglyMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    AEStronglyMeasurable
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
        H N hN beta hbeta f)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  have hphi :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
      H N hN beta hbeta
  have hf : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        f p.1)
      (boundaryMeasure.prod halfMeasure) :=
    (Lp.aestronglyMeasurable f).comp_fst
  have hpsi : AEStronglyMeasurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2 * f p.1)
      (boundaryMeasure.prod halfMeasure) :=
    hphi.aestronglyMeasurable.mul hf
  simpa [periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection,
    boundaryMeasure, halfMeasure] using
      hpsi.prod_swap.integral_prod_right'

/-- The squared analysis section is integrable on open-half Haar space.  This
is extracted directly from the weighted triple-integrability theorem already
used for complete-boundary Gram positivity. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection_sq_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    Integrable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
          H N hN beta hbeta f x) ^ 2)
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  have htriple :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_weightedTriple_integrable
      H N hN beta hbeta f
  have hiter : Integrable
      (fun x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        ∫ p :
          PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N,
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta p.1 x * f p.1) *
            (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta p.2 x * f p.2)
          ∂(boundaryMeasure.prod boundaryMeasure))
      halfMeasure := by
    simpa [boundaryMeasure, halfMeasure] using htriple.integral_prod_right
  apply hiter.congr
  filter_upwards with x
  simpa [periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection,
    boundaryMeasure, pow_two] using
      (MeasureTheory.integral_prod_mul
        (μ := boundaryMeasure) (ν := boundaryMeasure)
        (fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta b x * f b)
        (fun c : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta c x * f c))

/-- The analysis section belongs to the actual open-half Haar `L²` Hilbert
space. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection_memLp_two
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    MemLp
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
        H N hN beta hbeta f)
      2
      (periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  apply (memLp_two_iff_integrable_sq_norm
    (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection_aestronglyMeasurable
      H N hN beta hbeta f)).2
  exact
    (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection_sq_integrable
      H N hN beta hbeta f).congr
      (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs, sq_abs])

/-- Canonical open-half `L²` vector represented by the scalar analysis
section. -/
noncomputable def periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N) :=
  (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection_memLp_two
    H N hN beta hbeta f).toLp
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
        H N hN beta hbeta f)

/-- The section `L²` vector has the expected scalar representative. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_coeFn
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    (fun x => periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2
      H N hN beta hbeta f x) =ᵐ[
        periodicHypercubicEvenOpenHalfHaarMeasure H N]
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
        H N hN beta hbeta f := by
  exact
    (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection_memLp_two
      H N hN beta hbeta f).coeFn_toLp

/-- The section `L²` norm is exactly the open-half integral of the squared
scalar analysis section. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_norm_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2
        H N hN beta hbeta f‖ ^ 2 =
      ∫ x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N,
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
          H N hN beta hbeta f x) ^ 2
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
  let s := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2
    H N hN beta hbeta f
  calc
    ‖s‖ ^ 2 = inner ℝ s s := by
      simpa using (real_inner_self_eq_norm_sq s).symm
    _ = ∫ x, inner ℝ (s x) (s x)
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) :=
      MeasureTheory.L2.inner_def s s
    _ = ∫ x,
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
          H N hN beta hbeta f x) ^ 2
        ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_coeFn
          H N hN beta hbeta f] with x hx
      rw [hx, realL2Scalar_inner_eq_mul]
      ring

/-- The raw product integrand defining the rectangular feature pairing is
integrable for arbitrary complete boundary/open-half `L²` test vectors. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeature_weightedPair_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (g : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N)) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2 * (f p.1 * g p.2))
      ((periodicHypercubicEvenBoundaryHaarMeasure H N).prod
        (periodicHypercubicEvenOpenHalfHaarMeasure H N)) := by
  let K := periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
    H N hN beta hbeta
  let E := realL2ExternalTensor f g
  have h := MeasureTheory.L2.integrable_inner K E
  apply h.congr
  filter_upwards [
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn
      H N hN beta hbeta,
    realL2ExternalTensor_coeFn
      (μ := periodicHypercubicEvenBoundaryHaarMeasure H N)
      (ν := periodicHypercubicEvenOpenHalfHaarMeasure H N) f g] with p hK hE
  rw [show K p =
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta p.1 p.2 by exact hK,
    show E p = f p.1 * g p.2 by exact hE]
  exact realL2Scalar_inner_eq_mul _ _

/-- Matrix coefficients of the section `L²` vector are exactly the
rectangular physical feature pairings. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (g : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N)) :
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2
          H N hN beta hbeta f) g =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta) f g := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let raw := fun p :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta p.1 p.2 * (f p.1 * g p.2)
  have hraw :=
    periodicHypercubicEvenWilsonBoundaryGramFeature_weightedPair_integrable
      H N hN beta hbeta f g
  calc
    inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2
          H N hN beta hbeta f) g =
        ∫ x,
          periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
            H N hN beta hbeta f x * g x
          ∂halfMeasure := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_coeFn
          H N hN beta hbeta f] with x hx
      rw [hx, realL2Scalar_inner_eq_mul]
    _ = ∫ x, ∫ b,
          raw (b, x) ∂boundaryMeasure ∂halfMeasure := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
          H N hN beta hbeta f x =
          ∫ b,
            periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
              H N hN beta hbeta b x * f b ∂boundaryMeasure by
        rfl]
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with b
      simp [raw]
      ring
    _ = ∫ p, raw p ∂(boundaryMeasure.prod halfMeasure) := by
      exact (MeasureTheory.integral_prod_symm raw hraw).symm
    _ = realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
          H N hN beta hbeta) f g := by
      rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2_coeFn
          H N hN beta hbeta,
        realL2ExternalTensor_coeFn
          (μ := boundaryMeasure) (ν := halfMeasure) f g] with p hK hfg
      rw [hK, hfg, realL2Scalar_inner_eq_mul]
      rfl

/-- The abstract rectangular Fréchet--Riesz analysis vector is exactly the
canonical `L²` section vector. -/
theorem periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_eq_analysisOperator
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2
        H N hN beta hbeta f =
      periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta f := by
  let s := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2
    H N hN beta hbeta f
  let a := periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
    H N hN beta hbeta f
  have hinner : ∀ g : Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N),
      inner ℝ s g = inner ℝ a g := by
    intro g
    rw [show inner ℝ s g =
        realL2HilbertSchmidtKernelPairing
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureRectangularL2
            H N hN beta hbeta) f g by
      exact periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_inner
        H N hN beta hbeta f g]
    symm
    exact periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator_inner
      H N hN beta hbeta f g
  have hdiff := hinner (s - a)
  have hself : inner ℝ (s - a) (s - a) = 0 := by
    rw [inner_sub_left, hdiff]
    simp
  have hnormsq : ‖s - a‖ ^ 2 = 0 := by
    simpa using hself
  have hnorm : ‖s - a‖ = 0 := by
    nlinarith [norm_nonneg (s - a)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The actual square Gram pairing has the same diagonal quadratic form as the
rectangular feature analysis map. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_self_eq_analysis_inner_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : Lp ℝ 2 (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
          H N hN beta hbeta) f f =
      inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f) := by
  calc
    realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
          H N hN beta hbeta) f f =
        ∫ x,
          (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection
            H N hN beta hbeta f x) ^ 2
          ∂(periodicHypercubicEvenOpenHalfHaarMeasure H N) := by
      simpa [periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSection] using
        periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_self_eq_integral_sq
          H N hN beta hbeta f
    _ = ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2
          H N hN beta hbeta f‖ ^ 2 := by
      symm
      exact periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_norm_sq
        H N hN beta hbeta f
    _ = ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f‖ ^ 2 := by
      rw [periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisSectionL2_eq_analysisOperator]
    _ = inner ℝ
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f)
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta f) := by
      symm
      exact real_inner_self_eq_norm_sq _

/-- The actual compact Wilson square Gram pairing admits the exact quotient-
level feature Gram factorization through the open-half analysis operator. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_gramFactorization
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    RealL2HilbertSchmidtKernelPairingGramFactorization
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta)
      (Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N))
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta) := by
  exact
    realL2HilbertSchmidtKernelPairing_gramFactorization_of_symmetric_of_quadratic
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta)
      (Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N))
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_symmetric
        H N hN beta hbeta)
      (periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_self_eq_analysis_inner_self
        H N hN beta hbeta)

/-- Exact operator-level Gram factorization for the actual compact Wilson
shared-boundary Hilbert--Schmidt operator:

`T_G = A_φ† A_φ`. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_eq_adjoint_comp_analysis
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta =
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta)†.comp
        (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
          H N hN beta hbeta) := by
  exact
    realL2HilbertSchmidtKernelOperator_eq_adjoint_comp_of_gramFactorization
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta)
      (Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N))
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_gramFactorization
        H N hN beta hbeta)

/-- The previously constructed factorized physical operator is exactly the
shared-boundary Gram Hilbert--Schmidt operator. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_eq_factorizedOperator
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta =
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H N hN beta hbeta := by
  rw [periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_eq_adjoint_comp_analysis]
  rfl

/-- Consequently the actual shared-boundary Gram operator has the exact
analysis-square norm, not merely the earlier Hilbert--Schmidt upper bound. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_norm_eq_analysis_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta‖ ^ 2 := by
  exact
    realL2HilbertSchmidtKernelOperator_norm_eq_analysis_sq_of_gramFactorization
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta)
      (Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N))
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_gramFactorization
        H N hN beta hbeta)

/-- Audit-visible actual Wilson exact `A†A` factorization package. -/
structure PeriodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtFactorizationPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  pairingGram :
    RealL2HilbertSchmidtKernelPairingGramFactorization
      (periodicHypercubicEvenBoundaryCompletedPositiveGramKernelPairL2
        H N hN beta hbeta)
      (Lp ℝ 2 (periodicHypercubicEvenOpenHalfHaarMeasure H N))
      (periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta)
  operatorFactorization :
    periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta =
      periodicHypercubicEvenWilsonBoundaryGramFeatureFactorizedOperator
        H N hN beta hbeta
  exactNorm :
    ‖periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator
        H N hN beta hbeta‖ =
      ‖periodicHypercubicEvenWilsonBoundaryGramFeatureAnalysisOperator
        H N hN beta hbeta‖ ^ 2

/-- Construct the exact actual Wilson `A†A` factorization receipt. -/
theorem periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtFactorizationPackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtFactorizationPackage
      H N hN beta hbeta :=
  { pairingGram :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtPairing_gramFactorization
        H N hN beta hbeta
    operatorFactorization :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_eq_factorizedOperator
        H N hN beta hbeta
    exactNorm :=
      periodicHypercubicEvenWilsonBoundaryGramHilbertSchmidtOperator_norm_eq_analysis_sq
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
