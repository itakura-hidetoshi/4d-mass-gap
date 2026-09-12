import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryGramL2KernelIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

local instance boundaryOpenHalfProductL2SideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance boundaryOpenHalfProductL2SpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryOpenHalfProductL2SpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryOpenHalfProductL2SpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryOpenHalfProductL2SpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryOpenHalfProductL2SpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Product of the actual shared-boundary Haar measure and the positive
open-half Haar measure.  This is the natural measure for viewing the completed
positive Wilson Gram feature as one two-variable Hilbert-Schmidt kernel. -/
noncomputable def periodicHypercubicEvenBoundaryOpenHalfHaarMeasure
    (H N : ℕ) : Measure
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N) :=
  (periodicHypercubicEvenBoundaryHaarMeasure H N).prod
    (periodicHypercubicEvenOpenHalfHaarMeasure H N)

/-- The completed positive Wilson Gram feature is jointly measurable in the
shared-boundary and positive-open-half variables.  Pointwise measurability in
only the open-half variable is not enough for the later rank-one Bochner
integral; this theorem supplies the genuine product-space receipt. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2) := by
  let Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ
  have hc : Measurable
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge)) :=
    (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
      H Gauge).measurable
  have hpair : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (p.2, periodicHypercubicEvenOpenHalfOrientationCorrection H p.2)) :=
    measurable_snd.prodMk (hc.comp measurable_snd)
  have hdiag : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        (p.1,
          (p.2, periodicHypercubicEvenOpenHalfOrientationCorrection H p.2))) :=
    measurable_fst.prodMk hpair
  have hd :=
    periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity_measurable
      H N hN beta hbeta
  have hsqrt : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (p.1,
              (p.2,
                periodicHypercubicEvenOpenHalfOrientationCorrection
                  H p.2))).toReal)) :=
    Real.continuous_sqrt.measurable.comp
      ((ENNReal.measurable_toReal.comp hd).comp hdiag)
  have heq :
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2) =
      fun p =>
        Real.sqrt
          ((periodicHypercubicEvenSpecialUnitaryBoundaryFiberedGibbsDensity
            H N hN beta hbeta
            (p.1,
              (p.2,
                periodicHypercubicEvenOpenHalfOrientationCorrection
                  H p.2))).toReal) := by
    funext p
    exact
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_eq_sqrt_diagonalDensity
        H N hN beta hbeta p.1 p.2
  rw [heq]
  exact hsqrt

/-- The actual completed positive Wilson Gram feature has integrable squared
norm on boundary × open-half product Haar measure.  The proof uses only joint
measurability, finiteness of normalized compact Haar products, and the existing
uniform reciprocal-partition-function bound. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_norm_sq_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2)
      (periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N) := by
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let productMeasure := periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta hbeta
  let bound : ℝ := Real.sqrt (C.base.partitionFunction⁻¹)
  letI : IsFiniteMeasure boundaryMeasure := by
    dsimp [boundaryMeasure, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  letI : IsFiniteMeasure halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  letI : IsFiniteMeasure productMeasure := by
    dsimp [productMeasure, periodicHypercubicEvenBoundaryOpenHalfHaarMeasure]
    infer_instance
  have hm :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
      H N hN beta hbeta
  have hsqMeasurable : Measurable
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2) :=
    hm.norm.pow_const 2
  exact Integrable.of_bound hsqMeasurable.aestronglyMeasurable (bound ^ 2)
    (Filter.Eventually.of_forall fun p => by
      let g := periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
        H N hN beta hbeta p.1 p.2
      have hg0 : 0 ≤ g := by
        dsimp [g]
        exact periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_nonneg
          H N hN beta hbeta p.1 p.2
      have hbound0 : 0 ≤ bound := by
        dsimp [bound]
        exact Real.sqrt_nonneg _
      have hle : g ≤ bound := by
        dsimp [g, bound, C]
        exact
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_le_sqrt_inv_partitionFunction
            H N hN beta hbeta p.1 p.2
      have hprod : 0 ≤ (bound - g) * (bound + g) :=
        mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hbound0 hg0)
      change |‖g‖ ^ 2| ≤ bound ^ 2
      rw [abs_of_nonneg (sq_nonneg ‖g‖), Real.norm_eq_abs, abs_of_nonneg hg0]
      nlinarith)

/-- The actual two-variable compact Wilson Gram feature belongs to
`L²(boundary Haar × open-half Haar)`. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    MemLp
      (fun p :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2)
      2
      (periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N) :=
  (memLp_two_iff_integrable_sq_norm
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_jointMeasurable
      H N hN beta hbeta).aestronglyMeasurable).2
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_norm_sq_integrable
      H N hN beta hbeta)

/-- The product Haar `L²` Hilbert space carrying the actual compact Wilson
boundary/open-half Gram kernel. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryBoundaryOpenHalfL2
    (H N : ℕ) : Type :=
  Lp ℝ 2 (periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N)

/-- Canonical product-Haar `L²` vector represented by the actual completed
positive Wilson boundary/open-half Gram feature. -/
noncomputable def periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryOpenHalfL2 H N :=
  (periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
    H N hN beta hbeta).toLp
      (fun p =>
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2)

/-- The product-Haar Hilbert norm is exactly the integrated squared completed
positive Gram feature.  This is the Hilbert-Schmidt square-norm identity needed
for the subsequent analysis/synthesis and rank-one operator construction. -/
theorem periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2_norm_sq
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
        H N hN beta hbeta‖ ^ 2 =
      ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N) := by
  let v :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureProductL2
      H N hN beta hbeta
  let hv :=
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_memLp_two
      H N hN beta hbeta
  calc
    ‖v‖ ^ 2 = inner ℝ v v := by
      simpa using (real_inner_self_eq_norm_sq v).symm
    _ = ∫ p, inner ℝ (v p) (v p)
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N) :=
      MeasureTheory.L2.inner_def v v
    _ = ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N) := by
      apply integral_congr_ae
      filter_upwards [hv.coeFn_toLp] with p hp
      rw [show v p =
          periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
            H N hN beta hbeta p.1 p.2 by exact hp]
      exact real_inner_self_eq_norm_sq _

end

end MathlibAnalytic
end MGAP4D