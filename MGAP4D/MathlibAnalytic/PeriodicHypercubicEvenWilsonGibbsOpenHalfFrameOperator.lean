import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonGibbsBoundaryOpenHalfProductL2
import MGAP4D.MathlibAnalytic.RealHilbertIntegratedSelfRankOnePositive
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

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

/-- The actual compact Wilson boundary-indexed open-half `L²` feature has an
integrable squared Hilbert norm in the boundary Haar variable.

This is the precise Fubini bridge from the already-constructed joint
`L²(boundary × open-half)` Wilson feature to the Bochner frame-operator
hypothesis `∫ ‖v_b‖² db < ∞`.  No Hilbert-valued currying measurability is used
here. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_boundary_sqNorm_integrable
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Integrable
      (fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
          H N hN beta hbeta b‖ ^ 2)
      (periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  let Boundary :=
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N
  let Half :=
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let f : Boundary × Half → ℝ := fun p =>
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta p.1 p.2‖ ^ 2
  letI : SFinite halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hprod : Integrable f (boundaryMeasure.prod halfMeasure) := by
    simpa [f, boundaryMeasure, halfMeasure,
      periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_norm_sq_integrable
        H N hN beta hbeta
  have hiter : Integrable
      (fun b : Boundary => ∫ x : Half, f (b, x) ∂halfMeasure)
      boundaryMeasure :=
    hprod.integral_prod_right
  refine hiter.congr ?_
  filter_upwards with b
  simpa [f, halfMeasure, Boundary, Half] using
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_norm_sq
      H N hN beta hbeta b).symm

/-- Fubini identifies the total boundary-indexed Hilbert-feature energy with
exactly the squared `L²(boundary × open-half)` norm density already constructed
for the physical compact Wilson Gram feature. -/
theorem
    periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_boundary_integral_sqNorm_eq_product
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ b,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
          H N hN beta hbeta b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) =
      ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N) := by
  let Boundary :=
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N
  let Half :=
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H N
  let boundaryMeasure := periodicHypercubicEvenBoundaryHaarMeasure H N
  let halfMeasure := periodicHypercubicEvenOpenHalfHaarMeasure H N
  let f : Boundary × Half → ℝ := fun p =>
    ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
      H N hN beta hbeta p.1 p.2‖ ^ 2
  letI : SFinite boundaryMeasure := by
    dsimp [boundaryMeasure, periodicHypercubicEvenBoundaryHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.boundaryPiMeasure]
    infer_instance
  letI : SFinite halfMeasure := by
    dsimp [halfMeasure, periodicHypercubicEvenOpenHalfHaarMeasure,
      FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure]
    infer_instance
  have hprod : Integrable f (boundaryMeasure.prod halfMeasure) := by
    simpa [f, boundaryMeasure, halfMeasure,
      periodicHypercubicEvenBoundaryOpenHalfHaarMeasure] using
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeature_product_norm_sq_integrable
        H N hN beta hbeta
  calc
    (∫ b,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
          H N hN beta hbeta b‖ ^ 2 ∂boundaryMeasure) =
        ∫ b : Boundary, ∫ x : Half, f (b, x) ∂halfMeasure ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards with b
      simpa [f, halfMeasure, Boundary, Half] using
        periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_norm_sq
          H N hN beta hbeta b
    _ = ∫ p : Boundary × Half, f p ∂(boundaryMeasure.prod halfMeasure) := by
      exact (MeasureTheory.integral_prod f hprod).symm
    _ = ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N) := by
      rfl

/-- The actual compact Wilson open-half frame operator obtained by integrating
self rank-one operators of the boundary-indexed physical Gram vectors.

The Bochner integral is total.  Its useful positivity and quadratic-form
properties are established below once the still-distinct `L²`-valued currying
measurability receipt is supplied. -/
noncomputable def periodicHypercubicEvenWilsonOpenHalfFrameOperator
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N :=
  realHilbertIntegratedSelfRankOne
    (periodicHypercubicEvenBoundaryHaarMeasure H N)
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
      H N hN beta hbeta)

/-- Exact bilinear form of the actual compact Wilson frame operator. -/
theorem periodicHypercubicEvenWilsonOpenHalfFrameOperator_inner
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hFeatureMeas : AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta)
      (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (f g : PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N) :
    inner ℝ
        (periodicHypercubicEvenWilsonOpenHalfFrameOperator
          H N hN beta hbeta f) g =
      ∫ b,
        inner ℝ
            (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
              H N hN beta hbeta b) f *
          inner ℝ
            (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
              H N hN beta hbeta b) g
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  exact realHilbertIntegratedSelfRankOne_inner hFeatureMeas
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_boundary_sqNorm_integrable
      H N hN beta hbeta) f g

/-- The actual compact Wilson open-half frame operator is symmetric once the
boundary-to-`L²` feature map is ae strongly measurable. -/
theorem periodicHypercubicEvenWilsonOpenHalfFrameOperator_isSymmetric
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hFeatureMeas : AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta)
      (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    ((periodicHypercubicEvenWilsonOpenHalfFrameOperator
      H N hN beta hbeta :
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N) :
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N).IsSymmetric := by
  exact realHilbertIntegratedSelfRankOne_isSymmetric hFeatureMeas
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_boundary_sqNorm_integrable
      H N hN beta hbeta)

/-- The actual compact Wilson open-half frame operator is positive in Mathlib's
Hilbert-space operator order. -/
theorem periodicHypercubicEvenWilsonOpenHalfFrameOperator_isPositive
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hFeatureMeas : AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta)
      (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    ((periodicHypercubicEvenWilsonOpenHalfFrameOperator
      H N hN beta hbeta :
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N) :
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N).IsPositive := by
  exact realHilbertIntegratedSelfRankOne_isPositive hFeatureMeas
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_boundary_sqNorm_integrable
      H N hN beta hbeta)

/-- Exact quadratic form: the physical compact Wilson frame energy is the
boundary Haar integral of squared boundary-feature coefficients. -/
theorem periodicHypercubicEvenWilsonOpenHalfFrameOperator_inner_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hFeatureMeas : AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta)
      (periodicHypercubicEvenBoundaryHaarMeasure H N))
    (f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N) :
    inner ℝ
        (periodicHypercubicEvenWilsonOpenHalfFrameOperator
          H N hN beta hbeta f) f =
      ∫ b,
        (inner ℝ
          (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
            H N hN beta hbeta b) f) ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
  exact realHilbertIntegratedSelfRankOne_inner_self hFeatureMeas
    (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_boundary_sqNorm_integrable
      H N hN beta hbeta) f

/-- The operator norm is controlled by the exact physical product-Haar feature
energy.  This is the Hilbert--Schmidt/frame bound needed before normalization
and spectral-cap arguments. -/
theorem periodicHypercubicEvenWilsonOpenHalfFrameOperator_norm_le_productFeatureEnergy
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenWilsonOpenHalfFrameOperator
        H N hN beta hbeta‖ ≤
      ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N) := by
  calc
    ‖periodicHypercubicEvenWilsonOpenHalfFrameOperator
        H N hN beta hbeta‖ ≤
      ∫ b,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
          H N hN beta hbeta b‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryHaarMeasure H N) := by
      exact realHilbertIntegratedSelfRankOne_norm_le_integral_sq_norm
        (periodicHypercubicEvenBoundaryHaarMeasure H N)
        (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
          H N hN beta hbeta)
    _ = ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N) :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_boundary_integral_sqNorm_eq_product
        H N hN beta hbeta

/-- Audit-visible actual compact-Wilson frame-operator receipt.  The only
separate analytic input is the `L²`-valued currying measurability of the already
jointly measurable physical scalar feature; square-integrability itself is
proved unconditionally above by Fubini. -/
structure PeriodicHypercubicEvenWilsonOpenHalfFrameOperatorPositivePackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hFeatureMeas : AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta)
      (periodicHypercubicEvenBoundaryHaarMeasure H N)) : Prop where
  featureSquareNormIntegrable :
    Integrable
      (fun b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N =>
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
          H N hN beta hbeta b‖ ^ 2)
      (periodicHypercubicEvenBoundaryHaarMeasure H N)
  featureEnergyFubini :
    (∫ b,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
          H N hN beta hbeta b‖ ^ 2
      ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)) =
      ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N)
  symmetric :
    ((periodicHypercubicEvenWilsonOpenHalfFrameOperator
      H N hN beta hbeta :
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N) :
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N).IsSymmetric
  positive :
    ((periodicHypercubicEvenWilsonOpenHalfFrameOperator
      H N hN beta hbeta :
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N) :
      PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N).IsPositive
  quadraticForm :
    ∀ f : PeriodicHypercubicEvenSpecialUnitaryOpenHalfL2 H N,
      inner ℝ
          (periodicHypercubicEvenWilsonOpenHalfFrameOperator
            H N hN beta hbeta f) f =
        ∫ b,
          (inner ℝ
            (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
              H N hN beta hbeta b) f) ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure H N)
  normLeProductFeatureEnergy :
    ‖periodicHypercubicEvenWilsonOpenHalfFrameOperator
        H N hN beta hbeta‖ ≤
      ∫ p,
        ‖periodicHypercubicEvenBoundaryCompletedPositiveGramFeature
          H N hN beta hbeta p.1 p.2‖ ^ 2
        ∂(periodicHypercubicEvenBoundaryOpenHalfHaarMeasure H N)

/-- Construct the complete actual compact-Wilson positive frame-operator
receipt from the single remaining Hilbert-valued measurability input. -/
noncomputable def periodicHypercubicEvenWilsonOpenHalfFrameOperatorPositivePackage
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hFeatureMeas : AEStronglyMeasurable
      (periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2
        H N hN beta hbeta)
      (periodicHypercubicEvenBoundaryHaarMeasure H N)) :
    PeriodicHypercubicEvenWilsonOpenHalfFrameOperatorPositivePackage
      H N hN beta hbeta hFeatureMeas :=
  { featureSquareNormIntegrable :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_boundary_sqNorm_integrable
        H N hN beta hbeta
    featureEnergyFubini :=
      periodicHypercubicEvenBoundaryCompletedPositiveGramFeatureL2_boundary_integral_sqNorm_eq_product
        H N hN beta hbeta
    symmetric :=
      periodicHypercubicEvenWilsonOpenHalfFrameOperator_isSymmetric
        H N hN beta hbeta hFeatureMeas
    positive :=
      periodicHypercubicEvenWilsonOpenHalfFrameOperator_isPositive
        H N hN beta hbeta hFeatureMeas
    quadraticForm :=
      periodicHypercubicEvenWilsonOpenHalfFrameOperator_inner_self
        H N hN beta hbeta hFeatureMeas
    normLeProductFeatureEnergy :=
      periodicHypercubicEvenWilsonOpenHalfFrameOperator_norm_le_productFeatureEnergy
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
