import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFullSpatialWilsonFeatureExponentialV5_LE
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# P4-Q2-LF — full spatial SU(2) Wilson feature = genuine finite-coordinate Gram

LD injects the ACTUAL full spatial SU(2) configuration into one finite
EuclideanSpace indexed by (physical link, real matrix entry).
LE identifies the literal full Wilson crossing kernel as an
exponential of a sum of actual one-link SU(2) real-feature pairings.

We prove the exact full-spatial inner-product identity, so this entire
physical Wilson kernel has one true finite-dimensional real-feature
exponential, including its original -beta*number-of-links factor.

For EACH degree n, the nth power of this FULL product-feature inner
is exactly a finite positive Gram sum of all n-fold actual spatial
matrix-coordinate monomials. Every such monomial belongs to the
Stone-Weierstrass DENSE spatial coordinate algebra already proved in LD.

This does NOT yet claim integrated strict positivity, Haar moment
completeness, whole-spatial transfer injectivity, centered Wilson
GI two-context minor, H1-C3 or continuum mass gap.
No sorry/admit, new axiom, synthetic rank, or posterior replacement.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint
section SpatialProduct
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Coord" => ((Fin 2 × Fin 2) × Bool)
local notation "ProductCoord" => (Link × Coord)
local notation "FullPhi" => p4Q2LD_originalSpatialMatrixRealFeature H
local notation "Phi" => specialUnitaryMatrixRealFeature 2

local instance p4Q2LF_linkFintype : Fintype Link :=
  Fintype.ofFinite _

/-- The full ORIGINAL finite-volume real Hilbert-Schmidt spatial
feature inner product is exactly the sum of original single-link
SU(2) real feature inner products. -/
theorem p4Q2LF_originalSpatialFeatureInner_eq_linkSum
    (A B : Cfg) :
    inner ℝ (FullPhi A) (FullPhi B) =
      ∑ e : Link, inner ℝ (Phi (A e)) (Phi (B e)) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [p4Q2LD_originalSpatialMatrixRealFeature_apply]
  apply Finset.sum_congr rfl
  intro e he
  rw [PiLp.inner_apply]

/-- The LE link-list exponent equals a SINGLE Euclidean feature
pairing, retaining the exact length of the ORIGINAL canonical
spatial-link list. This is the actual finite number of links. -/
theorem p4Q2LF_originalSpatialCrossingExponent_eq_fullFeatureInner
    (b : ℝ) (A B : Cfg) :
    p4Q2LE_originalSpatialCrossingFeatureExponent H b A B =
      -b * ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) +
        (b / 2) * inner ℝ (FullPhi A) (FullPhi B) := by
  have hList (es : List Link) :
      (es.map fun e =>
        -b + (b / 2) * inner ℝ (Phi (A e)) (Phi (B e))).sum =
      -b * (es.length : ℝ) +
        (b / 2) * (es.map fun e =>
          inner ℝ (Phi (A e)) (Phi (B e))).sum := by
    induction es with
    | nil => simp
    | cons e es ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [ih]
        push_cast
        ring
  have hSum :
      ((periodicHypercubicEvenSpatialSliceLinkList H).map fun e =>
        inner ℝ (Phi (A e)) (Phi (B e))).sum =
      ∑ e : Link, inner ℝ (Phi (A e)) (Phi (B e)) := by
    classical
    simpa [periodicHypercubicEvenSpatialSliceLinkList] using
      (Finset.sum_toList
        (Finset.univ : Finset Link)
        (fun e : Link => inner ℝ (Phi (A e)) (Phi (B e)))).symm
  unfold p4Q2LE_originalSpatialCrossingFeatureExponent
  rw [hList, hSum,
    ← p4Q2LF_originalSpatialFeatureInner_eq_linkSum H A B]

/-- Literal original full temporal crossing Wilson kernel is the
one exponential of the complete spatial Hilbert-Schmidt pairing. -/
theorem p4Q2LF_originalSpatialWilsonCrossing_eq_fullFeatureExponential
    (b : ℝ) (A B : Cfg) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
      H 2 b A B =
      Real.exp (-b *
        ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) +
        (b / 2) * inner ℝ (FullPhi A) (FullPhi B)) := by
  rw [p4Q2LE_originalSpatialWilsonCrossing_eq_featureExponential,
    p4Q2LF_originalSpatialCrossingExponent_eq_fullFeatureInner]

/-- ACTUAL degree-n spatial matrix-coordinate monomial, constructed
from the continuous real/imaginary entries of each physical SU(2)
link in the very same full spatial Wilson configuration. -/
noncomputable def p4Q2LF_originalSpatialMatrixCoordinateMonomial
    (n : ℕ) (a : Fin n → ProductCoord) : C(Cfg, ℝ) :=
  ∏ i : Fin n,
    p4Q2LD_originalSpatialLinkRealCoordinate H (a i).1 (a i).2

@[simp] theorem p4Q2LF_originalSpatialMatrixCoordinateMonomial_apply
    (n : ℕ) (a : Fin n → ProductCoord) (A : Cfg) :
    p4Q2LF_originalSpatialMatrixCoordinateMonomial H n a A =
      ∏ i : Fin n, FullPhi A (a i) := by
  classical
  calc
    p4Q2LF_originalSpatialMatrixCoordinateMonomial H n a A =
        ∏ i : Fin n, Phi (A (a i).1) (a i).2 := by
      simp [p4Q2LF_originalSpatialMatrixCoordinateMonomial]
    _ = ∏ i : Fin n, FullPhi A (a i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rcases h : a i with ⟨e, q⟩
      simp [h]

/-- Every full spatial matrix-coordinate monomial belongs to
the proved DENSE actual spatial coordinate algebra from LD. -/
theorem p4Q2LF_originalSpatialMatrixCoordinateMonomial_mem_algebra
    (n : ℕ) (a : Fin n → ProductCoord) :
    p4Q2LF_originalSpatialMatrixCoordinateMonomial H n a ∈
      p4Q2LD_originalSpatialMatrixCoordinateAlgebra H := by
  classical
  unfold p4Q2LF_originalSpatialMatrixCoordinateMonomial
  exact Subalgebra.prod_mem _ (fun i _ =>
    Algebra.mem_adjoin_of_mem (Set.mem_range_self (a i)))

/-- Each original FULL spatial real Wilson Hilbert-Schmidt feature
inner power is an EXACT finite positive Gram expansion of the
actual full-lattice matrix-coordinate monomials. Valid for every
degree, including the constant degree-zero term. -/
theorem p4Q2LF_originalFullSpatialFeatureInnerPow_eq_monomialGram
    (n : ℕ) (A B : Cfg) :
    (inner ℝ (FullPhi A) (FullPhi B)) ^ n =
      ∑ a : Fin n → ProductCoord,
        p4Q2LF_originalSpatialMatrixCoordinateMonomial H n a A *
          p4Q2LF_originalSpatialMatrixCoordinateMonomial H n a B := by
  have hInner :
      inner ℝ (FullPhi A) (FullPhi B) =
        ∑ q : ProductCoord, FullPhi A q * FullPhi B q := by
    rw [PiLp.inner_apply]
    simp only [realScalarInner_eq_mul]
  rw [hInner, Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]
  simp only [p4Q2LF_originalSpatialMatrixCoordinateMonomial_apply]

end SpatialProduct
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LF_originalSpatialFeatureInner_eq_linkSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LF_originalSpatialCrossingExponent_eq_fullFeatureInner
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LF_originalSpatialWilsonCrossing_eq_fullFeatureExponential
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LF_originalSpatialMatrixCoordinateMonomial_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LF_originalSpatialMatrixCoordinateMonomial_mem_algebra
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LF_originalFullSpatialFeatureInnerPow_eq_monomialGram
