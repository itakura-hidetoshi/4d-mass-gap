import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianFockLowerBoundsV5_NS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianPSDSignedPolynomialV5_NP
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Tactic

/-!
# P4-Q2-NT — genuine signed Wilson–Perron coordinate-monomial detection

NP and NO proved that the polynomial algebra in the ACTUAL continuous
real-eight SU(2) matrix features is uniformly dense, and that the
genuine two-interacting-Wilson-posterior Perron-minus-Dirac functional
is nonzero. NT refines the polynomial witness to ONE finite PRODUCT
of actual real matrix-coordinate observables (including the empty
product). This is the precise multiplicative target for eventual
Hilbert Fock-tensor-moment integration.

The proof reuses mathlib Algebra.adjoin_eq_span: the polynomial algebra
is exactly the REAL LINEAR SPAN of the coordinate multiplicative
submonoid. Its dense span therefore detects every nonzero bounded real
linear functional. Submonoid closure induction turns a monomial into an
explicit finite list product, without an artificial posterior or any
rank/injectivity hypothesis.

This step does NOT establish positivity of the signed Gaussian double
integral, Bochner integrability of all Fock tensor moments, moment/kernel
identification, fixed-beta kernel section linear-span density, physical
signed receiver variance, U0, H1-C3 or the continuum mass gap.
Those analytical bridges remain to be proved. It preserves the two
genuine Wilson posteriors, the Gauss-law source, Perron half-density and
the genuine temporal Wilson interaction exactly as in NI/NJ/NL/NS.
No sorry, admit or new unproved axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NT_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2NT_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2NT_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2NT_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2NT_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Index" => (Fin 2 × Fin 2) × Bool
local notation "coord" => p4Q2NO_originalSU2RealEightCoordinate

/-- Finite multiplicative monomials in the genuine real-eight SU(2)
coordinates; notably, NO's whole polynomial ALGEBRA is larger than
this submonoid, but equals its real linear span. -/
noncomputable def p4Q2NT_originalRealEightCoordinateMonomials :
    Submonoid C(Gauge, ℝ) :=
  Submonoid.closure (Set.range coord)

/-- Exact algebra-to-module passage: finite coordinate monomials
already have dense REAL LINEAR SPAN, by NO/NP Stone–Weierstrass.
This makes no assertion about the genuine Gaussian kernel sections. -/
theorem p4Q2NT_originalRealEightCoordinateMonomialSpan_dense :
    Dense
      (↑(Submodule.span ℝ
        (↑p4Q2NT_originalRealEightCoordinateMonomials : Set C(Gauge, ℝ)))
        : Set C(Gauge, ℝ)) := by
  have hSpan :
      Submodule.span ℝ
        (↑p4Q2NT_originalRealEightCoordinateMonomials : Set C(Gauge, ℝ)) =
        p4Q2NO_originalSU2RealEightPolynomialAlgebra.toSubmodule := by
    change
      Submodule.span ℝ
        (↑(Submonoid.closure (Set.range coord)) : Set C(Gauge, ℝ)) =
          (Algebra.adjoin ℝ (Set.range coord)).toSubmodule
    exact (Algebra.adjoin_eq_span ℝ (Set.range coord)).symm
  rw [hSpan]
  exact p4Q2NP_originalSU2RealEightPolynomialAlgebra_dense

/-- Every NONZERO continuous signed real functional on the original
SU(2) continuous observables is detected by a SINGLE genuine
coordinate monomial; no synthetic measure or Fock moment is assumed. -/
theorem p4Q2NT_nonzeroSignedFunctional_has_realEightMonomialWitness
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ f : C(Gauge, ℝ),
      f ∈ p4Q2NT_originalRealEightCoordinateMonomials ∧ L f ≠ 0 := by
  by_contra hExists
  have hVanish (f : C(Gauge, ℝ))
      (hf : f ∈ p4Q2NT_originalRealEightCoordinateMonomials) :
      L f = 0 := by
    by_contra hNe
    exact hExists ⟨f, hf, hNe⟩
  have hEq : Set.EqOn (⇑L) (⇑(0 : C(Gauge, ℝ) →L[ℝ] ℝ))
      (↑p4Q2NT_originalRealEightCoordinateMonomials : Set C(Gauge, ℝ)) := by
    intro f hf
    simpa using hVanish f hf
  have hLzero : L = 0 :=
    ContinuousLinearMap.ext_on
      p4Q2NT_originalRealEightCoordinateMonomialSpan_dense hEq
  exact hL hLzero

/-- Constructive normal form for an actual coordinate monomial:
a finite ordered list of the genuine matrix-coordinate functions.
The empty list represents the constant one function. -/
theorem p4Q2NT_originalRealEightMonomial_eq_finiteCoordinateProduct
    (f : C(Gauge, ℝ))
    (hf : f ∈ p4Q2NT_originalRealEightCoordinateMonomials) :
    ∃ indices : List Index, f = (indices.map coord).prod := by
  change f ∈ Submonoid.closure (Set.range coord) at hf
  induction hf using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨[i], by simp⟩
  | one =>
      exact ⟨[], by simp⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨is, his⟩ := ihx
      obtain ⟨js, hjs⟩ := ihy
      refine ⟨is ++ js, ?_⟩
      rw [his, hjs]
      simp [List.map_append, List.prod_append]

/-- A single finite coordinate product detects every nonzero real
bounded signed functional, strengthening NP's arbitrary polynomial
witness to one concrete multiplicative observable. -/
theorem p4Q2NT_nonzeroSignedFunctional_has_coordinateProductWitness
    (L : C(Gauge, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ indices : List Index, L ((indices.map coord).prod) ≠ 0 := by
  obtain ⟨f, hf, hLf⟩ :=
    p4Q2NT_nonzeroSignedFunctional_has_realEightMonomialWitness L hL
  obtain ⟨indices, hEq⟩ :=
    p4Q2NT_originalRealEightMonomial_eq_finiteCoordinateProduct f hf
  exact ⟨indices, by simpa only [← hEq] using hLf⟩

/-- MAIN ACTUAL WILSON–PERRON SPECIALIZATION.  For each genuine
two-interacting-Wilson-posterior signed rho, any boundary SU(2)
source y and any Dirac coefficient c, ONE finite coordinate product
already has nonzero genuine Haar-minus-Dirac pairing.

There is NO assertion that this polynomial lies in the fixed-beta
kernel section LINEAR SPAN. NT still needs the full genuine Fock
tensor Bochner-moment and signed Gaussian energy theorem. -/
theorem p4Q2NT_originalWilsonPerronSignedDefect_has_coordinateProductWitness
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) (bpos : 0 < b)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (y : Gauge) (c : ℝ) :
    ∃ indices : List Index,
      p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c
        ((indices.map coord).prod) ≠ 0 := by
  exact p4Q2NT_nonzeroSignedFunctional_has_coordinateProductWitness
    (p4Q2NJ_originalSignedDiracDefectCLM H b hb e z y c)
    (p4Q2NJ_originalSignedDiracDefectCLM_ne_zero
      H b hb bpos e z y c)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NT_originalRealEightCoordinateMonomialSpan_dense
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NT_nonzeroSignedFunctional_has_realEightMonomialWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NT_originalRealEightMonomial_eq_finiteCoordinateProduct
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NT_nonzeroSignedFunctional_has_coordinateProductWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NT_originalWilsonPerronSignedDefect_has_coordinateProductWitness
