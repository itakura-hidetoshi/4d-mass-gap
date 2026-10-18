import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2FeatureCoordinateMomentSeparationV5_KL
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# P4-Q2-KN — exact finite tensor-coordinate polynomial expansion of the SU(2) Wilson kernel

The genuine SU(2) defining matrix realification Phi constructed in
the existing finite Wilson kernel features has EIGHT continuous real
coordinates, shown to generate a uniformly dense algebra in KK/KL.

For each natural degree n and tuple a : Fin n → Coord, define the
actual coordinate monomial m_a(g)=∏_i Phi(g)[a_i]. Prove explicitly
that every such monomial is in the SAME KK coordinate algebra.

We then prove the literal finite power expansion
    <Phi(g),Phi(h)>^n = ∑_(a : Fin n → Coord) m_a(g) m_a(h).
This is an exact finite positive Gram decomposition of EACH Wilson
feature-kernel homogeneous term. Its future Haar double integral is
a sum of squares of the original coordinate polynomial moments.

There is no asymptotic series interchanging, no posterior substitution,
new axiom/sorry, artificial rank, H1-C3 or mass-gap claim here.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Coord" => ((Fin 2 × Fin 2) × Bool)
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "Alg" => p4Q2KK_originalSU2MatrixCoordinateAlgebra

/-- Genuine SU(2) coordinate monomial of arbitrary finite degree,
formed ONLY from the eight real/imaginary SU(2) matrix entries. -/
noncomputable def p4Q2KN_originalSU2MatrixCoordinateMonomial
    (n : ℕ) (a : Fin n → Coord) : C(Gauge, ℝ) :=
  ∏ i : Fin n, p4Q2KK_originalSU2MatrixRealCoordinate (a i)

/-- The actual matrix-coordinate polynomial evaluates as the literal
finite product of the genuine Euclidean feature coordinates. -/
@[simp] theorem p4Q2KN_originalSU2MatrixCoordinateMonomial_apply
    (n : ℕ) (a : Fin n → Coord) (g : Gauge) :
    p4Q2KN_originalSU2MatrixCoordinateMonomial n a g =
      ∏ i : Fin n, Phi g (a i) := by
  simp [p4Q2KN_originalSU2MatrixCoordinateMonomial]

/-- The existing KK Stone–Weierstrass algebra includes ALL
finite products of the original SU(2) defining matrix coordinates,
not merely the original linear coordinate generators. -/
theorem p4Q2KN_originalSU2MatrixCoordinateMonomial_mem_algebra
    (n : ℕ) (a : Fin n → Coord) :
    p4Q2KN_originalSU2MatrixCoordinateMonomial n a ∈ Alg := by
  classical
  unfold p4Q2KN_originalSU2MatrixCoordinateMonomial
  exact Subalgebra.prod_mem _ (fun i _ =>
    Algebra.mem_adjoin_of_mem (Set.mem_range_self (a i)))

/-- The original real Hilbert-Schmidt SU(2) feature inner power
is a FINITE positive Gram sum of all degree-n true coordinate
monomials. This is valid for every n, including the constant n=0
term, and every actual physical SU(2) pair g,h. -/
theorem p4Q2KN_originalSU2RealFeatureInnerPow_eq_coordinateMonomialGram
    (n : ℕ) (g h : Gauge) :
    (inner ℝ (Phi g) (Phi h)) ^ n =
      ∑ a : Fin n → Coord,
        p4Q2KN_originalSU2MatrixCoordinateMonomial n a g *
          p4Q2KN_originalSU2MatrixCoordinateMonomial n a h := by
  have hInner :
      inner ℝ (Phi g) (Phi h) =
        ∑ q : Coord, (Phi g q) * (Phi h q) := by
    rw [PiLp.inner_apply]
    simp only [realScalarInner_eq_mul]
  rw [hInner, Fintype.sum_pow]
  simp only [Finset.prod_mul_distrib]
  simp only [p4Q2KN_originalSU2MatrixCoordinateMonomial_apply]

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KN_originalSU2MatrixCoordinateMonomial_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KN_originalSU2MatrixCoordinateMonomial_mem_algebra
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KN_originalSU2RealFeatureInnerPow_eq_coordinateMonomialGram
