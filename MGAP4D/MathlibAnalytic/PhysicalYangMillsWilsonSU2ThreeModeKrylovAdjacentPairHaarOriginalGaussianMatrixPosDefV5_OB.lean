import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianAllFiniteStrictGramV5_OA
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# P4-Q2-OB — genuine SU2 Wilson Gaussian Gram matrices are positive-definite and invertible

OA established, with no rank or physical source hypothesis, that for
EVERY finite family of distinct genuine SU(2) holonomies x_i and
EVERY nonzero real coefficient vector a, the EXACT original temporal
Wilson Gaussian Gram quadratic form
  Σ_i Σ_j a_i a_j exp(b chi(x_i,x_j))
is strictly positive for every b>0.

OB now transports that completed analytic result into the pinned
mathlib matrix Positive Definiteness API:
  M_(ij)=exp(b chi(x_i,x_j))=p4Q2NJ_originalSU2WilsonTemporalSection b x_i x_j.
First prove Hermitian/symmetric from the ORIGINAL NN SU2 real-eight
Gaussian symmetry, then show the genuine matrix quadratic
  star(a) ⬝ᵥ (M *ᵥ a)
equals OA's exact signed finite Gram energy.

Thus M.PosDef holds in mathlib, and so the *actual finite* Gram
matrix is a unit, its determinant is nonzero, and its inverse is
also positive-definite. These follow from proved matrix positivity,
not an invented rank or positivity hypothesis.

Crucial boundary: existence of a finite inverse or pointwise strictly
positive eigenvalue is NOT a volume-uniform physical coercive bound
U0; neither full Gauss-law physical GI covariance, endpoint transport,
arbitrary-depth fine transfer nor continuum mass gap is claimed.
Original two interacting Wilson posterior laws, Perron half-density,
Gauss-law source and true spatial Wilson factors are unchanged.
No Dobrushin, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OB_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OB_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OB_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OB_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OB_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "k" => p4Q2NJ_originalSU2WilsonTemporalSection

/-- Real finite Gram matrix of the literal original temporal Wilson
SU(2) kernel, with neither synthetic feature nor synthetic posterior. -/
noncomputable def p4Q2OB_originalTemporalGaussianGramMatrix
    (b : ℝ) {ι : Type} [Fintype ι]
    (points : ι → Gauge) : Matrix ι ι ℝ :=
  fun i j => k b (points i) (points j)

/-- The true SU2 Wilson Gaussian Gram matrix is Hermitian because
the ORIGINAL normalized SU2 Wilson temporal kernel is symmetric. -/
theorem p4Q2OB_originalTemporalGaussianGram_isHermitian
    (b : ℝ) {ι : Type} [Fintype ι]
    (points : ι → Gauge) :
    (p4Q2OB_originalTemporalGaussianGramMatrix b points).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change star (k b (points j) (points i)) = k b (points i) (points j)
  simpa using
    (p4Q2NN_originalSU2TemporalWilsonSection_symmetric
      b (points j) (points i))

/-- The pinned mathlib Hermitian dotProduct/mulVec matrix form equals
precisely OA's already-proved original finite signed Gaussian Gram
quadratic form, including the original exp(b) normalization. -/
theorem p4Q2OB_originalTemporalGaussianGram_dotProduct_eq
    (b : ℝ) {ι : Type} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ) :
    star a ⬝ᵥ
        (p4Q2OB_originalTemporalGaussianGramMatrix b points *ᵥ a) =
      p4Q2NR_originalTemporalExactGram b points a := by
  classical
  change (∑ i : ι, a i *
      (∑ j : ι, k b (points i) (points j) * a j)) =
    p4Q2NR_originalTemporalExactGram b points a
  unfold p4Q2NR_originalTemporalExactGram
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- MAIN: full arbitrary-finite matrix POSITIVE DEFINITENESS for
the genuine original SU2 temporal Wilson Gaussian kernel at every b>0.
This is matrix-level, not an artificial assumption on its rank. -/
theorem p4Q2OB_originalTemporalGaussianGram_posDef
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (hpoints : Function.Injective points) :
    (p4Q2OB_originalTemporalGaussianGramMatrix b points).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (p4Q2OB_originalTemporalGaussianGram_isHermitian b points)
  intro a ha
  rw [p4Q2OB_originalTemporalGaussianGram_dotProduct_eq]
  exact p4Q2OA_originalTemporalExactGram_pos_of_coefficients_ne_zero
    b hb points hpoints a ha

/-- Every such actual finite original Wilson Gram matrix is invertible
in mathlib's matrix unit sense. No uniform norm bound is asserted. -/
theorem p4Q2OB_originalTemporalGaussianGram_isUnit
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (hpoints : Function.Injective points) :
    IsUnit (p4Q2OB_originalTemporalGaussianGramMatrix b points) := by
  classical
  exact (p4Q2OB_originalTemporalGaussianGram_posDef b hb points hpoints).isUnit

/-- Nonvanishing determinant of the EXACT positive definite
finite Gram matrix, without asserting a uniform determinant floor. -/
theorem p4Q2OB_originalTemporalGaussianGram_det_ne_zero
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (hpoints : Function.Injective points) :
    (p4Q2OB_originalTemporalGaussianGramMatrix b points).det ≠ 0 := by
  classical
  exact ((Matrix.isUnit_iff_isUnit_det
    (p4Q2OB_originalTemporalGaussianGramMatrix b points)).mp
      (p4Q2OB_originalTemporalGaussianGram_isUnit b hb points hpoints)).ne_zero

/-- Inverse of the genuine finite original Wilson Gaussian Gram matrix
is again positive definite; no volume-independent conditioning follows. -/
theorem p4Q2OB_originalTemporalGaussianGram_inv_posDef
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (hpoints : Function.Injective points) :
    ((p4Q2OB_originalTemporalGaussianGramMatrix b points)⁻¹).PosDef := by
  classical
  exact (p4Q2OB_originalTemporalGaussianGram_posDef b hb points hpoints).inv

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OB_originalTemporalGaussianGram_isHermitian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OB_originalTemporalGaussianGram_dotProduct_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OB_originalTemporalGaussianGram_posDef
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OB_originalTemporalGaussianGram_isUnit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OB_originalTemporalGaussianGram_det_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OB_originalTemporalGaussianGram_inv_posDef
