import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianMatrixPosDefV5_OB
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# P4-Q2-OC — original SU(2) Wilson Gaussian exact finite interpolation

OA/OB established strict positivity, matrix PosDef, IsUnit, and a
positive-definite inverse for the literal original SU(2) Wilson
Gaussian Gram at EVERY b>0 and EVERY finite set of distinct genuine
holonomies x_i.

OC converts this verified finite positive matrix into an EXACT
interpolation construction in the real linear span of the ORIGINAL
Wilson kernel sections, with NO additional rank or nonsingularity
hypothesis:
  M_ij := exp(b * chi(x_i,x_j))
  c := target ᵥ* M⁻¹
  I_target(g) := Σ_j c_j k_b(x_j,g).
Then I_target(x_i) = target_i, for ANY real target vector and any
finite distinct points. The explicit right action (vecMul) avoids an
unproven transposition or normalization convention. It also proves
that a finite linear combination of distinct true kernel sections
can vanish identically only if ALL its coefficients vanish.

This is genuine finite interpolation in C(SU(2),R). It is NOT the
same as the original physical Gauss-law source/receiver or a single
physical endpoint source. No U0 volume-uniform lower spectral bound,
arbitrary depth fine transfer, H1-C3, or continuum Yang–Mills mass
gap follows from existence of finite interpolation.

Both original interacting Wilson posterior laws, true Perron
half-density, Gauss-law physical source, spatial Wilson factors and
their genuine temporal Wilson sections remain untouched.
No Dobrushin, sorry, admit, or new unproved axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "k" => p4Q2NJ_originalSU2WilsonTemporalSection
local notation "M" => p4Q2OB_originalTemporalGaussianGramMatrix

/-- Finite real linear combination of the LITERAL original temporal
SU(2) Wilson kernel sections. -/
noncomputable def p4Q2OC_originalWilsonFiniteSectionCombination
    (b : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (coeff : ι → ℝ) : C(Gauge, ℝ) :=
  ∑ j : ι, coeff j • k b (points j)

/-- Pointwise evaluation of an original Wilson section combination
is EXACTLY the right matrix action by the true OA/OB Gram matrix. -/
theorem p4Q2OC_originalWilsonFiniteSectionCombination_apply
    (b : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (coeff : ι → ℝ) (i : ι) :
    p4Q2OC_originalWilsonFiniteSectionCombination b points coeff (points i) =
      (coeff ᵥ* M b points) i := by
  change (∑ j : ι, coeff j * k b (points j) (points i)) =
    ∑ j : ι, coeff j * (M b points) j i
  rfl

/-- Explicit coefficients solving ANY finite original Wilson kernel
interpolation problem on distinct genuine SU(2) holonomies.
These are the targets multiplied on the right by the actual finite
Gram inverse, not coefficients of a synthetic proxy kernel. -/
noncomputable def p4Q2OC_originalWilsonFiniteInterpolationCoefficients
    (b : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (target : ι → ℝ) : ι → ℝ :=
  target ᵥ* (M b points)⁻¹

/-- OA/OB make the Gram inverse an EXACT right solver, for arbitrary
real finite target values; no uniform inverse bound is asserted. -/
theorem p4Q2OC_originalWilsonFiniteInterpolationCoefficients_exact
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (hpoints : Function.Injective points)
    (target : ι → ℝ) :
    (p4Q2OC_originalWilsonFiniteInterpolationCoefficients b points target)
        ᵥ* M b points = target := by
  classical
  let A : Matrix ι ι ℝ := M b points
  have hUnit : IsUnit A :=
    p4Q2OB_originalTemporalGaussianGram_isUnit b hb points hpoints
  have hDet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hUnit
  change (target ᵥ* A⁻¹) ᵥ* A = target
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul A hDet,
    Matrix.vecMul_one]

/-- An explicit genuine Wilson-kernel interpolation function belongs
to the actual finite real linear span of the original sections. -/
noncomputable def p4Q2OC_originalWilsonFiniteInterpolant
    (b : ℝ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (target : ι → ℝ) : C(Gauge, ℝ) :=
  p4Q2OC_originalWilsonFiniteSectionCombination b points
    (p4Q2OC_originalWilsonFiniteInterpolationCoefficients b points target)

/-- MAIN exact finite interpolation: the actual original Wilson
Gaussian kernel section sum realizes EVERY prescribed real value at
all genuine distinct SU(2) sample points. -/
theorem p4Q2OC_originalWilsonFiniteInterpolant_apply
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (hpoints : Function.Injective points)
    (target : ι → ℝ) (i : ι) :
    p4Q2OC_originalWilsonFiniteInterpolant b points target (points i) =
      target i := by
  change
    p4Q2OC_originalWilsonFiniteSectionCombination b points
      (p4Q2OC_originalWilsonFiniteInterpolationCoefficients b points target)
      (points i) = target i
  rw [p4Q2OC_originalWilsonFiniteSectionCombination_apply]
  exact congrFun
    (p4Q2OC_originalWilsonFiniteInterpolationCoefficients_exact
      b hb points hpoints target) i

/-- Surjectivity of the literal finite evaluation map on full
SU(2): every target vector is attained by a true Wilson-section
finite linear combination. -/
theorem p4Q2OC_originalWilsonFiniteEvaluation_surjective
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (hpoints : Function.Injective points) :
    ∀ target : ι → ℝ, ∃ f : C(Gauge, ℝ),
      (∀ i : ι, f (points i) = target i) := by
  intro target
  exact ⟨p4Q2OC_originalWilsonFiniteInterpolant b points target,
    p4Q2OC_originalWilsonFiniteInterpolant_apply b hb points hpoints target⟩

/-- Finite ORIGINAL Wilson sections at pairwise distinct SU2 points
are linearly independent in the strong no-cancellation sense:
if their full continuous linear combination vanishes, then all
real coefficients vanish. -/
theorem p4Q2OC_originalWilsonFiniteSectionCombination_eq_zero_iff
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (points : ι → Gauge) (hpoints : Function.Injective points)
    (coeff : ι → ℝ) :
    p4Q2OC_originalWilsonFiniteSectionCombination b points coeff = 0
      ↔ coeff = 0 := by
  classical
  let A : Matrix ι ι ℝ := M b points
  have hUnit : IsUnit A :=
    p4Q2OB_originalTemporalGaussianGram_isUnit b hb points hpoints
  have hDet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det A).mp hUnit
  constructor
  · intro hZero
    have hVec : coeff ᵥ* A = 0 := by
      funext i
      have hi := congrArg (fun f : C(Gauge, ℝ) => f (points i)) hZero
      rw [p4Q2OC_originalWilsonFiniteSectionCombination_apply] at hi
      simpa using hi
    have hInverse := congrArg (fun v : ι → ℝ => v ᵥ* A⁻¹) hVec
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv A hDet,
      Matrix.vecMul_one, Matrix.zero_vecMul] at hInverse
    exact hInverse
  · intro hZero
    subst coeff
    simp [p4Q2OC_originalWilsonFiniteSectionCombination]

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OC_originalWilsonFiniteSectionCombination_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OC_originalWilsonFiniteInterpolationCoefficients_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OC_originalWilsonFiniteInterpolant_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OC_originalWilsonFiniteEvaluation_surjective
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OC_originalWilsonFiniteSectionCombination_eq_zero_iff
