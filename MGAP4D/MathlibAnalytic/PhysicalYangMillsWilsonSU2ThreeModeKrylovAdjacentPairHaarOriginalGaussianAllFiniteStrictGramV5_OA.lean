import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianKernelSpanDenseV5_NZ
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic

/-!
# P4-Q2-OA — unconditionally strict ALL finite Gram positivity of genuine SU2 Wilson Gaussian

NY proved that for ANY nonzero real continuous signed functional L on
C(SU(2),R) and EVERY b>0, the full ORIGINAL Wilson temporal exponential
double signed energy T_L(exp(b chi)) is strictly positive, using genuine
uniform Banach exponential convergence and all nonnegative actual
tensor-coordinate signed energies. NZ independently proved fixed-b true
Wilson section LINEAR-SPAN density by Hahn–Banach.

OA specializes the universal NY result to ALL finite families of actual
SU(2) points with pairwise DISTINCT holonomies and ANY nonzero real
signed coefficient family, with NO added rank/nondegeneracy axiom.

For finitely many distinct points x_i construct the continuous
distance-Lagrange selector

  f_i(g) = ∏_(j ≠ i) dist(g, x_j).

Then f_i(x_i)>0, f_i(x_j)=0 for j != i. Thus the actual finite
evaluation functional L=Σ_i a_i eval_(x_i) is provably NONZERO whenever
at least one coefficient is nonzero. Next prove the exact identity

  T_L(F)= Σ_i Σ_j a_i a_j F(x_i,x_j)

for an arbitrary continuous pair F on FULL SU(2)×SU(2); in particular
the Banach exponential F=exp(b chi) equals the ORIGINAL physical
Wilson temporal Gaussian kernel by NY. Therefore

  0 < Σ_i Σ_j a_i a_j exp(b chi(x_i,x_j)).

Unlike the old NN pair determinant, this is unconditional for EVERY
finite index type and any number of distinct original SU(2) points.
The original two interacting Wilson posterior laws, Gauss-law source,
Perron half-density and right-spatial factors are untouched.

Strict finite Gram positivity is not physical GI covariance or
volume-uniform U0, endpoint-source connection, H1-C3 or continuum mass
gap. No artificial rank assumption, Dobrushin, sorry, admit or axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2OA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2OA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2OA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2OA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2OA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "k" => p4Q2NJ_originalSU2WilsonTemporalSection
local notation "Double" => p4Q2NX_originalSignedDoubleCLM
local notation "PairChi" => p4Q2NX_originalTemporalPairCharacter

/-- Genuine SU(2) finite-point separation certificate: finite
continuous product of distances to all *other* original holonomies.
Unlike a synthetic source, this is solely a test of linear independence
of actual point evaluation functionals. -/
noncomputable def p4Q2OA_originalFinitePointSelector
    {ι : Type*} [Fintype ι] (points : ι → Gauge) (i : ι) :
    C(Gauge, ℝ) := by
  classical
  refine ⟨fun g => ∏ j ∈ Finset.univ.erase i, dist g (points j), ?_⟩
  apply continuous_finset_prod
  intro j hj
  exact continuous_id.dist continuous_const

/-- A selector does not vanish at its own SU(2) point when all
the genuine holonomies are distinct. -/
theorem p4Q2OA_originalFinitePointSelector_self_pos
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (hpoints : Function.Injective points) (i : ι) :
    0 < p4Q2OA_originalFinitePointSelector points i (points i) := by
  classical
  change 0 < ∏ j ∈ Finset.univ.erase i, dist (points i) (points j)
  apply Finset.prod_pos
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact dist_pos.mpr (fun heq => hji (hpoints heq).symm)

/-- Every other original point is a root of the corresponding
continuous distance-Lagrange selector. -/
theorem p4Q2OA_originalFinitePointSelector_other_zero
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (i j : ι) (hij : j ≠ i) :
    p4Q2OA_originalFinitePointSelector points i (points j) = 0 := by
  classical
  change (∏ t ∈ Finset.univ.erase i, dist (points j) (points t)) = 0
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩)
  simp

/-- A finite real signed point evaluation functional on the original
full compact SU(2). No posterior law or physical detector is replaced. -/
noncomputable def p4Q2OA_originalFiniteSignedEvaluation
    {ι : Type*} [Fintype ι] (points : ι → Gauge) (a : ι → ℝ) :
    C(Gauge, ℝ) →L[ℝ] ℝ :=
  ∑ i : ι, (a i) • ContinuousMap.evalCLM ℝ (points i)

/-- Original finite signed point functional acts by exactly the
specified finite signed sum of true SU(2) point evaluations. -/
theorem p4Q2OA_originalFiniteSignedEvaluation_apply
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ) (f : C(Gauge, ℝ)) :
    p4Q2OA_originalFiniteSignedEvaluation points a f =
      ∑ i : ι, a i * f (points i) := by
  classical
  simp only [p4Q2OA_originalFiniteSignedEvaluation,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousMap.evalCLM_apply, smul_eq_mul]

/-- TRUE finite signed Dirac evaluations at distinct SU(2) points are
linearly independent. This is proved by explicit continuous point
selectors, with no rank or injectivity premise on a hypothetical
Gaussian feature; only the real points themselves are distinct. -/
theorem p4Q2OA_originalFiniteSignedEvaluation_ne_zero
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (hpoints : Function.Injective points)
    (a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    p4Q2OA_originalFiniteSignedEvaluation points a ≠ 0 := by
  classical
  obtain ⟨i, hai⟩ := ha
  let f : C(Gauge, ℝ) := p4Q2OA_originalFinitePointSelector points i
  have hEval :
      p4Q2OA_originalFiniteSignedEvaluation points a f =
        a i * f (points i) := by
    rw [p4Q2OA_originalFiniteSignedEvaluation_apply]
    apply Finset.sum_eq_single i
    · intro j hj hji
      have hZero :
          f (points j) = 0 :=
        p4Q2OA_originalFinitePointSelector_other_zero points i j hji
      simp [hZero]
    · intro hni
      exact (hni (Finset.mem_univ i)).elim
  have hNonzero : p4Q2OA_originalFiniteSignedEvaluation points a f ≠ 0 := by
    rw [hEval]
    exact mul_ne_zero hai
      (ne_of_gt (p4Q2OA_originalFinitePointSelector_self_pos
        points hpoints i))
  intro hZero
  have hContr : p4Q2OA_originalFiniteSignedEvaluation points a f = 0 := by
    rw [hZero]
    simp
  exact hNonzero hContr

/-- Applying the existing full SU(2) signed double CLM to an arbitrary
continuous pair observable gives the exact finite signed point Gram
double sum. No exchange of two infinite integrals occurs. -/
theorem p4Q2OA_originalFiniteSignedDouble_apply
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ)
    (F : C(Gauge × Gauge, ℝ)) :
    Double (p4Q2OA_originalFiniteSignedEvaluation points a) F =
      ∑ i : ι, ∑ j : ι,
        a i * a j * F (points i, points j) := by
  classical
  rw [p4Q2NX_originalSignedDoubleCLM_apply,
    p4Q2OA_originalFiniteSignedEvaluation_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [p4Q2NX_originalSignedPairSection_apply,
    p4Q2OA_originalFiniteSignedEvaluation_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [ContinuousMap.curry_apply]
  ring

/-- The true original temporal Wilson exponential finite Gram is
EXACTLY the double signed evaluation of the EXISTING Banach kernel. -/
theorem p4Q2OA_originalTemporalExactGram_eq_signedDouble
    (b : ℝ) {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ) :
    p4Q2NR_originalTemporalExactGram b points a =
      Double (p4Q2OA_originalFiniteSignedEvaluation points a)
        (NormedSpace.exp (b • PairChi)) := by
  rw [p4Q2OA_originalFiniteSignedDouble_apply]
  unfold p4Q2NR_originalTemporalExactGram
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [p4Q2NY_originalPairBanachExp_eq_trueTemporalWilson]

/-- MAIN all-finite strict positivity theorem. For EVERY positive
original Wilson coupling b and any finite family of DISTINCT ACTUAL
SU(2) points, EVERY nonzero signed coefficient vector has strictly
positive original Gaussian temporal Wilson Gram energy. -/
theorem p4Q2OA_originalTemporalExactGram_strict_pos
    (b : ℝ) (hb : 0 < b)
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (hpoints : Function.Injective points)
    (a : ι → ℝ) (ha : ∃ i, a i ≠ 0) :
    0 < p4Q2NR_originalTemporalExactGram b points a := by
  rw [p4Q2OA_originalTemporalExactGram_eq_signedDouble]
  exact p4Q2NY_originalSignedGaussianDoubleEnergy_pos
    (p4Q2OA_originalFiniteSignedEvaluation points a)
    (p4Q2OA_originalFiniteSignedEvaluation_ne_zero
      points hpoints a ha) b hb

/-- Matrix-language strict positive definiteness: every nonzero
vector in the real finite-index coefficient space is detected by
the ORIGINAL SU(2) temporal Wilson Gaussian Gram quadratic form. -/
theorem p4Q2OA_originalTemporalExactGram_pos_of_coefficients_ne_zero
    (b : ℝ) (hb : 0 < b)
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (hpoints : Function.Injective points)
    (a : ι → ℝ) (ha : a ≠ 0) :
    0 < p4Q2NR_originalTemporalExactGram b points a := by
  have hWitness : ∃ i : ι, a i ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    funext i
    simpa using h i
  exact p4Q2OA_originalTemporalExactGram_strict_pos
    b hb points hpoints a hWitness

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OA_originalFinitePointSelector_self_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OA_originalFinitePointSelector_other_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OA_originalFiniteSignedEvaluation_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OA_originalFiniteSignedEvaluation_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OA_originalFiniteSignedDouble_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OA_originalTemporalExactGram_eq_signedDouble
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OA_originalTemporalExactGram_strict_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2OA_originalTemporalExactGram_pos_of_coefficients_ne_zero
