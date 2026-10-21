import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianAllDegreeZeroObstructionV5_NR
import Mathlib.Tactic

/-!
# P4-Q2-NS — quantitative all-degree lower bounds for genuine temporal Wilson Gaussian Gram

NR established all-order Hilbert tensor moment noncancellation from zero exact
original SU2 Wilson Gaussian Gram energy. NS strengthens its scalar content:

  Q_original(b) >= (b^n/n!) * Q_tensorPower(n)   for every n, b>0.

All finite point families are actual SU(2), all coefficients are arbitrary
real signed weights. The proof is a positive single Taylor term bounded by
the complete nonnegative partial sum, then passage to the EXACT original
Wilson kernel using existing NQ convergence and mathlib order closedness.

In particular the true n=0 and n=1 moments obey explicit lower bounds.
This supplies a FINITE-VOLUME Fock-mode coercivity estimate WITHOUT any
invented rank hypothesis, posterior, physical source or detector.

It does NOT imply a UNIFORM volume lower bound, all-n strict Gram positivity,
density of the original fixed-beta section linear span, or H1-C3.
Two original interacting Wilson posteriors, Gauss-law physical source,
Perron half-density and spatial interactions remain unchanged.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section

local instance p4Q2NS_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

namespace GroundStatePosteriorJoint

local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "chi" => p4Q2NG_originalSU2TemporalCharacter

/-- A single nonnegative Taylor tensor mode gives an explicit LOWER
BOUND on the EXACT original SU2 Wilson temporal Gaussian quadratic form,
uniform in the truncation cutoff but not in lattice volume. -/
theorem p4Q2NS_originalTemporalExactGram_ge_weightedTensorPower
    (b : ℝ) (hb : 0 < b) (n : ℕ)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ) :
    (b ^ n / (n.factorial : ℝ)) *
      p4Q2NR_originalTemporalPowerGram n points a ≤
        p4Q2NR_originalTemporalExactGram b points a := by
  have hLimit :
      Tendsto
        (fun degree => p4Q2NR_originalTemporalTaylorGram b degree points a)
        atTop (𝓝 (p4Q2NR_originalTemporalExactGram b points a)) :=
    p4Q2NQ_originalTemporalTaylorFiniteGram_tendsto b points a
  have hEventually : ∀ᶠ degree : ℕ in atTop,
      (b ^ n / (n.factorial : ℝ)) *
          p4Q2NR_originalTemporalPowerGram n points a ≤
        p4Q2NR_originalTemporalTaylorGram b degree points a := by
    filter_upwards [Filter.eventually_ge_atTop n] with degree hn
    rw [p4Q2NR_originalTemporalTaylorGram_eq_powerSum]
    apply Finset.single_le_sum
      (fun m _ =>
        mul_nonneg
          (p4Q2NL_originalWilsonTemporalTaylorCoefficient_pos b hb m).le
          (p4Q2NQ_originalTemporalPowerGram_nonneg m points a))
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  exact ge_of_tendsto hLimit hEventually

/-- Degree zero: the EXACT genuine Wilson temporal Gaussian quadratic
form bounds the original signed mass-square Gram without additional
moment conditions. -/
theorem p4Q2NS_originalTemporalExactGram_ge_degreeZero
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ) :
    (∑ i : ι, ∑ j : ι, a i * a j) ≤
      p4Q2NR_originalTemporalExactGram b points a := by
  simpa [p4Q2NR_originalTemporalPowerGram] using
    (p4Q2NS_originalTemporalExactGram_ge_weightedTensorPower
      b hb 0 points a)

/-- Degree one: an explicit genuine normalized SU2 character Gram
lower bound survives the exact original exponential, with coefficient b. -/
theorem p4Q2NS_originalTemporalExactGram_ge_degreeOne
    (b : ℝ) (hb : 0 < b)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ) :
    b * (∑ i : ι, ∑ j : ι,
      a i * a j * chi (points i) (points j)) ≤
        p4Q2NR_originalTemporalExactGram b points a := by
  simpa [p4Q2NR_originalTemporalPowerGram] using
    (p4Q2NS_originalTemporalExactGram_ge_weightedTensorPower
      b hb 1 points a)

/-- One positive actual tensor Gram degree suffices to produce strict
original Gaussian finite signed energy, now with a QUANTITATIVE
positive lower bound rather than the zero-cancellation contradiction. -/
theorem p4Q2NS_originalTemporalExactGram_pos_of_powerGram_pos
    (b : ℝ) (hb : 0 < b) (n : ℕ)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ)
    (hpos : 0 < p4Q2NR_originalTemporalPowerGram n points a) :
    0 < p4Q2NR_originalTemporalExactGram b points a :=
  lt_of_lt_of_le
    (mul_pos (p4Q2NL_originalWilsonTemporalTaylorCoefficient_pos b hb n) hpos)
    (p4Q2NS_originalTemporalExactGram_ge_weightedTensorPower b hb n points a)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NS_originalTemporalExactGram_ge_weightedTensorPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NS_originalTemporalExactGram_ge_degreeZero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NS_originalTemporalExactGram_ge_degreeOne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NS_originalTemporalExactGram_pos_of_powerGram_pos
