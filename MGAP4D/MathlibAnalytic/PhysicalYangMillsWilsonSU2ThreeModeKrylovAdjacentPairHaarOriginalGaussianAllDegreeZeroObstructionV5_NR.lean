import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianTensorMomentV5_NQ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianPSDSignedPolynomialV5_NP
import Mathlib.Tactic

/-!
# P4-Q2-NR — authentic SU2 Wilson Gaussian zero-Gram ⇒ all Hilbert tensor moments zero

NQ already proves the degree-n genuine temporal SU2 Wilson character Gram
equals the squared norm of the EXISTING completed Hilbert tensor feature
moment, and proves all finite Taylor Gram forms converge to the EXACT
original Wilson exponential temporal kernel at every real b.

NR formalizes the key NONCANCELLATION bridge for every finite family of
ACTUAL SU2 holonomies and signed real coefficients:

  Q_exact = lim_N Σ_(n≤N) (b^n / n!) Q_n,
  Q_n ≥ 0,  (b>0) ⇒
  Q_exact = 0 ⇒ Q_n=0 for ALL n ⇒ each true degree-n tensor moment = 0.

The proof uses finite-sum interchange, strictly positive coefficients,
Finset.single_le_sum, ge_of_tendsto and NQ's genuine Hilbert power features.
It does not assume a finite-rank detector, moment injectivity, density or
a synthetic Gaussian measure. No new axioms, sorry, admit or Dobrushin.

This does NOT yet establish arbitrary-finite strict positivity, polynomial
moment completeness for ALL continuous signed measures, section-span density,
authentic signed receiver variance, physical GI lower bound, H1-C3 or the
continuum mass gap. Original interacting posteriors, Gauss-law source,
Perron half-density and spatial Wilson factors are unchanged.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

namespace GroundStatePosteriorJoint
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "chi" => p4Q2NG_originalSU2TemporalCharacter
local notation "k" => p4Q2NJ_originalSU2WilsonTemporalSection

noncomputable def p4Q2NR_originalTemporalPowerGram
    {ι : Type*} [Fintype ι]
    (n : ℕ) (points : ι → Gauge) (a : ι → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι,
    a i * a j * (chi (points i) (points j)) ^ n

noncomputable def p4Q2NR_originalTemporalTaylorGram
    {ι : Type*} [Fintype ι]
    (b : ℝ) (degree : ℕ) (points : ι → Gauge) (a : ι → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι,
    a i * a j *
      RealHilbertKernelFeature.exponentialPartialKernel chi b degree
        (points i) (points j)

noncomputable def p4Q2NR_originalTemporalExactGram
    {ι : Type*} [Fintype ι]
    (b : ℝ) (points : ι → Gauge) (a : ι → ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι,
    a i * a j * k b (points i) (points j)

/-- Interchange arbitrary finite signed Gram sums with arbitrary finite
Taylor degree sums. All sums are finite; no integration interchange
or additional convergence assumption enters. -/
private theorem p4Q2NR_finiteGram_degree_sum_comm
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (w : ℕ → ℝ) (κ : ℕ → ι → ι → ℝ)
    (s : Finset ℕ) :
    (∑ i : ι, ∑ j : ι,
      a i * a j * (∑ n ∈ s, w n * κ n i j)) =
        ∑ n ∈ s, w n *
          (∑ i : ι, ∑ j : ι, a i * a j * κ n i j) := by
  classical
  calc
    _ = ∑ i : ι, ∑ j : ι, ∑ n ∈ s,
          w n * (a i * a j * κ n i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = ∑ i : ι, ∑ n ∈ s, ∑ j : ι,
          w n * (a i * a j * κ n i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ n ∈ s, ∑ i : ι, ∑ j : ι,
          w n * (a i * a j * κ n i j) := by
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- At every finite cutoff, the EXACT original temporal SU2 Wilson
signed Gram Taylor approximation is the finite positive-weight sum of
its degree-n true Hilbert tensor Gram energies. -/
theorem p4Q2NR_originalTemporalTaylorGram_eq_powerSum
    (b : ℝ) (degree : ℕ)
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ) :
    p4Q2NR_originalTemporalTaylorGram b degree points a =
      ∑ n ∈ Finset.range (degree + 1),
        (b ^ n / (n.factorial : ℝ)) *
          p4Q2NR_originalTemporalPowerGram n points a := by
  classical
  have hPoint (x g : Gauge) :
      RealHilbertKernelFeature.exponentialPartialKernel chi b degree x g =
        ∑ n ∈ Finset.range (degree + 1),
          (b ^ n / (n.factorial : ℝ)) * (chi x g) ^ n := by
    rw [RealHilbertKernelFeature.exponentialPartialKernel_eq_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [mul_pow]
    ring
  unfold p4Q2NR_originalTemporalTaylorGram p4Q2NR_originalTemporalPowerGram
  simp_rw [hPoint]
  exact p4Q2NR_finiteGram_degree_sum_comm
    a (fun n => b ^ n / (n.factorial : ℝ))
    (fun n i j => (chi (points i) (points j)) ^ n)
    (Finset.range (degree + 1))

/-- Mathlib order convergence: a convergent sequence of finite sums
of NONNEGATIVE terms cannot converge to zero unless every term is zero.
The index n is kept fixed while finite cutoffs tend to infinity. -/
private theorem p4Q2NR_nonnegative_series_each_zero
    (term : ℕ → ℝ)
    (hNonneg : ∀ n, 0 ≤ term n)
    (hLimit :
      Tendsto (fun degree => ∑ n ∈ Finset.range (degree + 1), term n)
        atTop (𝓝 (0 : ℝ))) :
    ∀ n, term n = 0 := by
  intro n
  have hEventually : ∀ᶠ degree : ℕ in atTop,
      term n ≤ ∑ m ∈ Finset.range (degree + 1), term m := by
    filter_upwards [Filter.eventually_ge_atTop n] with degree hd
    apply Finset.single_le_sum (fun m _ => hNonneg m)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hLe : term n ≤ 0 := ge_of_tendsto hLimit hEventually
  exact le_antisymm hLe (hNonneg n)

/-- Fundamental NR bridge: if the EXACT original positive-coupling
Wilson temporal Gaussian Gram vanishes for any finite REAL signed
SU2 points, EVERY nonnegative Hilbert tensor power Gram vanishes.
No all-mode density or measure injectivity is assumed. -/
theorem p4Q2NR_originalTemporalExactGram_zero_forces_allPowerGrams_zero
    (b : ℝ) (hb : 0 < b)
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ)
    (hZero : p4Q2NR_originalTemporalExactGram b points a = 0) :
    ∀ n : ℕ, p4Q2NR_originalTemporalPowerGram n points a = 0 := by
  have hTaylor :
      Tendsto
        (fun degree => p4Q2NR_originalTemporalTaylorGram b degree points a)
        atTop
        (𝓝 (p4Q2NR_originalTemporalExactGram b points a)) :=
    p4Q2NQ_originalTemporalTaylorFiniteGram_tendsto b points a
  let term : ℕ → ℝ := fun n =>
    (b ^ n / (n.factorial : ℝ)) *
      p4Q2NR_originalTemporalPowerGram n points a
  have hTermNonneg : ∀ n, 0 ≤ term n := by
    intro n
    exact mul_nonneg
      (p4Q2NL_originalWilsonTemporalTaylorCoefficient_pos b hb n).le
      (p4Q2NQ_originalTemporalPowerGram_nonneg n points a)
  have hSeries :
      Tendsto (fun degree => ∑ n ∈ Finset.range (degree + 1), term n)
        atTop (𝓝 (0 : ℝ)) := by
    simpa only [term, ← p4Q2NR_originalTemporalTaylorGram_eq_powerSum, hZero]
      using hTaylor
  have hEachZero := p4Q2NR_nonnegative_series_each_zero term
    hTermNonneg hSeries
  intro n
  have hMulZero := hEachZero n
  exact (mul_eq_zero.mp hMulZero).resolve_left
    (p4Q2NL_originalWilsonTemporalTaylorCoefficient_pos b hb n).ne'

/-- Original Gaussian zero energy forces the zero vector in EACH of
the existing completed Hilbert tensor powers, for all natural degrees.
Finite signed families of genuine SU2 points, with no rank premise. -/
theorem p4Q2NR_originalTemporalExactGram_zero_forces_allTensorMoments_zero
    (b : ℝ) (hb : 0 < b)
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ)
    (hZero : p4Q2NR_originalTemporalExactGram b points a = 0) :
    ∀ n : ℕ,
      (∑ i : ι, a i •
        ((p4Q2NQ_originalSU2TemporalCharacterHilbertFeature.pow n).feature
          (points i))) = 0 := by
  intro n
  exact (p4Q2NQ_originalTemporalPowerGram_zero_iff_tensorMoment_zero
    n points a).mp
      (p4Q2NR_originalTemporalExactGram_zero_forces_allPowerGrams_zero
        b hb points a hZero n)

/-- Strict positivity of the actual finite Gaussian Gram follows whenever
ONE TRUE degree-n Hilbert tensor moment is nonzero; no cancellation across
different Fock degrees is possible at positive coupling. This is a
conditional finite-family statement, NOT a claimed nonzero moment
hypothesis for every physical signed configuration. -/
theorem p4Q2NR_originalTemporalExactGram_pos_of_tensorMoment_witness
    (b : ℝ) (hb : 0 < b)
    {ι : Type*} [Fintype ι]
    (points : ι → Gauge) (a : ι → ℝ)
    (hWitness : ∃ n : ℕ,
      (∑ i : ι, a i •
        ((p4Q2NQ_originalSU2TemporalCharacterHilbertFeature.pow n).feature
          (points i))) ≠ 0) :
    0 < p4Q2NR_originalTemporalExactGram b points a := by
  have hNonneg : 0 ≤ p4Q2NR_originalTemporalExactGram b points a :=
    p4Q2NP_originalSU2WilsonTemporal_allFiniteGram_nonneg b hb.le points a
  have hNe : p4Q2NR_originalTemporalExactGram b points a ≠ 0 := by
    intro hZero
    obtain ⟨n, hn⟩ := hWitness
    exact hn
      (p4Q2NR_originalTemporalExactGram_zero_forces_allTensorMoments_zero
        b hb points a hZero n)
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NR_originalTemporalTaylorGram_eq_powerSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NR_originalTemporalExactGram_zero_forces_allPowerGrams_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NR_originalTemporalExactGram_zero_forces_allTensorMoments_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NR_originalTemporalExactGram_pos_of_tensorMoment_witness
