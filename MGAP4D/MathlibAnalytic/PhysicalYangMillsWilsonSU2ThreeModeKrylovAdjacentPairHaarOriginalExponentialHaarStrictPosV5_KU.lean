import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2NonzeroHomogeneousEnergyV5_KT
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2FeatureExponentialBanachSeriesV5_KR
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-KU — strict positive-definiteness of the ACTUAL SU(2) Wilson
# exponential real-feature kernel for all nonzero continuous signed sources

KS/KL: true matrix-coordinate monomial Haar moments separate sources.
KN/KO/KP: the original degree-n homogeneous double-Haar energy is an
exact finite sum of squared coordinate moments (hence nonnegative).
KT: for each nonzero signed continuous source, some homogeneous energy
and a finite positive Wilson Taylor energy is STRICTLY positive.
KR: the exact original SU(2) matrix-feature Wilson exponential is the
uniform-norm Banach-algebra sum of its genuine positive-coefficient
Taylor terms.

We now define the bounded REAL Haar-pair integration functional on
the complete C(SU(2)×SU(2),ℝ) Banach space by the canonical product-Haar
L² inner product with the actual tensor-source ψ(g)ψ(h).
Its evaluation is the LITERAL Haar-pair integral. Fubini identifies
each power-kernel evaluation exactly with KP's homogeneous Haar energy.
The bounded functional carries KR's uniform Banach series to a genuine
HasSum of nonnegative real energy coefficients; KT gives one positive
term. Thus the FULL original SU(2) exponential feature-kernel
quadratic energy is STRICTLY positive for every nonzero continuous
source and any t>0.

Haar here is the original Wilson posterior's reference measure, not
a replacement posterior; no independent-Haar conditional law or
artificial rank/source frame is introduced. This SU(2) exponential
integral transform step does NOT YET identify the actual two-posterior
Gauss-law static spatial receiver, prove H1-C3, or establish the
continuum 4D Yang–Mills mass gap. No new axioms/sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "nu" => normalizedCompactHaar Gauge
local notation "nuPair" => Measure.prod (normalizedCompactHaar Gauge) (normalizedCompactHaar Gauge)
local notation "E" => p4Q2KR_originalSU2RealFeatureInnerContinuous
local notation "Energy" => p4Q2KP_originalSU2HomogeneousWilsonHaarEnergy
local notation "Exp" => p4Q2KR_originalSU2FeatureExponentialContinuous

/-- The real continuous pair source built from the SAME signed SU(2)
Haar-reference test ψ at both genuinely interacting coordinates. -/
noncomputable def p4Q2KU_originalSU2PairSourceContinuous
    (ψ : C(Gauge, ℝ)) : C(Gauge × Gauge, ℝ) := by
  refine ⟨(fun p => ψ p.1 * ψ p.2), ?_⟩
  exact (ψ.continuous.comp continuous_fst).mul
    (ψ.continuous.comp continuous_snd)

/-- The canonical original reference Haar-double integral is a
bounded linear functional on C(SU(2)×SU(2),ℝ). It uses the actual
product of the SAME normalized SU(2) Haar measures that occur
in the original interacting Wilson conditional posterior densities. -/
noncomputable def p4Q2KU_originalSU2PairHaarMomentCLM
    (ψ : C(Gauge, ℝ)) : C(Gauge × Gauge, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (ContinuousMap.toLp 2 nuPair ℝ
    (p4Q2KU_originalSU2PairSourceContinuous ψ))).comp
      (ContinuousMap.toLp 2 nuPair ℝ)

/-- Exact product-Haar integral formula for the bounded functional.
No conditional posterior measure is replaced: this is only the
underlying SU(2) Haar reference for the original Wilson fiber. -/
theorem p4Q2KU_originalSU2PairHaarMomentCLM_apply
    (ψ : C(Gauge, ℝ)) (F : C(Gauge × Gauge, ℝ)) :
    p4Q2KU_originalSU2PairHaarMomentCLM ψ F =
      ∫ p : Gauge × Gauge, F p * (ψ p.1 * ψ p.2) ∂nuPair := by
  change
    inner ℝ
      (ContinuousMap.toLp 2 nuPair ℝ
        (p4Q2KU_originalSU2PairSourceContinuous ψ))
      (ContinuousMap.toLp 2 nuPair ℝ F) = _
  simpa only [p4Q2KU_originalSU2PairSourceContinuous] using
    (ContinuousMap.inner_toLp nuPair
      (p4Q2KU_originalSU2PairSourceContinuous ψ) F)

/-- For every homogeneous degree, the pair-Haar bounded functional
of the ACTUAL continuous Wilson feature inner-power is EXACTLY KP's
true iterated Haar double-energy. This is finite Fubini, not a
formal unproved interchange of an infinite series. -/
theorem p4Q2KU_originalSU2PairHaarMomentCLM_homogeneous
    (ψ : C(Gauge, ℝ)) (n : ℕ) :
    p4Q2KU_originalSU2PairHaarMomentCLM ψ (E ^ n) =
      Energy ψ n := by
  let F : C(Gauge × Gauge, ℝ) := E ^ n
  have hCont : Continuous (fun p : Gauge × Gauge =>
      F p * (ψ p.1 * ψ p.2)) :=
    F.continuous.mul
      ((ψ.continuous.comp continuous_fst).mul
        (ψ.continuous.comp continuous_snd))
  have hInt :
      Integrable (fun p : Gauge × Gauge =>
        F p * (ψ p.1 * ψ p.2)) nuPair :=
    hCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [p4Q2KU_originalSU2PairHaarMomentCLM_apply]
  change (∫ p : Gauge × Gauge,
    F p * (ψ p.1 * ψ p.2) ∂nuPair) = Energy ψ n
  calc
    (∫ p : Gauge × Gauge,
        F p * (ψ p.1 * ψ p.2) ∂nuPair) =
      ∫ g : Gauge, ∫ h : Gauge,
        F (g,h) * (ψ g * ψ h) ∂nu ∂nu :=
      integral_prod _ hInt
    _ = ∫ g : Gauge, ∫ h : Gauge,
      ψ g * ψ h * (inner ℝ (Phi g) (Phi h)) ^ n ∂nu ∂nu := by
      apply integral_congr_ae
      filter_upwards with g
      apply integral_congr_ae
      filter_upwards with h
      change (E (g,h)) ^ n * (ψ g * ψ h) =
        ψ g * ψ h * (inner ℝ (Phi g) (Phi h)) ^ n
      rw [p4Q2KR_originalSU2RealFeatureInnerContinuous_apply]
      ring
    _ = Energy ψ n := rfl

/-- Exact evaluation of each ACTUAL Taylor term of the SU(2)
Wilson Banach exponential series against the genuine signed
Haar-pair source. No assumed positivity of the integral transform. -/
theorem p4Q2KU_originalSU2PairHaarMomentCLM_taylorTerm
    (ψ : C(Gauge, ℝ)) (t : ℝ) (n : ℕ) :
    p4Q2KU_originalSU2PairHaarMomentCLM ψ
      (((Nat.factorial n : ℝ)⁻¹) • ((t • E) ^ n)) =
    (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n := by
  have hPow : (t • E) ^ n = t ^ n • (E ^ n) := by
    ext p
    simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [mul_pow]
  calc
    p4Q2KU_originalSU2PairHaarMomentCLM ψ
        (((Nat.factorial n : ℝ)⁻¹) • ((t • E) ^ n)) =
      ((Nat.factorial n : ℝ)⁻¹) * (t ^ n * Energy ψ n) := by
      rw [hPow]
      simp only [map_smul, smul_eq_mul,
        p4Q2KU_originalSU2PairHaarMomentCLM_homogeneous]
    _ = (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n := by
      simp only [div_eq_mul_inv]
      ring

/-- Push KR's GENUINE uniform Banach-algebra Wilson exponential
series through the proved BOUNDED pair-Haar functional. The exact
full exponential Wilson Haar energy is the HasSum of the original
positive-coefficient homogeneous energies. This is the previously
missing justified Taylor/integral interchange. -/
theorem p4Q2KU_originalSU2PairHaarMomentCLM_exp_hasSum
    (ψ : C(Gauge, ℝ)) (t : ℝ) :
    HasSum
      (fun n : ℕ =>
        (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n)
      (p4Q2KU_originalSU2PairHaarMomentCLM ψ (Exp t)) := by
  have hSeries :
      HasSum
        (fun n : ℕ =>
          p4Q2KU_originalSU2PairHaarMomentCLM ψ
            (((Nat.factorial n : ℝ)⁻¹) • ((t • E) ^ n)))
        (p4Q2KU_originalSU2PairHaarMomentCLM ψ (Exp t)) :=
    (p4Q2KR_originalSU2FeatureExpBanachSeries_hasSum t).mapL
      (p4Q2KU_originalSU2PairHaarMomentCLM ψ)
  convert hSeries using 1
  funext n
  exact (p4Q2KU_originalSU2PairHaarMomentCLM_taylorTerm ψ t n).symm

/-- The FULL original SU(2) real Wilson exponential feature-kernel
has STRICTLY positive Haar quadratic form against every nonzero
continuous signed source, at EVERY positive t. All individual
homogeneous terms are nonnegative and KT proves one strictly
positive term. Thus no cancellation survives the original
uniform Banach-series limit. -/
theorem p4Q2KU_originalSU2WilsonExponentialHaarQuadratic_pos
    (ψ : C(Gauge, ℝ)) (hψ : ψ ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    0 < p4Q2KU_originalSU2PairHaarMomentCLM ψ (Exp t) := by
  obtain ⟨n, hn⟩ :=
    p4Q2KT_originalSU2_exists_positive_homogeneousWilsonEnergy ψ hψ
  have hCoeff : 0 < t ^ n / (Nat.factorial n : ℝ) :=
    div_pos (pow_pos ht n) (by positivity)
  have hTerm :
      0 < (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n :=
    mul_pos hCoeff hn
  have hLimit :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range N,
            (t ^ k / (Nat.factorial k : ℝ)) * Energy ψ k)
        Filter.atTop
        (nhds (p4Q2KU_originalSU2PairHaarMomentCLM ψ (Exp t))) :=
    (p4Q2KU_originalSU2PairHaarMomentCLM_exp_hasSum ψ t).tendsto_sum_nat
  have hEventually :
      ∀ᶠ N : ℕ in Filter.atTop,
        (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n ≤
          ∑ k ∈ Finset.range N,
            (t ^ k / (Nat.factorial k : ℝ)) * Energy ψ k := by
    filter_upwards [Filter.eventually_ge_atTop (n + 1)] with N hN
    exact Finset.single_le_sum
      (f := fun k : ℕ =>
        (t ^ k / (Nat.factorial k : ℝ)) * Energy ψ k)
      (s := Finset.range N)
      (fun k hk =>
        p4Q2KT_originalSU2_positiveWilsonTaylorEnergyTerm_nonneg ψ t ht.le k)
      (Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self n) hN))
  have hLower :
      (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n ≤
        p4Q2KU_originalSU2PairHaarMomentCLM ψ (Exp t) :=
    ge_of_tendsto hLimit hEventually
  exact lt_of_lt_of_le hTerm hLower

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KU_originalSU2PairHaarMomentCLM_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KU_originalSU2PairHaarMomentCLM_homogeneous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KU_originalSU2PairHaarMomentCLM_taylorTerm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KU_originalSU2PairHaarMomentCLM_exp_hasSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KU_originalSU2WilsonExponentialHaarQuadratic_pos
