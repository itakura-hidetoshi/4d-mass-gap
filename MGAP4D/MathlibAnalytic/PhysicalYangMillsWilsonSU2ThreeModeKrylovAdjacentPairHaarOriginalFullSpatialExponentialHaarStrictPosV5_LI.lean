import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullSpatialHaarMonomialCompletenessV5_LH
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2FeatureExponentialBanachSeriesV5_KR
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-LI — strict original FULL spatial SU(2) Wilson exponential Haar energy

LG proved ALL finite-degree original full-spatial Wilson feature
homogeneous energies are exactly sums of true spatial-coordinate
Haar moments squared (nonnegative). LH proved that EVERY NONZERO
continuous real signed spatial source has a strictly positive
homogeneous energy at SOME finite degree.

Here we assemble the SAME genuine full spatial feature exponential
and its Banach norm-convergent Taylor series directly in
C(Cfg_H × Cfg_H, ℝ). Its Haar pair integration is an ACTUAL bounded
continuous linear functional on the real Banach space, defined via
the original finite-volume spatial product Haar L² Riesz pairing.

We prove precise homogeneous evaluations, exact Taylor coefficient
identity and a rigorous HasSum through the bounded Haar-pair map.
The LH positive homogeneous witness plus nonnegativity of every
coefficient proves STRICT POSITIVITY of the full exponential Haar
quadratic energy for any nonzero continuous spatial signed source.

We also identify this exponential with the LITERAL, originally
defined full Wilson temporal crossing kernel, including ALL -β
per-link normalizations, and derive its strict full spatial Haar
quadratic positivity at each β > 0.

Important: Haar remains the true spatial Haar REFERENCE, not a
substitute for the actual interacting two-Wilson posterior laws.
Strict positivity here does not silently provide a uniform volume
lower bound, physical gauge normalization, a centered Wilson GI
two-context determinant, H1-C3 or a continuum YM mass gap.

No synthetic rank/source-frame, Dobrushin, new axiom, sorry/admit.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "FullPhi" => p4Q2LD_originalSpatialMatrixRealFeature H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "haarPair" => Measure.prod haar haar
local notation "Energy" => p4Q2LG_originalFullSpatialHomogeneousWilsonHaarEnergy H

/-- One exact, continuous, REAL original entire spatial Wilson
matrix-feature inner kernel. The finite sum traverses every
real physical spatial link and uses KR's actual SU(2) factor. -/
noncomputable def p4Q2LI_originalFullSpatialFeatureInnerContinuous :
    C(Cfg × Cfg, ℝ) :=
  ∑ e : Link,
    (p4Q2KR_originalSU2RealFeatureInnerContinuous).comp
      ⟨(fun p : Cfg × Cfg => (p.1 e, p.2 e)), by fun_prop⟩

/-- Its evaluation is the original full finite-volume real matrix
Hilbert-Schmidt feature pairing from the merged LF proof. -/
@[simp] theorem p4Q2LI_originalFullSpatialFeatureInnerContinuous_apply
    (A B : Cfg) :
    p4Q2LI_originalFullSpatialFeatureInnerContinuous H (A,B) =
      inner ℝ (FullPhi A) (FullPhi B) := by
  calc
    p4Q2LI_originalFullSpatialFeatureInnerContinuous H (A,B) =
      ∑ e : Link, inner ℝ (Phi (A e)) (Phi (B e)) := by
        simp [p4Q2LI_originalFullSpatialFeatureInnerContinuous,
          p4Q2KR_originalSU2RealFeatureInnerContinuous_apply]
    _ = inner ℝ (FullPhi A) (FullPhi B) :=
      (p4Q2LF_originalSpatialFeatureInner_eq_linkSum H A B).symm

local notation "E" => p4Q2LI_originalFullSpatialFeatureInnerContinuous H

/-- Exact full spatial physical feature exponential in the BANACH
algebra of real continuous functions on original Cfg_H × Cfg_H. -/
noncomputable def p4Q2LI_originalFullSpatialFeatureExpContinuous
    (t : ℝ) : C(Cfg × Cfg, ℝ) :=
  NormedSpace.exp (t • E)

local notation "Exp" => p4Q2LI_originalFullSpatialFeatureExpContinuous H

theorem p4Q2LI_originalFullSpatialFeatureExpContinuous_apply
    (t : ℝ) (A B : Cfg) :
    Exp t (A,B) = Real.exp (t * inner ℝ (FullPhi A) (FullPhi B)) := by
  unfold p4Q2LI_originalFullSpatialFeatureExpContinuous
  rw [NormedSpace.exp_continuousMap_eq]
  change NormedSpace.exp (t * E (A,B)) =
    Real.exp (t * inner ℝ (FullPhi A) (FullPhi B))
  rw [p4Q2LI_originalFullSpatialFeatureInnerContinuous_apply]
  rw [Real.exp_eq_exp_ℝ]

/-- All true finite-volume Wilson homogeneous Taylor terms have
their original inverse factorial coefficients, with norm-convergent
series in the full spatial continuous pair-function Banach space. -/
theorem p4Q2LI_originalFullSpatialFeatureExpBanachSeries_hasSum
    (t : ℝ) :
    HasSum
      (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹) • ((t • E) ^ n))
      (Exp t) := by
  change HasSum
    (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹) •
      ((t • E) ^ n)) (NormedSpace.exp (t • E))
  exact NormedSpace.exp_series_hasSum_exp'
    (𝕂 := ℝ) (t • E)

/-- The authentic signed spatial source at BOTH real Haar-pair
coordinates (no new interaction measure or assumed source rank). -/
noncomputable def p4Q2LI_originalFullSpatialPairSourceContinuous
    (ψ : C(Cfg, ℝ)) : C(Cfg × Cfg, ℝ) := by
  refine ⟨(fun p => ψ p.1 * ψ p.2), ?_⟩
  exact (ψ.continuous.comp continuous_fst).mul
    (ψ.continuous.comp continuous_snd)

/-- The bounded ORIGINAL full-spatial Haar-pair integration
functional, constructed on real C(Cfg_H × Cfg_H) from canonical
Haar-pair L² inner product. -/
noncomputable def p4Q2LI_originalFullSpatialPairHaarMomentCLM
    (ψ : C(Cfg, ℝ)) : C(Cfg × Cfg, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (ContinuousMap.toLp 2 haarPair ℝ
    (p4Q2LI_originalFullSpatialPairSourceContinuous H ψ))).comp
      (ContinuousMap.toLp 2 haarPair ℝ)

/-- The LITERAL original spatial Haar-pair integral formula for
this bounded linear map. Both coordinate measures are the true
spatial product Haar reference of the original Wilson slab. -/
theorem p4Q2LI_originalFullSpatialPairHaarMomentCLM_apply
    (ψ : C(Cfg, ℝ)) (F : C(Cfg × Cfg, ℝ)) :
    p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ F =
      ∫ p : Cfg × Cfg, F p * (ψ p.1 * ψ p.2) ∂haarPair := by
  change
    inner ℝ
      (ContinuousMap.toLp 2 haarPair ℝ
        (p4Q2LI_originalFullSpatialPairSourceContinuous H ψ))
      (ContinuousMap.toLp 2 haarPair ℝ F) = _
  simpa only [p4Q2LI_originalFullSpatialPairSourceContinuous] using
    (ContinuousMap.inner_toLp haarPair
      (p4Q2LI_originalFullSpatialPairSourceContinuous H ψ) F)

/-- The evaluation of the ACTUAL nth feature inner-power is exactly
LG's full-spatial original Wilson homogeneous double-Haar energy,
not an unverified Taylor/integral interchange. -/
theorem p4Q2LI_originalFullSpatialPairHaarMomentCLM_homogeneous
    (ψ : C(Cfg, ℝ)) (n : ℕ) :
    p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ (E ^ n) =
      Energy ψ n := by
  let F : C(Cfg × Cfg, ℝ) := E ^ n
  have hCont : Continuous (fun p : Cfg × Cfg =>
      F p * (ψ p.1 * ψ p.2)) :=
    F.continuous.mul
      ((ψ.continuous.comp continuous_fst).mul
        (ψ.continuous.comp continuous_snd))
  have hInt : Integrable (fun p : Cfg × Cfg =>
      F p * (ψ p.1 * ψ p.2)) haarPair :=
    hCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [p4Q2LI_originalFullSpatialPairHaarMomentCLM_apply]
  change (∫ p : Cfg × Cfg,
    F p * (ψ p.1 * ψ p.2) ∂haarPair) = Energy ψ n
  calc
    (∫ p : Cfg × Cfg,
        F p * (ψ p.1 * ψ p.2) ∂haarPair) =
      ∫ A : Cfg, ∫ B : Cfg,
        F (A,B) * (ψ A * ψ B) ∂haar ∂haar :=
      integral_prod _ hInt
    _ = ∫ A : Cfg, ∫ B : Cfg,
      ψ A * ψ B * (inner ℝ (FullPhi A) (FullPhi B)) ^ n ∂haar ∂haar := by
      apply integral_congr_ae
      filter_upwards with A
      apply integral_congr_ae
      filter_upwards with B
      change (E (A,B)) ^ n * (ψ A * ψ B) =
        ψ A * ψ B * (inner ℝ (FullPhi A) (FullPhi B)) ^ n
      rw [p4Q2LI_originalFullSpatialFeatureInnerContinuous_apply]
      ring
    _ = Energy ψ n := rfl

/-- Exact original nth Taylor term after applying the TRUE bounded
full-spatial Haar pair moment functional. -/
theorem p4Q2LI_originalFullSpatialPairHaarMomentCLM_taylorTerm
    (ψ : C(Cfg, ℝ)) (t : ℝ) (n : ℕ) :
    p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ
      (((Nat.factorial n : ℝ)⁻¹) • ((t • E) ^ n)) =
      (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n := by
  have hPow : (t • E) ^ n = t ^ n • (E ^ n) := by
    ext p
    simp only [ContinuousMap.pow_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [mul_pow]
  calc
    p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ
        (((Nat.factorial n : ℝ)⁻¹) • ((t • E) ^ n)) =
      ((Nat.factorial n : ℝ)⁻¹) * (t ^ n * Energy ψ n) := by
        rw [hPow]
        simp only [map_smul, smul_eq_mul,
          p4Q2LI_originalFullSpatialPairHaarMomentCLM_homogeneous]
    _ = (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n := by
      simp only [div_eq_mul_inv]
      ring

/-- Pass the original Banach-algebra Wilson exponential series
through its provably bounded original full-spatial Haar-pair
integration functional, preserving the complete Taylor HasSum. -/
theorem p4Q2LI_originalFullSpatialPairHaarMomentCLM_exp_hasSum
    (ψ : C(Cfg, ℝ)) (t : ℝ) :
    HasSum
      (fun n : ℕ =>
        (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n)
      (p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ (Exp t)) := by
  have hSeries :
      HasSum
        (fun n : ℕ =>
          p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ
            (((Nat.factorial n : ℝ)⁻¹) • ((t • E) ^ n)))
        (p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ (Exp t)) :=
    (p4Q2LI_originalFullSpatialFeatureExpBanachSeries_hasSum H t).mapL
      (p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ)
  convert hSeries using 1
  funext n
  exact (p4Q2LI_originalFullSpatialPairHaarMomentCLM_taylorTerm H ψ t n).symm

/-- Strict positive-definiteness of the EXACT full-spatial Wilson
matrix-realification exponential kernel, for EVERY nonzero signed
continuous spatial source ψ and EVERY positive coupling parameter. -/
theorem p4Q2LI_originalFullSpatialFeatureExpHaarQuadratic_pos
    (ψ : C(Cfg, ℝ)) (hψ : ψ ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    0 < p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ (Exp t) := by
  obtain ⟨n, hn⟩ :=
    p4Q2LH_originalFullSpatialHaar_exists_positive_homogeneousWilsonEnergy
      H ψ hψ
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
        (nhds (p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ (Exp t))) :=
    (p4Q2LI_originalFullSpatialPairHaarMomentCLM_exp_hasSum H ψ t).tendsto_sum_nat
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
        p4Q2LG_originalFullSpatialPositiveWilsonTaylorEnergyTerm_nonneg
          H ψ t ht.le k)
      (Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self n) hN))
  have hLower :
      (t ^ n / (Nat.factorial n : ℝ)) * Energy ψ n ≤
        p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ (Exp t) :=
    ge_of_tendsto hLimit hEventually
  exact lt_of_lt_of_le hTerm hLower

/-- TRUE complete spatial SU(2) temporal crossing Wilson kernel,
as a continuous pair function with its exact physical per-link
Boltzmann normalization (no invented kernel). -/
noncomputable def p4Q2LI_originalSpatialWilsonCrossingContinuous
    (b : ℝ) : C(Cfg × Cfg, ℝ) :=
  Real.exp (-b *
    ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ)) •
    Exp (b / 2)

@[simp] theorem p4Q2LI_originalSpatialWilsonCrossingContinuous_apply
    (b : ℝ) (A B : Cfg) :
    p4Q2LI_originalSpatialWilsonCrossingContinuous H b (A,B) =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 b A B := by
  change Real.exp (-b *
      ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ)) *
      Exp (b / 2) (A,B) = _
  rw [p4Q2LI_originalFullSpatialFeatureExpContinuous_apply,
    p4Q2LF_originalSpatialWilsonCrossing_eq_fullFeatureExponential]
  rw [← Real.exp_add]

/-- An ACTUAL finite-volume spatial Wilson temporal crossing kernel
has a STRICTLY positive Haar quadratic energy against any nonzero
real continuous signed spatial test source, at every beta>0. -/
theorem p4Q2LI_originalSpatialWilsonCrossingHaarQuadratic_pos
    (ψ : C(Cfg, ℝ)) (hψ : ψ ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    0 < p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ
      (p4Q2LI_originalSpatialWilsonCrossingContinuous H b) := by
  change 0 < p4Q2LI_originalFullSpatialPairHaarMomentCLM H ψ
    (Real.exp (-b *
      ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ)) •
      Exp (b / 2))
  rw [map_smul]
  simp only [smul_eq_mul]
  exact mul_pos (Real.exp_pos _)
    (p4Q2LI_originalFullSpatialFeatureExpHaarQuadratic_pos
      H ψ hψ (b / 2) (by linarith))

/-- Integral form: strict positive Haar DOUBLE integral of the
ORIGINAL genuine all-link Wilson crossing kernel (the same
spatial measure as the one-slab Wilson transfer), for every
nonzero continuous real spatial source at every beta>0. -/
theorem p4Q2LI_originalSpatialWilsonCrossingHaarDoubleIntegral_pos
    (ψ : C(Cfg, ℝ)) (hψ : ψ ≠ 0)
    (b : ℝ) (hb : 0 < b) :
    0 < (∫ A : Cfg, ∫ B : Cfg,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel
        H 2 b A B * (ψ A * ψ B) ∂haar ∂haar) := by
  let F : C(Cfg × Cfg, ℝ) :=
    p4Q2LI_originalSpatialWilsonCrossingContinuous H b
  have hCont : Continuous (fun p : Cfg × Cfg =>
      F p * (ψ p.1 * ψ p.2)) :=
    F.continuous.mul
      ((ψ.continuous.comp continuous_fst).mul
        (ψ.continuous.comp continuous_snd))
  have hInt : Integrable (fun p : Cfg × Cfg =>
      F p * (ψ p.1 * ψ p.2)) haarPair :=
    hCont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPos :=
    p4Q2LI_originalSpatialWilsonCrossingHaarQuadratic_pos H ψ hψ b hb
  rw [p4Q2LI_originalFullSpatialPairHaarMomentCLM_apply] at hPos
  rw [integral_prod _ hInt] at hPos
  -- Unfold the local alias explicitly: simp only does not delta-reduce
  -- the named F while rewriting the original Wilson kernel integrand.
  change
    0 < (∫ A : Cfg, ∫ B : Cfg,
      p4Q2LI_originalSpatialWilsonCrossingContinuous H b (A,B) *
        (ψ A * ψ B) ∂haar ∂haar) at hPos
  simpa only [p4Q2LI_originalSpatialWilsonCrossingContinuous_apply] using hPos

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalFullSpatialFeatureInnerContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalFullSpatialFeatureExpContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalFullSpatialFeatureExpBanachSeries_hasSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalFullSpatialPairHaarMomentCLM_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalFullSpatialPairHaarMomentCLM_homogeneous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalFullSpatialPairHaarMomentCLM_taylorTerm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalFullSpatialPairHaarMomentCLM_exp_hasSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalFullSpatialFeatureExpHaarQuadratic_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalSpatialWilsonCrossingContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalSpatialWilsonCrossingHaarQuadratic_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LI_originalSpatialWilsonCrossingHaarDoubleIntegral_pos
