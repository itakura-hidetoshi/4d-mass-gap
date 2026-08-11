import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalTraceFockWitness
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureKernelMomentNonzero
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceKernelFeature
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureMeasurability
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators InnerProduct InnerProductSpace

noncomputable section

private theorem boundaryMarginalTraceFockFeatureTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance boundaryMarginalTraceFockFeatureTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance boundaryMarginalTraceFockFeatureCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance boundaryMarginalTraceFockFeatureSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance boundaryMarginalTraceFockFeatureMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance boundaryMarginalTraceFockFeatureBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

/-- The normalized relative-trace kernel of the canonical primary spatial
plaquette, pulled back to the actual reflection-fixed boundary configuration. -/
def periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel
    (H : ℕ)
    (b₁ b₂ : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) : ℝ :=
  specialUnitaryNormalizedTraceRelativeKernel 2
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b₁)
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b₂)

/-- The actual boundary relative-trace kernel has the concrete finite-dimensional
real Hilbert feature obtained by pulling back the defining `SU(2)` trace feature. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernelFeature
    (H : ℕ) :
    RealHilbertKernelFeature
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel H) := by
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel] using
    (specialUnitaryNormalizedTraceRelativeKernelFeature
      2 boundaryMarginalTraceFockFeatureTwoRankPositive).comap
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2)

/-- Canonical boundary basepoint whose primary plaquette holonomy is the identity. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteTraceKernelBasepoint
    (H : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 :=
  periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomySection H 1

/-- At the identity-holonomy basepoint, the relative-trace kernel section is
exactly the normalized primary-plaquette trace `r = 1 - E_W`. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel_basepoint
    (H : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel H
        (periodicHypercubicEvenPrimarySpatialPlaquetteTraceKernelBasepoint H) b =
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H b := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteTraceKernelBasepoint
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy_section]
  simp only [specialUnitaryNormalizedTraceRelativeKernel, inv_one, one_mul]
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous_apply
      H b).symm

/-- The normalized relative-trace kernel is jointly continuous on `SU(2)`. -/
theorem continuous_specialUnitaryNormalizedTraceRelativeKernel_two :
    Continuous fun p :
      Matrix.specialUnitaryGroup (Fin 2) ℂ ×
        Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      specialUnitaryNormalizedTraceRelativeKernel 2 p.1 p.2 := by
  have hTrace : Continuous fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      normalizedSpecialUnitaryRealTrace 2 U := by
    have hEnergy : Continuous fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
        (1 : ℝ) - specialUnitaryWilsonPlaquetteEnergy 2 U :=
      continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
    convert hEnergy using 1
    funext U
    rw [specialUnitaryWilsonPlaquetteEnergy_eq]
    ring
  exact hTrace.comp ((continuous_fst.inv).mul continuous_snd)

/-- Hence the actual primary-plaquette relative-trace boundary kernel is jointly
continuous. -/
theorem
    continuous_periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel
    (H : ℕ) :
    Continuous fun p :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel H
        p.1 p.2 := by
  have hhol : Continuous
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2) :=
    continuous_periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy_two H
  change Continuous fun p =>
    specialUnitaryNormalizedTraceRelativeKernel 2
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 p.1)
      (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 p.2)
  exact continuous_specialUnitaryNormalizedTraceRelativeKernel_two.comp
    ((hhol.comp continuous_fst).prodMk (hhol.comp continuous_snd))

/-- The actual boundary relative-trace kernel has unit diagonal. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel_self
    (H : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2) :
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel H b b = 1 := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel
  unfold specialUnitaryNormalizedTraceRelativeKernel
  rw [show
    (periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b)⁻¹ *
        periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryCyclicHolonomy H 2 b =
      (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) by group]
  exact normalizedSpecialUnitaryRealTrace_one 2
    boundaryMarginalTraceFockFeatureTwoRankPositive

/-- The centered normalized-trace polynomial attached to a finite coefficient
vector, kept as a continuous map so that its `L²` representative and its
Lebesgue integral are definitionally tied to the same function. -/
noncomputable def periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial
    (H k : ℕ)
    (c : Fin (k + 1) → ℝ) :
    C(PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2, ℝ) :=
  ∑ j : Fin (k + 1), c j •
    (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
      (j : ℕ))

/-- Every polynomial-weighted degree-`n` tensor trace feature is Bochner
integrable in the actual interacting boundary marginal.  Compactness gives a
sup-norm bound for the scalar polynomial, while the tensor-power feature has
unit norm because the relative-trace kernel has unit diagonal. -/
theorem
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_powFeature_integrable
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (n : ℕ) :
    Integrable
      (fun b =>
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
          ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernelFeature
            H).pow n).feature b)
      (periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta) := by
  let C :=
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernelFeature H
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta
  have hKernelPow : Continuous fun q :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 ×
        PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2 =>
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel H
          q.1 q.2 ^ n :=
    (continuous_periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel
      H).pow n
  have hFeature : Continuous (C.pow n).feature := by
    exact RealHilbertKernelFeature.continuous_feature_of_continuous_kernel
      (C.pow n) hKernelPow
  have hWeighted : Continuous fun b => p b • (C.pow n).feature b :=
    p.continuous.smul hFeature
  have hFeatureNorm : ∀ b, ‖(C.pow n).feature b‖ = 1 := by
    intro b
    apply RealHilbertKernelFeature.feature_norm_eq_one
    intro x
    rw [periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel_self]
    simp
  refine Integrable.of_bound hWeighted.aestronglyMeasurable ‖p‖ ?_
  filter_upwards [] with b
  rw [norm_smul, hFeatureNorm]
  simpa using p.norm_coe_le_norm b

/-- A nonzero `L²` pairing with the degree-`n` normalized trace power is exactly
a nonzero scalar kernel moment at the identity-holonomy basepoint, and hence
forces the actual degree-`n` tensor-feature Bochner moment to be nonzero. -/
theorem
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_powFeature_integral_ne_zero_of_inner_ne_zero
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (n : ℕ)
    (hmoment :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^ n))
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c)) ≠ 0) :
    (∫ b,
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
        ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernelFeature
          H).pow n).feature b
      ∂(periodicHypercubicEvenBoundaryMarginalMeasure
        H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta)) ≠ 0 := by
  let C :=
    periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernelFeature H
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  let μ := periodicHypercubicEvenBoundaryMarginalMeasure
    H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta
  have hInnerEq :
      inner ℝ
        (ContinuousMap.toLp (E := ℝ) 2 μ ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^ n))
        (ContinuousMap.toLp (E := ℝ) 2 μ ℝ p) =
      ∫ b, p b *
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H b ^ n
        ∂μ := by
    simpa using MeasureTheory.ContinuousMap.inner_toLp μ
      (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^ n) p
  have hTraceMoment :
      (∫ b, p b *
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H b ^ n
        ∂μ) ≠ 0 := by
    intro hz
    apply hmoment
    simpa [μ, p] using hInnerEq.trans hz
  have hKernelMoment :
      (∫ b, p b *
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel H
          (periodicHypercubicEvenPrimarySpatialPlaquetteTraceKernelBasepoint H) b ^ n
        ∂μ) ≠ 0 := by
    simpa only [
      periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernel_basepoint]
      using hTraceMoment
  have hIntegrable : Integrable (fun b => p b • (C.pow n).feature b) μ := by
    simpa [C, p, μ] using
      periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_powFeature_integrable
        H beta hbeta k c n
  have hNonzero :=
    C.pow_integral_ne_zero_of_kernel_pow_moment_ne_zero
      μ (fun b => p b) n hIntegrable
      (periodicHypercubicEvenPrimarySpatialPlaquetteTraceKernelBasepoint H)
      hKernelMoment
  simpa [C, p, μ] using hNonzero

/-- Actual positive-coupling Fock strictness.  Every centered nonzero finite
normalized-trace polynomial has a strictly positive tensor degree whose
Bochner feature moment is nonzero, and the positive Taylor coefficient
`beta^i / i!` cannot annihilate that component under the canonical square-root
Fock scaling. -/
theorem
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_exists_positiveTaylorDegree_powFeatureMoment_ne_zero
    (H : ℕ)
    (beta : ℝ) (hbeta : 0 < beta)
    (k : ℕ)
    (c : Fin (k + 1) → ℝ) (hc : c ≠ 0)
    (hzero :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (0 : ℕ)))
        (∑ j : Fin (k + 1), c j •
          ContinuousMap.toLp
            (E := ℝ) 2
            (periodicHypercubicEvenBoundaryMarginalMeasure
              H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta.le) ℝ
            (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
              (j : ℕ))) = 0) :
    ∃ i : Fin (k + 1),
      0 < (i : ℕ) ∧
      0 < beta ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ) ∧
      (∫ b,
        periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
          ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernelFeature
            H).pow (i : ℕ)).feature b
        ∂(periodicHypercubicEvenBoundaryMarginalMeasure
          H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta.le)) ≠ 0 ∧
      Real.sqrt (beta ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ)) •
        (∫ b,
          periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c b •
            ((periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceRelativeBoundaryKernelFeature
              H).pow (i : ℕ)).feature b
          ∂(periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta.le)) ≠ 0 := by
  rcases
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePower_exists_positiveTaylorDegree
      H beta hbeta k c hc hzero with ⟨i, hi, hcoefficient, hmoment⟩
  let p := periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial H k c
  have hmoment' :
      inner ℝ
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta.le) ℝ
          (periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTraceTwoBoundaryContinuous H ^
            (i : ℕ)))
        (ContinuousMap.toLp
          (E := ℝ) 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H 2 boundaryMarginalTraceFockFeatureTwoRankPositive beta hbeta.le) ℝ p) ≠ 0 := by
    simpa [p, periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePolynomial] using hmoment
  have hFeatureMoment :=
    periodicHypercubicEvenBoundaryMarginalPrimarySpatialPlaquetteNormalizedTracePolynomial_powFeature_integral_ne_zero_of_inner_ne_zero
      H beta hbeta.le k c (i : ℕ) hmoment'
  refine ⟨i, hi, hcoefficient, hFeatureMoment, ?_⟩
  exact RealHilbertKernelFeature.sqrt_smul_ne_zero_of_pos
    (beta ^ (i : ℕ) / (Nat.factorial (i : ℕ) : ℝ)) hcoefficient _ hFeatureMoment

end

end MathlibAnalytic
end MGAP4D