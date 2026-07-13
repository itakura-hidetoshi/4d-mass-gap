import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedSharedPlaquetteOscillationBound
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkConditional
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Real normalized exponential density with respect to a base measure. -/
def normalizedExponentialDensity
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f : α → ℝ)
    (x : α) : ℝ :=
  Real.exp (f x) / ∫ y, Real.exp (f y) ∂μ

/-- Oscillation control of two log weights gives the sharp pointwise mutual
likelihood-ratio factor after normalization.  No second normalization factor is
lost: the partition-function comparison is obtained by integrating the same
cross-multiplied pointwise exponential inequality. -/
theorem normalizedExponentialDensity_mutual_le_exp_mul_of_difference_oscillation
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g : α → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) μ)
    (hg : Integrable (fun x => Real.exp (g x)) μ)
    (R : ℝ)
    (hOsc : ∀ x y : α,
      (f x - g x) - (f y - g y) ≤ R)
    (x : α) :
    normalizedExponentialDensity μ f x ≤
        Real.exp R * normalizedExponentialDensity μ g x ∧
      normalizedExponentialDensity μ g x ≤
        Real.exp R * normalizedExponentialDensity μ f x := by
  have hZf : 0 < ∫ y, Real.exp (f y) ∂μ := integral_exp_pos hf
  have hZg : 0 < ∫ y, Real.exp (g y) ∂μ := integral_exp_pos hg
  constructor
  · unfold normalizedExponentialDensity
    rw [show Real.exp R *
        (Real.exp (g x) / ∫ y, Real.exp (g y) ∂μ) =
      (Real.exp R * Real.exp (g x)) /
        ∫ y, Real.exp (g y) ∂μ by ring]
    apply (div_le_div_iff₀ hZf hZg).2
    have hPoint : ∀ y : α,
        Real.exp (f x) * Real.exp (g y) ≤
          (Real.exp R * Real.exp (g x)) * Real.exp (f y) := by
      intro y
      calc
        Real.exp (f x) * Real.exp (g y) =
            Real.exp (f x + g y) := by rw [Real.exp_add]
        _ ≤ Real.exp (R + g x + f y) := by
          exact Real.exp_le_exp.mpr (by linarith [hOsc x y])
        _ = (Real.exp R * Real.exp (g x)) * Real.exp (f y) := by
          rw [Real.exp_add, Real.exp_add]
    have hInt :
        (∫ y, Real.exp (f x) * Real.exp (g y) ∂μ) ≤
          ∫ y, (Real.exp R * Real.exp (g x)) * Real.exp (f y) ∂μ := by
      exact integral_mono_ae
        (hg.const_mul (Real.exp (f x)))
        (hf.const_mul (Real.exp R * Real.exp (g x)))
        (Filter.Eventually.of_forall hPoint)
    simpa using hInt
  · unfold normalizedExponentialDensity
    rw [show Real.exp R *
        (Real.exp (f x) / ∫ y, Real.exp (f y) ∂μ) =
      (Real.exp R * Real.exp (f x)) /
        ∫ y, Real.exp (f y) ∂μ by ring]
    apply (div_le_div_iff₀ hZg hZf).2
    have hPoint : ∀ y : α,
        Real.exp (g x) * Real.exp (f y) ≤
          (Real.exp R * Real.exp (f x)) * Real.exp (g y) := by
      intro y
      calc
        Real.exp (g x) * Real.exp (f y) =
            Real.exp (g x + f y) := by rw [Real.exp_add]
        _ ≤ Real.exp (R + f x + g y) := by
          exact Real.exp_le_exp.mpr (by linarith [hOsc y x])
        _ = (Real.exp R * Real.exp (f x)) * Real.exp (g y) := by
          rw [Real.exp_add, Real.exp_add]
    have hInt :
        (∫ y, Real.exp (g x) * Real.exp (f y) ∂μ) ≤
          ∫ y, (Real.exp R * Real.exp (f x)) * Real.exp (g y) ∂μ := by
      exact integral_mono_ae
        (hf.const_mul (Real.exp (g x)))
        (hg.const_mul (Real.exp R * Real.exp (f x)))
        (Filter.Eventually.of_forall hPoint)
    simpa using hInt

/-- Real density of the exact compact-Haar one-link conditional law. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  C.singleLinkBoltzmannFactor A target g /
    C.singleLinkPartitionFunction A target

/-- A pointwise oscillation radius for the one-link Gibbs exponents gives the
same exponential mutual likelihood-ratio factor for the exact normalized Haar
conditional densities. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_mutual_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (R : ℝ)
    (hOsc : ∀ u v : C.base.Gauge,
      (C.base.gibbsExponent (C.base.replaceLink A target u) -
        C.base.gibbsExponent (C.base.replaceLink B target u)) -
      (C.base.gibbsExponent (C.base.replaceLink A target v) -
        C.base.gibbsExponent (C.base.replaceLink B target v)) ≤ R)
    (u : C.base.Gauge) :
    C.singleLinkConditionalDensity A target u ≤
        Real.exp R * C.singleLinkConditionalDensity B target u ∧
      C.singleLinkConditionalDensity B target u ≤
        Real.exp R * C.singleLinkConditionalDensity A target u := by
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction,
    normalizedExponentialDensity] using
    normalizedExponentialDensity_mutual_le_exp_mul_of_difference_oscillation
      (normalizedCompactHaar C.base.Gauge)
      (fun g => C.base.gibbsExponent (C.base.replaceLink A target g))
      (fun g => C.base.gibbsExponent (C.base.replaceLink B target g))
      (continuous_compact_oriented_singleLinkBoltzmannIntegrable C A target)
      (continuous_compact_oriented_singleLinkBoltzmannIntegrable C B target)
      R hOsc u

/-- Short name for the continuous compact-oriented canonical `SU(N)` Wilson
system used in the conditional-density theorem. -/
abbrev specialUnitaryContinuousCompactOrientedDensitySystem
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactOrientedGaugeWilsonSystem :=
  specialUnitaryContinuousCompactOrientedGaugeWilsonSystem
    geometry N hN beta beta_nonneg

/-- For the canonical non-Abelian `SU(N)` Wilson conditional laws, changing one
source-link background gives the explicit pointwise likelihood-ratio factor
`exp (4 * beta * sharedPlaquetteCard)`. -/
theorem specialUnitaryContinuousCompactOriented_singleLinkConditionalDensity_mutual_le
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (A B : (specialUnitaryContinuousCompactOrientedDensitySystem
      geometry N hN beta beta_nonneg).base.Configuration)
    (target source : geometry.Edge)
    (hAgree : (specialUnitaryContinuousCompactOrientedDensitySystem
      geometry N hN beta beta_nonneg).base.AgreeOffLink A B source)
    (u : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let C := specialUnitaryContinuousCompactOrientedDensitySystem
      geometry N hN beta beta_nonneg
    let R := beta *
      (4 * ((C.base.sharedPlaquettes target source).card : ℝ))
    C.singleLinkConditionalDensity A target u ≤
        Real.exp R * C.singleLinkConditionalDensity B target u ∧
      C.singleLinkConditionalDensity B target u ≤
        Real.exp R * C.singleLinkConditionalDensity A target u := by
  dsimp only
  let C := specialUnitaryContinuousCompactOrientedDensitySystem
    geometry N hN beta beta_nonneg
  let R := beta *
    (4 * ((C.base.sharedPlaquettes target source).card : ℝ))
  apply continuous_compact_oriented_singleLinkConditionalDensity_mutual_le
    C A B target R
  intro x y
  have hAbs :=
    specialUnitaryCompactOriented_gibbsExponent_sourceResponse_oscillation_abs_le
      geometry N hN beta beta_nonneg A B target source x y hAgree
  exact le_trans (le_abs_self _) (by simpa [C, R] using hAbs)

end

end MathlibAnalytic
end MGAP4D
