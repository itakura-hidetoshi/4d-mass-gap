import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedSharedPlaquetteOscillationBound
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHeatBathDensityBalance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

namespace HaarNormalizedExponentialRatio

/-- Real normalized exponential density with respect to a base measure. -/
def density
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f : α → ℝ)
    (x : α) : ℝ :=
  Real.exp (f x) / ∫ y, Real.exp (f y) ∂μ

/-- Oscillation control of two log weights gives the pointwise mutual
likelihood-ratio factor after normalization, without a second normalization
loss. -/
theorem mutual_le_exp_mul_of_difference_oscillation
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (f g : α → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) μ)
    (hg : Integrable (fun x => Real.exp (g x)) μ)
    (R : ℝ)
    (hOsc : ∀ x y : α,
      (f x - g x) - (f y - g y) ≤ R)
    (x : α) :
    density μ f x ≤ Real.exp R * density μ g x ∧
      density μ g x ≤ Real.exp R * density μ f x := by
  have hZf : 0 < ∫ y, Real.exp (f y) ∂μ := integral_exp_pos hf
  have hZg : 0 < ∫ y, Real.exp (g y) ∂μ := integral_exp_pos hg
  constructor
  · unfold density
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
  · unfold density
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

end HaarNormalizedExponentialRatio

/-- A pointwise oscillation radius for one-link Gibbs exponents gives the same
exponential mutual likelihood-ratio factor for exact normalized Haar
conditional densities. -/
theorem continuous_compact_oriented_singleLinkConditionalDensityReal_mutual_le
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
    C.singleLinkConditionalDensityReal A target u ≤
        Real.exp R * C.singleLinkConditionalDensityReal B target u ∧
      C.singleLinkConditionalDensityReal B target u ≤
        Real.exp R * C.singleLinkConditionalDensityReal A target u := by
  simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensityReal,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction,
    HaarNormalizedExponentialRatio.density] using
    HaarNormalizedExponentialRatio.mutual_le_exp_mul_of_difference_oscillation
      (normalizedCompactHaar C.base.Gauge)
      (fun g => C.base.gibbsExponent (C.base.replaceLink A target g))
      (fun g => C.base.gibbsExponent (C.base.replaceLink B target g))
      (continuous_compact_oriented_singleLinkBoltzmannIntegrable C A target)
      (continuous_compact_oriented_singleLinkBoltzmannIntegrable C B target)
      R hOsc u

/-- Short name for the continuous compact-oriented canonical `SU(N)` Wilson
system used in the conditional-density theorem. -/
abbrev specialUnitaryContinuousCompactOrientedDensityRatioSystem
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    ContinuousCompactOrientedGaugeWilsonSystem :=
  specialUnitaryContinuousCompactOrientedGaugeWilsonSystem
    geometry N hN beta beta_nonneg

/-- Canonical non-Abelian `SU(N)` one-link Haar conditional densities obey the
explicit pointwise factor `exp (4 * beta * sharedPlaquetteCard)`. -/
theorem specialUnitaryContinuousCompactOriented_singleLinkConditionalDensityReal_mutual_le
    (geometry : FiniteOrientedFourDimensionalPlaquetteGeometry)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta)
    (A B : (specialUnitaryContinuousCompactOrientedDensityRatioSystem
      geometry N hN beta beta_nonneg).base.Configuration)
    (target source : geometry.Edge)
    (hAgree : (specialUnitaryContinuousCompactOrientedDensityRatioSystem
      geometry N hN beta beta_nonneg).base.AgreeOffLink A B source)
    (u : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let C := specialUnitaryContinuousCompactOrientedDensityRatioSystem
      geometry N hN beta beta_nonneg
    let R := beta * (4 * ((C.base.sharedPlaquettes target source).card : ℝ))
    C.singleLinkConditionalDensityReal A target u ≤
        Real.exp R * C.singleLinkConditionalDensityReal B target u ∧
      C.singleLinkConditionalDensityReal B target u ≤
        Real.exp R * C.singleLinkConditionalDensityReal A target u := by
  dsimp only
  let C := specialUnitaryContinuousCompactOrientedDensityRatioSystem
    geometry N hN beta beta_nonneg
  let R := beta * (4 * ((C.base.sharedPlaquettes target source).card : ℝ))
  apply continuous_compact_oriented_singleLinkConditionalDensityReal_mutual_le
    C A B target R
  intro x y
  have hAbs :=
    specialUnitaryCompactOriented_gibbsExponent_sourceResponse_oscillation_abs_le
      geometry N hN beta beta_nonneg A B target source x y hAgree
  exact le_trans (le_abs_self _) (by simpa [C, R] using hAbs)

end

end MathlibAnalytic
end MGAP4D
