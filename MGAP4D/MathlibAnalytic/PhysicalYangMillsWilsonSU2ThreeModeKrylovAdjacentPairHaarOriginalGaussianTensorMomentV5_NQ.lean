import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianStoneWeierstrassV5_NO
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureFiniteGram
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPositiveSemidefinite
import Mathlib.Tactic

/-!
# P4-Q2-NQ — exact original SU(2) Wilson power Gram and genuine Hilbert tensor moments

This leaf applies the EXISTING real Hilbert-Schmidt SU(2) feature and the
existing completed-tensor Hilbert kernel construction to the ORIGINAL
normalized temporal Wilson character χ(x⁻¹g).

For every finite family of actual SU(2) points and arbitrary real signed
coefficients:
  Q_n = Σ_ij a_i a_j χ(x_i⁻¹x_j)^n
      = ‖Σ_i a_i feature_n(x_i)‖² ≥ 0.
Consequently Q_n=0 iff the degree-n completed Hilbert tensor moment vanishes.
The original finite Taylor Gram is also ≥0 at every nonnegative coupling,
and these exact finite Gram energies converge to the actual exponential
temporal Wilson Gram.

This is an unconditional, arbitrary-finite-index analytic foundation. It
does NOT assert arbitrary-n STRICT Gram positivity or all-degree moment
vanishing from a ZERO exact Gaussian energy, or fixed-beta section-span
density. Those are separate mathematical goals.

Two genuine posterior laws, Gauss-law physical source, Perron half-density,
and the original spatial Wilson interactions are not changed. No assumed
rank/injectivity/continuum gap, Dobrushin, sorry, admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2NQ_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

namespace GroundStatePosteriorJoint
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "chi" => p4Q2NG_originalSU2TemporalCharacter
local notation "k" => p4Q2NJ_originalSU2WilsonTemporalSection

/-- Identification of the true original Wilson SU(2) character with the
PREEXISTING normalized SU2 trace kernel, requiring no new kernel model. -/
theorem p4Q2NQ_originalSU2TemporalCharacter_eq_normalizedTrace
    (x g : Gauge) :
    chi x g = specialUnitaryNormalizedTraceRelativeKernel 2 x g := by
  rw [p4Q2NG_originalSU2TemporalCharacter_eq_trace,
    specialUnitaryNormalizedTraceRelativeKernel_eq_scaled]
  unfold specialUnitaryRealTraceRelativeKernel
  norm_num

/-- Canonical, preexisting normalized SU(2) trace Hilbert feature transported
along the just-proved equality with the ORIGINAL temporal character. -/
noncomputable def p4Q2NQ_originalSU2TemporalCharacterHilbertFeature :
    RealHilbertKernelFeature Gauge chi := by
  have hk : chi = specialUnitaryNormalizedTraceRelativeKernel 2 := by
    funext x g
    exact p4Q2NQ_originalSU2TemporalCharacter_eq_normalizedTrace x g
  rw [hk]
  exact specialUnitaryNormalizedTraceRelativeKernelFeature 2 (by norm_num)

/-- The EXACT finite degree-n original SU(2) character Gram quadratic form
equals the squared norm of the genuinely constructed nth completed-tensor
Hilbert feature moment. All points and signed weights are arbitrary. -/
theorem p4Q2NQ_originalTemporalPowerGram_eq_tensorMoment_inner
    (n : ℕ)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (coefficients : ι → ℝ) :
    (∑ i : ι, ∑ j : ι,
      coefficients i * coefficients j *
        (chi (points i) (points j)) ^ n) =
      inner ℝ
        (∑ i : ι, coefficients i •
          ((p4Q2NQ_originalSU2TemporalCharacterHilbertFeature.pow n).feature
            (points i)))
        (∑ i : ι, coefficients i •
          ((p4Q2NQ_originalSU2TemporalCharacterHilbertFeature.pow n).feature
            (points i))) := by
  exact (p4Q2NQ_originalSU2TemporalCharacterHilbertFeature.pow n).finiteGram_eq_inner
    points coefficients

/-- Every genuine SU(2) character power yields a nonnegative Gram energy,
for all degrees, all finite point families and arbitrary real signs. -/
theorem p4Q2NQ_originalTemporalPowerGram_nonneg
    (n : ℕ)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (coefficients : ι → ℝ) :
    0 ≤ ∑ i : ι, ∑ j : ι,
      coefficients i * coefficients j *
        (chi (points i) (points j)) ^ n :=
  (p4Q2NQ_originalSU2TemporalCharacterHilbertFeature.pow n).positiveSemidefinite
    ι points coefficients

/-- No algebraic signed cancellation within a fixed power Hilbert feature:
vanishing of its original Gram energy is EQUIVALENT to vanishing of its
degree-n finite signed Hilbert tensor moment. -/
theorem p4Q2NQ_originalTemporalPowerGram_zero_iff_tensorMoment_zero
    (n : ℕ)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (coefficients : ι → ℝ) :
    (∑ i : ι, ∑ j : ι,
      coefficients i * coefficients j *
        (chi (points i) (points j)) ^ n) = 0 ↔
      (∑ i : ι, coefficients i •
        ((p4Q2NQ_originalSU2TemporalCharacterHilbertFeature.pow n).feature
          (points i))) = 0 := by
  rw [p4Q2NQ_originalTemporalPowerGram_eq_tensorMoment_inner]
  exact inner_self_eq_zero

/-- Every truncation of the ORIGINAL SU(2) temporal Wilson exponential has
a concrete nonnegative finite Gram quadratic form for b≥0. -/
theorem p4Q2NQ_originalTemporalTaylorFiniteGram_nonneg
    (b : ℝ) (hb : 0 ≤ b) (degree : ℕ)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (coefficients : ι → ℝ) :
    0 ≤ ∑ i : ι, ∑ j : ι,
      coefficients i * coefficients j *
        RealHilbertKernelFeature.exponentialPartialKernel chi b degree
          (points i) (points j) :=
  (p4Q2NQ_originalSU2TemporalCharacterHilbertFeature.exponentialPartial
    b hb degree).positiveSemidefinite ι points coefficients

/-- The finite-dimensional genuine Wilson temporal Taylor Gram energies
converge to the EXACT original exponential section Gram energy.
The proof takes the already-formalized Hilbert Taylor pointwise limit
through both finite signed-index sums, with no positivity hypothesis. -/
theorem p4Q2NQ_originalTemporalTaylorFiniteGram_tendsto
    (b : ℝ)
    {ι : Type} [Fintype ι]
    (points : ι → Gauge) (coefficients : ι → ℝ) :
    Tendsto
      (fun degree =>
        ∑ i : ι, ∑ j : ι,
          coefficients i * coefficients j *
            RealHilbertKernelFeature.exponentialPartialKernel chi b degree
              (points i) (points j))
      atTop
      (𝓝 (∑ i : ι, ∑ j : ι,
        coefficients i * coefficients j * k b (points i) (points j))) := by
  classical
  have hTerm (p : ι × ι) :
      Tendsto
        (fun degree =>
          coefficients p.1 * coefficients p.2 *
            RealHilbertKernelFeature.exponentialPartialKernel chi b degree
              (points p.1) (points p.2))
        atTop
        (𝓝 (coefficients p.1 * coefficients p.2 *
          k b (points p.1) (points p.2))) := by
    change Tendsto
      (fun degree =>
        coefficients p.1 * coefficients p.2 *
          RealHilbertKernelFeature.exponentialPartialKernel chi b degree
            (points p.1) (points p.2))
      atTop
      (𝓝 (coefficients p.1 * coefficients p.2 *
        Real.exp (b * chi (points p.1) (points p.2))))
    exact tendsto_const_nhds.mul
      (RealHilbertKernelFeature.exponentialPartialKernel_tendsto
        chi b (points p.1) (points p.2))
  have hSum :=
    tendsto_fintype_sum_real
      (fun degree (p : ι × ι) =>
        coefficients p.1 * coefficients p.2 *
          RealHilbertKernelFeature.exponentialPartialKernel chi b degree
            (points p.1) (points p.2))
      (fun p : ι × ι =>
        coefficients p.1 * coefficients p.2 *
          k b (points p.1) (points p.2))
      hTerm
  simpa only [Fintype.sum_prod_type] using hSum

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NQ_originalSU2TemporalCharacter_eq_normalizedTrace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NQ_originalTemporalPowerGram_eq_tensorMoment_inner
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NQ_originalTemporalPowerGram_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NQ_originalTemporalPowerGram_zero_iff_tensorMoment_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NQ_originalTemporalTaylorFiniteGram_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2NQ_originalTemporalTaylorFiniteGram_tendsto
