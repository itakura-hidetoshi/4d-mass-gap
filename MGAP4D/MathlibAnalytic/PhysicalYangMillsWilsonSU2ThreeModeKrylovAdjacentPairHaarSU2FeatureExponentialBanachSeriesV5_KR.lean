import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSU2HomogeneousWilsonHaarMomentGramV5_KP
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-KR — the ORIGINAL SU(2) real Wilson feature exponential has an
# exact globally convergent Banach-algebra Taylor series on SU(2) × SU(2)

KP, KN and KO established the finite-degree positive-Haar Gram formulas.
To bridge them to the actual Wilson exponential kernel WITHOUT assuming
a Taylor/integral interchange, we use the fixed pinned mathlib's
NORMED BANACH-ALGEBRA exponential series directly in the complete
uniform-norm algebra C(SU(2) × SU(2), R).

The actual SU(2) finite realification-feature inner product
  k(g,h) = <Phi(g), Phi(h)>
is bundled as a continuous real map on SU(2) × SU(2), using the exact
physical Wilson plaquette-energy identity (KH), whose continuity is
already theorem-proved. The actual exponential is then
  exp (t * k(g,h)).
With no restriction on t, the power series
  Σ_n (n!)^{-1} (t*k)^n
sums to the ORIGINAL exponential kernel uniformly, as convergence
in the SUP NORM of C(SU(2)×SU(2),R).

This is a genuinely analytic, all-degree uniform Taylor passage.
The interchange of its sum with the original Haar double integration,
the strict quadratic form and GI detector injectivity are separate
follow-up theorems, not assumed here.

No independent-Haar posterior replacement, new axiom/sorry/admit,
artificial physical frame/rank hypothesis, H1-C3, or continuum gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KR_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KR_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KR_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KR_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KR_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section SU2
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Phi" => specialUnitaryMatrixRealFeature 2
local notation "E" => p4Q2KR_originalSU2RealFeatureInnerContinuous

/-- The exact original SU(2) matrix-realification feature inner-product
kernel is a genuine continuous function on the compact PRODUCT group.
This is proved through the true continuous Wilson plaquette energy,
not an assumed continuous synthetic feature. -/
noncomputable def p4Q2KR_originalSU2RealFeatureInnerContinuous :
    C(Gauge × Gauge, ℝ) := by
  refine ⟨(fun p => inner ℝ (Phi p.1) (Phi p.2)), ?_⟩
  have hEnergy : Continuous (fun p : Gauge × Gauge =>
      specialUnitaryWilsonPlaquetteEnergy 2 (p.1⁻¹ * p.2)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy 2).comp
      ((continuous_fst.inv).mul continuous_snd)
  have hExpr : Continuous (fun p : Gauge × Gauge =>
      (2 : ℝ) * (1 -
        specialUnitaryWilsonPlaquetteEnergy 2 (p.1⁻¹ * p.2))) :=
    continuous_const.mul (continuous_const.sub hEnergy)
  have hEq :
      (fun p : Gauge × Gauge => inner ℝ (Phi p.1) (Phi p.2)) =
      (fun p : Gauge × Gauge =>
        (2 : ℝ) * (1 -
          specialUnitaryWilsonPlaquetteEnergy 2 (p.1⁻¹ * p.2))) := by
    funext p
    have h := p4Q2KH_originalSU2WilsonEnergy_eq_realFeatureInner p.1 p.2
    linarith
  rw [hEq]
  exact hExpr

/-- Its evaluation is literally the same true SU(2) real matrix inner
product used in KG/KH/KJ/KN/KP, without renormalization. -/
@[simp] theorem p4Q2KR_originalSU2RealFeatureInnerContinuous_apply
    (g h : Gauge) :
    p4Q2KR_originalSU2RealFeatureInnerContinuous (g,h) =
      inner ℝ (Phi g) (Phi h) := by
  rfl

/-- The Wilson real-feature exponential, constructed directly by the
Banach algebra exponential of a continuous real physical kernel. -/
noncomputable def p4Q2KR_originalSU2FeatureExponentialContinuous
    (t : ℝ) : C(Gauge × Gauge, ℝ) :=
  NormedSpace.exp (t • E)

/-- The Banach-algebra exponential EVALUATES to the original real
exponential of the physical SU(2) matrix inner product at every
physical right/left insertion pair. -/
theorem p4Q2KR_originalSU2FeatureExponentialContinuous_apply
    (t : ℝ) (g h : Gauge) :
    p4Q2KR_originalSU2FeatureExponentialContinuous t (g,h) =
      Real.exp (t * inner ℝ (Phi g) (Phi h)) := by
  unfold p4Q2KR_originalSU2FeatureExponentialContinuous
  rw [NormedSpace.exp_continuousMap_eq]
  change NormedSpace.exp (t * E (g,h)) =
    Real.exp (t * inner ℝ (Phi g) (Phi h))
  rw [p4Q2KR_originalSU2RealFeatureInnerContinuous_apply]
  rw [Real.exp_eq_exp_ℝ]

/-- The exact finite real-feature Wilson exponential Taylor polynomial
in the complete SUP-NORM algebra of continuous SU(2) pair functions.
All coefficients are actual inverse factorials, not guessed weights. -/
noncomputable def p4Q2KR_originalSU2FeatureExpTaylorPartial
    (t : ℝ) (n : ℕ) : C(Gauge × Gauge, ℝ) :=
  ∑ k ∈ Finset.range n,
    ((Nat.factorial k : ℝ)⁻¹) • ((t • E) ^ k)

/-- The FIXED mathlib Banach exponential series sums in the genuine
complete uniform-norm algebra C(SU(2)×SU(2),R). This proves
UNIFORM convergence of all original Wilson homogeneous powers,
for all real t with no small-coupling approximation. -/
theorem p4Q2KR_originalSU2FeatureExpBanachSeries_hasSum
    (t : ℝ) :
    HasSum
      (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹) • ((t • E) ^ n))
      (p4Q2KR_originalSU2FeatureExponentialContinuous t) := by
  change HasSum
    (fun n : ℕ => ((Nat.factorial n : ℝ)⁻¹) •
      ((t • E) ^ n)) (NormedSpace.exp (t • E))
  exact NormedSpace.exp_series_hasSum_exp'
    (𝕂 := ℝ) (t • E)

/-- Uniform convergence of the original finite Taylor polynomials
to the exact SU(2) Wilson exponential kernel.  Convergence is in the
C(SU(2)×SU(2),R) norm, i.e. the supremum norm on this compact domain,
NOT merely pointwise convergence or a finite-H proxy. -/
theorem p4Q2KR_originalSU2FeatureExpTaylorPartial_tendsto_uniform
    (t : ℝ) :
    Filter.Tendsto (fun n => p4Q2KR_originalSU2FeatureExpTaylorPartial t n)
      Filter.atTop
      (nhds (p4Q2KR_originalSU2FeatureExponentialContinuous t)) := by
  change Filter.Tendsto
    (fun n => ∑ k ∈ Finset.range n,
      ((Nat.factorial k : ℝ)⁻¹) • ((t • E) ^ k))
    Filter.atTop
    (nhds (p4Q2KR_originalSU2FeatureExponentialContinuous t))
  exact (p4Q2KR_originalSU2FeatureExpBanachSeries_hasSum t).tendsto_sum_nat

end SU2
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KR_originalSU2RealFeatureInnerContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KR_originalSU2FeatureExponentialContinuous_apply
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KR_originalSU2FeatureExpBanachSeries_hasSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KR_originalSU2FeatureExpTaylorPartial_tendsto_uniform
