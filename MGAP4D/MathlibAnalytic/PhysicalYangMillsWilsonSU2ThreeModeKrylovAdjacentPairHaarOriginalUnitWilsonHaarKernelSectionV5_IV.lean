import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineTransferUnitEigenmodeCriterionV5_IU
import MGAP4D.MathlibAnalytic.RealL2BoundedKernelIntegralRepresentation
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

/-!
# P4-Q2-IV: literal one-slab Wilson Haar kernel section and physical fine-unit eigenline

At arbitrary finite SU(2) spatial volume and nonnegative fine coupling β,
the ORIGINAL one-slab kernel is exactly
  Kβ(A,B) = hβ(A) Cβ(A,B) hβ(B)
with hβ the actual spatial-plaquette half-Boltzmann weight and Cβ the actual
temporal crossing Wilson kernel (symmetric and positive-semidefinite).

Define the LITERAL Haar fiber row integral
  Fβ(B) = ∫ A, Kβ(A,B) dHaar(A).
This file exposes its exact half-weight/crossing-kernel factorization and
proves it is jointly-continuous in the right spatial boundary, by genuine
Bochner integration in the continuous-function space C(Cfg,R).

The original physical one-slab transfer of the ACTUAL gauge-invariant
constant Haar-L² unit has the a.e. representative Fβ. Consequently the
normalized fine Wilson unit lies on the constant-unit eigenline exactly
when Fβ is pointwise constant (Haar full support and continuity).
Equivalently, noncollinearity of the actual first fine-right physical
Krylov source is precisely a TWO-ACTUAL-BOUNDARY witness
  ∃ B0 B1, Fβ(B0) ≠ Fβ(B1).

The existence of this pair at beta>0 is still a genuine OPEN analytic
problem in the current proof lane. No fake boundary sample, independent
Haar posterior, artificial source frame, Dobrushin, uniform H/scale/depth
coercivity, H1-C3, OS reconstruction or continuum Yang--Mills gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators Matrix

noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2IV_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2IV_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2IV_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2IV_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2IV_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
/- The normalized genuine compact-group Haar has full support. The finite
product measure inherits open-set positivity from this factor instance. -/
local instance p4Q2IV_SU2_normalizedHaarOpenPos :
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance

local instance p4Q2IV_haarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2IV_haarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint

theorem p4Q2IV_abstract_continuous_ae_constant_iff_pointwise_constant
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (haar : Measure X) [haar.IsOpenPosMeasure]
    (f : X → ℝ) (hf : Continuous f) (c : ℝ) :
    (f =ᵐ[haar] fun _ => c) ↔ ∀ x, f x = c := by
  constructor
  · intro hae x
    have heq : f = (fun _ : X => c) :=
      MeasureTheory.Measure.eq_of_ae_eq hae hf continuous_const
    exact congrFun heq x
  · intro h
    filter_upwards with x
    exact h x

section RawWilson

variable (H : ℕ) (beta : ℝ)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 beta
local notation "Half" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHalfWeight H 2 beta
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2 beta

/-- The original SU(2) Wilson Haar-integrated one-slab kernel on a
literal physical right boundary B, not a conditional-Haar surrogate. -/
noncomputable def p4Q2IV_originalWilsonUnitHaarKernelSection (B : Cfg) : ℝ :=
  ∫ A : Cfg, K A B ∂haar

/-- Exact original one-slab kernel factorization after integration in
the LEFT physical spatial configuration. The right half Boltzmann
weight stays OUTSIDE the Haar integral; the left weight stays INSIDE. -/
theorem p4Q2IV_originalWilsonUnitHaarKernelSection_factorization (B : Cfg) :
    p4Q2IV_originalWilsonUnitHaarKernelSection H beta B =
      Half B * ∫ A : Cfg, Half A * Cross A B ∂haar := by
  unfold p4Q2IV_originalWilsonUnitHaarKernelSection
  change (∫ A : Cfg, (Half A * Cross A B) * Half B ∂haar) =
    Half B * ∫ A : Cfg, Half A * Cross A B ∂haar
  rw [integral_mul_const]
  ring

/-- This exact original Wilson kernel row integral is strictly
positive at every physical right boundary and arbitrary beta. -/
theorem p4Q2IV_originalWilsonUnitHaarKernelSection_pos (B : Cfg) :
    0 < p4Q2IV_originalWilsonUnitHaarKernelSection H beta B := by
  unfold p4Q2IV_originalWilsonUnitHaarKernelSection
  exact p4Q2GVUnit_originalKernelIntegral_pos H beta B

/-- Joint compact-space continuity gives a real continuous-function
valued kernel section in the right boundary. Bochner integration of
that C(Cfg,R)-valued function yields a genuinely continuous Fβ. -/
theorem p4Q2IV_originalWilsonUnitHaarKernelSection_continuous :
    Continuous (p4Q2IV_originalWilsonUnitHaarKernelSection H beta) := by
  let g : C(Cfg × Cfg, ℝ) :=
    ⟨fun p => K p.1 p.2,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H 2 beta⟩
  let f : C(Cfg, C(Cfg, ℝ)) := g.curry
  have hfInt : Integrable (fun A : Cfg => f A) haar :=
    f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hEval (B : Cfg) :
      (∫ A : Cfg, f A ∂haar) B =
        p4Q2IV_originalWilsonUnitHaarKernelSection H beta B := by
    rw [ContinuousMap.integral_apply hfInt B]
    rfl
  have hEq :
      p4Q2IV_originalWilsonUnitHaarKernelSection H beta =
        (fun B : Cfg => (∫ A : Cfg, f A ∂haar) B) := by
    funext B
    exact (hEval B).symm
  rw [hEq]
  exact (∫ A : Cfg, f A ∂haar).continuous

end RawWilson

section ActualFine

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "haar" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure Hn 2
local notation "Unit" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "FineTransfer" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
local notation "RawFiber" =>
  p4Q2IV_originalWilsonUnitHaarKernelSection Hn (beta (n + 1))

/-- The TRUE unnormalized physical Wilson transfer of the original
constant Haar-L² source is represented Haar-a.e. by the literal raw
one-slab Wilson kernel integral Fβ(B). This is the missing physical
bridge between the fine Hilbert-space source and the pointwise kernel. -/
theorem p4Q2IV_originalFineWilsonPhysicalUnit_rawFiber_ae :
    (fun B : Cfg => ((T Unit : Phys) :
      Lp ℝ 2 haar) B) =ᵐ[haar] RawFiber := by
  let k : Cfg → Cfg → ℝ :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel Hn 2 (beta (n + 1))
  let K2 : Lp ℝ 2 (Measure.prod haar haar) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      Hn 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1))
  let u : Lp ℝ 2 haar := (Unit : Phys)
  have hKernel :
      (fun p : Cfg × Cfg => K2 p) =ᵐ[Measure.prod haar haar]
        (fun p : Cfg × Cfg => k p.1 p.2) := by
    simpa only [k, K2,
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure] using
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
        Hn 2 specialUnitaryTwoWilsonRankPositive
        (beta (n + 1)) (hbeta (n + 1)))
  have hMeas :
      AEStronglyMeasurable (fun p : Cfg × Cfg => k p.1 p.2) (Measure.prod haar haar) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      Hn 2 (beta (n + 1))).measurable.aestronglyMeasurable
  have hBound (A B : Cfg) : |k A B| ≤ 1 :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
      Hn 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1)) A B
  have hPhysical :
      ((T Unit : Phys) : Lp ℝ 2 haar) =
        realL2BoundedKernelIntegralOutputL2
          (μ := haar) k hMeas hBound u := by
    change realL2HilbertSchmidtKernelOperator K2 u = _
    exact realL2HilbertSchmidtKernelOperator_apply_eq_integralOutputL2
      (μ := haar) k K2 hKernel hMeas hBound u
  have hUnitAE :
      (fun A : Cfg => u A) =ᵐ[haar] (fun _ => (1 : ℝ)) := by
    change (fun A : Cfg => (Lp.const 2 haar (1 : ℝ)) A) =ᵐ[haar]
      (fun _ => (1 : ℝ))
    exact Lp.coeFn_const (μ := haar) (p := 2) (c := (1 : ℝ))
  have hFiber (B : Cfg) :
      (∫ A : Cfg, k A B * u A ∂haar) = RawFiber B := by
    change (∫ A : Cfg, k A B * u A ∂haar) =
      (∫ A : Cfg, k A B ∂haar)
    apply integral_congr_ae
    filter_upwards [hUnitAE] with A hA
    simp only [hA, mul_one]
  have hOut :=
    realL2BoundedKernelIntegralOutputL2_coeFn
      (μ := haar) k hMeas hBound u
  change (fun B : Cfg => ((T Unit : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar] RawFiber
  rw [hPhysical]
  filter_upwards [hOut] with B hB
  exact hB.trans (hFiber B)

/-- The normalized physical fine Wilson unit is an eigenline of the
true constant Haar vector exactly when the UNNORMALIZED original
interacting Wilson Haar row integral is a.e. constant. There is no
pointwise evaluation of an arbitrary L² class. -/
theorem p4Q2IV_actualFineUnit_eigenline_iff_rawFiber_ae_constant :
    (∃ t : ℝ, FineTransfer Unit = t • Unit) ↔
      ∃ c : ℝ, RawFiber =ᵐ[haar] fun _ => c := by
  have hRaw :=
    p4Q2IV_originalFineWilsonPhysicalUnit_rawFiber_ae
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
  have hUnitAE :
      (fun B : Cfg => ((Unit : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar]
        (fun _ => (1 : ℝ)) := by
    change (fun B : Cfg => (Lp.const 2 haar (1 : ℝ)) B) =ᵐ[haar] _
    exact Lp.coeFn_const (μ := haar) (p := 2) (c := (1 : ℝ))
  have hScalarAE (c : ℝ) :
      (fun B : Cfg => (((c • Unit : Phys) : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar]
        (fun _ => c) := by
    change (fun B : Cfg => (c • ((Unit : Phys) : Lp ℝ 2 haar)) B) =ᵐ[haar] _
    filter_upwards [Lp.coeFn_smul c ((Unit : Phys) : Lp ℝ 2 haar), hUnitAE] with B hs hu
    rw [hs, hu]
    simp
  have hNorm : ‖T‖ ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      Hn 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1))).ne'
  constructor
  · rintro ⟨t, ht⟩
    have hT : T Unit = (t * ‖T‖) • Unit := by
      calc
        T Unit = ‖T‖ • FineTransfer Unit := by
          change T Unit = ‖T‖ • (‖T‖⁻¹ • T Unit)
          rw [smul_smul, mul_inv_cancel₀ hNorm, one_smul]
        _ = ‖T‖ • (t • Unit) := by rw [ht]
        _ = (t * ‖T‖) • Unit := by rw [smul_smul, mul_comm ‖T‖ t]
    refine ⟨t * ‖T‖, ?_⟩
    have hTae :
        (fun B : Cfg => ((T Unit : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar]
          (fun _ => t * ‖T‖) := by
      rw [hT]
      exact hScalarAE _
    exact hRaw.symm.trans hTae
  · rintro ⟨c, hc⟩
    have hCoe :
        (fun B : Cfg => ((T Unit : Phys) : Lp ℝ 2 haar) B) =ᵐ[haar]
          (fun _ => c) := hRaw.trans hc
    have hT : T Unit = c • Unit := by
      apply Subtype.ext
      apply Lp.ext
      exact hCoe.trans (hScalarAE c).symm
    refine ⟨‖T‖⁻¹ * c, ?_⟩
    change ‖T‖⁻¹ • T Unit = (‖T‖⁻¹ * c) • Unit
    rw [hT, smul_smul]

/-- Full support of the original product spatial SU(2) Haar and
continuity of its actual one-slab kernel row upgrade the a.e.
constant condition into a pointwise one on ALL physical boundaries. -/
theorem p4Q2IV_actualFineUnit_eigenline_iff_rawFiber_pointwise_constant :
    (∃ t : ℝ, FineTransfer Unit = t • Unit) ↔
      ∃ c : ℝ, ∀ B : Cfg, RawFiber B = c := by
  rw [p4Q2IV_actualFineUnit_eigenline_iff_rawFiber_ae_constant
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n]
  exact exists_congr (fun c =>
    p4Q2IV_abstract_continuous_ae_constant_iff_pointwise_constant
      haar RawFiber
      (p4Q2IV_originalWilsonUnitHaarKernelSection_continuous Hn (beta (n + 1)))
      c)

/-- Completely physical two-boundary decision procedure:
the first TRUE fine-right Krylov source is noncollinear with the
constant Haar-L² unit exactly when the actual original Wilson
Haar-integrated one-slab kernel takes different values at TWO
real right spatial configurations. This does NOT assert a witness. -/
theorem p4Q2IV_actualFineUnit_notEigenline_iff_two_rawWilson_boundaries :
    (¬ ∃ t : ℝ, FineTransfer Unit = t • Unit) ↔
      ∃ B₀ B₁ : Cfg, RawFiber B₀ ≠ RawFiber B₁ := by
  rw [p4Q2IV_actualFineUnit_eigenline_iff_rawFiber_pointwise_constant
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n]
  constructor
  · intro h
    by_contra hn
    apply h
    push Not at hn
    let B₀ : Cfg := fun _ => 1
    exact ⟨RawFiber B₀, fun B => hn B B₀⟩
  · rintro ⟨B₀, B₁, hne⟩ ⟨c, hc⟩
    exact hne ((hc B₀).trans (hc B₁).symm)

end ActualFine
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IV_abstract_continuous_ae_constant_iff_pointwise_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IV_originalWilsonUnitHaarKernelSection_factorization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IV_originalWilsonUnitHaarKernelSection_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IV_originalFineWilsonPhysicalUnit_rawFiber_ae
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IV_actualFineUnit_eigenline_iff_rawFiber_ae_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IV_actualFineUnit_eigenline_iff_rawFiber_pointwise_constant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2IV_actualFineUnit_notEigenline_iff_two_rawWilson_boundaries
