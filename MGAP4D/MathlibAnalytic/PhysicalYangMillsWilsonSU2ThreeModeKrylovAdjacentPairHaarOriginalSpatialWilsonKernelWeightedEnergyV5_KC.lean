import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonPhysicalSourceGIBridgeV5_JU
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonCenterWitnessV5_IY
import Mathlib.Tactic

/-!
# P4-Q2-KC — strictly positive original Wilson-kernel-weighted spatial energy

IY proves the ACTUAL finite spatial SU(2) Wilson plaquette action W_H
is nonconstant for every finite periodic even lattice, by an explicit
primary-link central twist. JU realizes W_H-c as a genuine
gauge-invariant Gauss-law physical Hilbert source.

The ORIGINAL frozen-Wilson one-slab transfer K_b(A,B) is strictly
positive for EVERY b, every physical source spatial configuration A,
and every right configuration B; the true spatial product Haar measure
has full topological support.

Therefore the ORIGINAL Wilson weighted centered-square source energy

       integral_A K_b(A,B) * (W_H(A)-c)^2 dHaar(A)

is strictly positive FOR ANY real scalar center c, EVERY finite H,
EVERY frozen b and EVERY physical right configuration B.
In particular this applies to JK's ACTUAL GI anchor center c_(b,e,z)
and JU's original physical Gauss-law anchored spatial Wilson source.

This proves a genuinely nondegenerate ORIGINAL WILSON KERNEL-WEIGHTED
SPATIAL QUADRATIC SOURCE, stronger than ordinary Haar-L² nonconstancy.
It does NOT prove the SIGNED GI source's first kernel moment or the
outstanding second-context detector response is nonzero. No fictitious
frame/rank, independent-Haar conditional posterior, sorry/new axiom,
H1-C3 or continuum Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2KC_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2KC_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2KC_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2KC_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2KC_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2KC_su2HaarOpenPos :
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)).IsOpenPosMeasure := by
  unfold normalizedCompactHaar
  infer_instance

local instance p4Q2KC_spatialHaarOpenPos (H : ℕ) :
    (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

namespace GroundStatePosteriorJoint
section Finite
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "W" => p4Q2JI_actualSpatialWilsonContinuous H

/-- Compact, genuine-Haar principle: any everywhere-positive
CONTINUOUS weight has strictly positive squared energy against
a continuous function which is nonzero at some genuine point. -/
private theorem p4Q2KC_positiveContinuousWeight_squaredEnergy_pos
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (k f : C(X, ℝ))
    (hk : ∀ x : X, 0 < k x)
    (hf : ∃ x : X, f x ≠ 0) :
    0 < ∫ x : X, k x * (f x) ^ 2 ∂μ := by
  have hQ : Continuous (fun x : X => k x * (f x) ^ 2) :=
    k.continuous.mul (f.continuous.pow 2)
  have hI : Integrable (fun x : X => k x * (f x) ^ 2) μ :=
    hQ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨x, hx⟩ := hf
  have hQAt : k x * (f x) ^ 2 ≠ 0 :=
    mul_ne_zero (hk x).ne' (pow_ne_zero 2 hx)
  have hOpen :
      IsOpen (Function.support (fun y : X => k y * (f y) ^ 2)) := by
    change IsOpen
      ((fun y : X => k y * (f y) ^ 2) ⁻¹' ({0} : Set ℝ)ᶜ)
    exact (isClosed_singleton.isOpen_compl).preimage hQ
  rw [integral_pos_iff_support_of_nonneg]
  · exact hOpen.measure_pos _ ⟨x, hQAt⟩
  · intro y
    exact mul_nonneg (hk y).le (sq_nonneg _)
  · exact hI

/-- Original Wilson one-slab K_b(A,B), continuous in the ACTUAL
spatial SU(2) source configuration A for each fixed physical B. -/
noncomputable def p4Q2KC_originalWilsonKernelColumn
    (b : ℝ) (B : Cfg) : C(Cfg, ℝ) :=
  ⟨fun A => K b A B,
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 b).comp (continuous_id.prodMk continuous_const)⟩

/-- NO assumption of monotonicity or nonzero GI signed detector:
strict positive ORIGINAL frozen-Wilson-weighted spatial squared source
energy about ANY scalar center, every coupling and right context.
The strict witness is the genuine Wilson primary-link central twist. -/
theorem p4Q2KC_originalSpatialWilsonKernelCenteredEnergy_pos
    (b : ℝ) (B : Cfg) (c : ℝ) :
    0 < ∫ A : Cfg, K b A B * (W A - c) ^ 2 ∂haar := by
  let k : C(Cfg, ℝ) := p4Q2KC_originalWilsonKernelColumn H b B
  let f : C(Cfg, ℝ) := W - c • (1 : C(Cfg, ℝ))
  have hK (A : Cfg) : 0 < k A :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A B
  obtain ⟨A₀, A₁, hW⟩ := p4Q2IY_originalSpatialWilsonAction_not_constant H
  have hA : ∃ A : Cfg, W A ≠ c := by
    by_cases h0 : W A₀ = c
    · refine ⟨A₁, ?_⟩
      intro h1
      exact hW (h0.trans h1.symm)
    · exact ⟨A₀, h0⟩
  obtain ⟨A, hAw⟩ := hA
  have hF : ∃ X : Cfg, f X ≠ 0 := by
    refine ⟨A, ?_⟩
    have hEval : f A = W A - c := by
      simp only [f, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, mul_one]
    rw [hEval]
    exact sub_ne_zero.mpr hAw
  have hResult :=
    p4Q2KC_positiveContinuousWeight_squaredEnergy_pos haar k f hK hF
  simpa only [k, f, p4Q2KC_originalWilsonKernelColumn,
    ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one] using hResult

/-- The ACTUAL original spatial Wilson GI-anchored Gauss-law source
from JK/JU has strictly positive one-slab Wilson-kernel-weighted
quadratic energy, despite having ZERO signed GI response at its OWN
anchor (JV). Do not confuse positive energy with detector nonzero. -/
theorem p4Q2KC_originalAnchoredSpatialWilsonKernelEnergy_pos
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (B : Cfg) :
    0 < ∫ A : Cfg,
      K b A B * (p4Q2JK_anchorCenteredSpatialWilson H b hb e z A) ^ 2 ∂haar := by
  simpa only [p4Q2JK_anchorCenteredSpatialWilson, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul, mul_one]
    using (p4Q2KC_originalSpatialWilsonKernelCenteredEnergy_pos
      H b B (p4Q2JK_originalWilsonAnchorSlope H b hb e z))

end Finite
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KC_originalSpatialWilsonKernelCenteredEnergy_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KC_originalAnchoredSpatialWilsonKernelEnergy_pos
