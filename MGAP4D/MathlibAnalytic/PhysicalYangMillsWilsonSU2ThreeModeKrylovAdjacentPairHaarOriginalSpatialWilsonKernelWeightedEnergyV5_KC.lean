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

/-- NO assumption of monotonicity or nonzero GI signed detector:
strict positive ORIGINAL frozen-Wilson-weighted spatial squared source
energy about ANY scalar center, every coupling and right context.
The strict witness is the genuine Wilson primary-link central twist. -/
theorem p4Q2KC_originalSpatialWilsonKernelCenteredEnergy_pos
    (b : ℝ) (B : Cfg) (c : ℝ) :
    0 < ∫ A : Cfg, K b A B * (W A - c) ^ 2 ∂haar := by
  let k : Cfg → ℝ := fun A => K b A B
  let w : C(Cfg, ℝ) := W
  have hk : Continuous k :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H 2 b).comp (continuous_id.prodMk continuous_const)
  have hQ : Continuous (fun A : Cfg => k A * (w A - c) ^ 2) :=
    hk.mul ((w.continuous.sub continuous_const).pow 2)
  have hI : Integrable (fun A : Cfg => k A * (w A - c) ^ 2) haar :=
    hQ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨A₀, A₁, hW⟩ := p4Q2IY_originalSpatialWilsonAction_not_constant H
  have hA : ∃ A : Cfg, w A ≠ c := by
    by_cases h0 : w A₀ = c
    · refine ⟨A₁, ?_⟩
      intro h1
      exact hW (h0.trans h1.symm)
    · exact ⟨A₀, h0⟩
  obtain ⟨A, hAw⟩ := hA
  have hK : k A ≠ 0 :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H 2 b A B).ne'
  have hQAt : k A * (w A - c) ^ 2 ≠ 0 :=
    mul_ne_zero hK (pow_ne_zero 2 (sub_ne_zero.mpr hAw))
  have hOpen :
      IsOpen (Function.support (fun X : Cfg => k X * (w X - c) ^ 2)) := by
    change IsOpen
      ((fun X : Cfg => k X * (w X - c) ^ 2) ⁻¹' ({0} : Set ℝ)ᶜ)
    exact (isClosed_singleton.isOpen_compl).preimage hQ
  change 0 < ∫ X : Cfg, k X * (w X - c) ^ 2 ∂haar
  rw [integral_pos_iff_support_of_nonneg]
  · exact hOpen.measure_pos _ ⟨A, hQAt⟩
  · intro X
    exact mul_nonneg
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
        H 2 b X B).le
      (sq_nonneg _)
  · exact hI

/-- The ACTUAL original spatial Wilson GI-anchored Gauss-law source
from JK/JU has strictly positive one-slab Wilson-kernel-weighted
quadratic energy, despite having ZERO signed GI response at its OWN
anchor (JV). Do not confuse positive energy with detector nonzero. -/
theorem p4Q2KC_originalAnchoredSpatialWilsonKernelEnergy_pos
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) (B : Cfg) :
    0 < ∫ A : Cfg,
      K b A B * (p4Q2JK_anchorCenteredSpatialWilson H b hb e z A) ^ 2 ∂haar := by
  change 0 < ∫ A : Cfg,
    K b A B * (W A - p4Q2JK_originalWilsonAnchorSlope H b hb e z) ^ 2 ∂haar
  exact p4Q2KC_originalSpatialWilsonKernelCenteredEnergy_pos
    H b B (p4Q2JK_originalWilsonAnchorSlope H b hb e z)

end Finite
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KC_originalSpatialWilsonKernelCenteredEnergy_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2KC_originalAnchoredSpatialWilsonKernelEnergy_pos
