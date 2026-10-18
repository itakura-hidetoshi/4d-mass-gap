import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSpatialWilsonPhysicalPosteriorMinorKernelV5_JX
import Mathlib.Tactic

/-!
# P4-Q2-JY — exact antisymmetric double-Haar identity for the genuine Wilson receiver

The two ORIGINAL interacting SU(2) Wilson conditional posterior densities
remain unchanged. Their exact antisymmetric two-point determinant M_b(g,h)
was proved by JN/JX to have the opposite temporal Wilson-action order at
every frozen b>0.

We establish its Fubini-consistent anti-symmetrization for every continuous
test receiver F, without inventing any physical detector:
  2 * ∫ F(g) (p0_b(g)-ppi_b(g)) dν(g)
    = ∫∫ (F(g)-F(h)) M_b(g,h) dν(h)dν(g).

Apply this EXACT identity to the original Gauss-law spatial Wilson source
from JU/JX: the original double-Haar Wilson moment and the two-context
physical GI minor are represented entirely through authentic differences
of the same genuine physical receiver at two SU(2) link insertions.

The pointwise anti-monotonicity of M_b relative to temporal D also
implies that every continuous test increasing with D has a nonpositive
original two-posterior test gap, uniformly at ALL positive frozen couplings.
The genuine physical spatial receiver is NOT assumed monotone, and its
strict nonzero second-context GI response is NOT thereby established.

No surrogate independent-Haar conditional law, assumed physical frame,
new axiom/sorry/admit, H1-C3, or continuum Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JY_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JY_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JY_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JY_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JY_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Frozen
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nu" => normalizedCompactHaar Gauge
local notation "D" => p4Q2FZ_originalSU2TemporalWilsonContrast
local notation "M" => p4Q2JN_originalPosteriorTwoPointMinor H

/-- The ACTUAL two interacting Wilson posterior density minor is
strictly antisymmetric upon exchanging two SU(2) right-link insertions. -/
theorem p4Q2JY_originalPosteriorMinor_swap
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (g h : Gauge) :
    M b hb right e h g = -(M b hb right e g h) := by
  unfold p4Q2JN_originalPosteriorTwoPointMinor
  ring

/-- Exact genuine two-posterior anti-symmetrization. Since both Haar
integrations use the original normalized SU(2) reference, and M is
antisymmetric, the constant component of the test disappears.
Fubini is justified by continuity of the actual posterior densities
on compact SU(2) × SU(2), hence genuine integrability. -/
theorem p4Q2JY_originalPosteriorTestGap_antisymmetric
    (b : ℝ) (hb : 0 ≤ b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ)) :
    (2 : ℝ) * p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
        H b hb right e F =
      ∫ g : Gauge, ∫ h : Gauge,
        (F g - F h) * M b hb right e g h ∂nu ∂nu := by
  let P0 := p4Q2JN2_originalPosteriorIdentityContinuous H b hb right e
  let P1 := p4Q2JN2_originalPosteriorPiContinuous H b hb right e
  let A : Gauge × Gauge → ℝ :=
    fun p => F p.1 * M b hb right e p.1 p.2
  let B : Gauge × Gauge → ℝ :=
    fun p => F p.2 * M b hb right e p.1 p.2
  have hMCont :
      Continuous (fun p : Gauge × Gauge => M b hb right e p.1 p.2) := by
    change Continuous (fun p : Gauge × Gauge =>
      P0 p.1 * P1 p.2 - P0 p.2 * P1 p.1)
    exact ((P0.continuous.comp continuous_fst).mul
      (P1.continuous.comp continuous_snd)).sub
      ((P0.continuous.comp continuous_snd).mul
        (P1.continuous.comp continuous_fst))
  have hACont : Continuous A :=
    (F.continuous.comp continuous_fst).mul hMCont
  have hBCont : Continuous B :=
    (F.continuous.comp continuous_snd).mul hMCont
  have hAI : Integrable A (nu.prod nu) :=
    hACont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hBI : Integrable B (nu.prod nu) :=
    hBCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSwap :
      (∫ g : Gauge, ∫ h : Gauge, B (g,h) ∂nu ∂nu) =
        (∫ h : Gauge, ∫ g : Gauge, B (g,h) ∂nu ∂nu) :=
    integral_integral_swap_of_hasCompactSupport
      (μ := nu) (ν := nu)
      hBCont (HasCompactSupport.of_compactSpace _)
  have hMinus (g h : Gauge) : B (h,g) = -(A (g,h)) := by
    dsimp [A, B]
    rw [p4Q2JY_originalPosteriorMinor_swap H b hb right e g h]
    ring
  have hBIntegral :
      (∫ g : Gauge, ∫ h : Gauge, B (g,h) ∂nu ∂nu) =
        -(∫ g : Gauge, ∫ h : Gauge, A (g,h) ∂nu ∂nu) := by
    calc
      (∫ g : Gauge, ∫ h : Gauge, B (g,h) ∂nu ∂nu) =
          ∫ h : Gauge, ∫ g : Gauge, B (g,h) ∂nu ∂nu := hSwap
      _ = ∫ g : Gauge, ∫ h : Gauge, B (h,g) ∂nu ∂nu := rfl
      _ = ∫ g : Gauge, ∫ h : Gauge, -(A (g,h)) ∂nu ∂nu := by
        apply integral_congr_ae
        filter_upwards with g
        apply integral_congr_ae
        filter_upwards with h
        exact hMinus g h
      _ = -(∫ g : Gauge, ∫ h : Gauge, A (g,h) ∂nu ∂nu) := by
        simp only [integral_neg]
  have hExpand (g h : Gauge) :
      (F g - F h) * M b hb right e g h =
        A (g,h) - B (g,h) := by
    dsimp [A, B]
    ring
  calc
    (2 : ℝ) * p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
        H b hb right e F =
      (2 : ℝ) * (∫ g : Gauge, ∫ h : Gauge,
        A (g,h) ∂nu ∂nu) := by
          rw [p4Q2JX_originalPosteriorTestGap_eq_iteratedMinor]
          rfl
    _ = (∫ g : Gauge, ∫ h : Gauge, A (g,h) ∂nu ∂nu) -
        (∫ g : Gauge, ∫ h : Gauge, B (g,h) ∂nu ∂nu) := by
          rw [hBIntegral]
          ring
    _ = (∫ g : Gauge, ∫ h : Gauge,
        A (g,h) - B (g,h) ∂nu ∂nu) := by
          exact (integral_integral_sub hAI hBI).symm
    _ = ∫ g : Gauge, ∫ h : Gauge,
        (F g - F h) * M b hb right e g h ∂nu ∂nu := by
          apply integral_congr_ae
          filter_upwards with g
          apply integral_congr_ae
          filter_upwards with h
          exact (hExpand g h).symm

/-- The sign of the literal original density minor and an order-preserving
continuous test together force nonpositivity of every SU(2) pair term.
This is NOT asserted for an arbitrary actual spatial Wilson receiver. -/
theorem p4Q2JY_originalPosteriorMonotonePair_nonpos
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ))
    (hMon : ∀ g h : Gauge, D g ≤ D h → F g ≤ F h)
    (g h : Gauge) :
    (F g - F h) * M b hb.le right e g h ≤ 0 := by
  rcases lt_trichotomy (D g) (D h) with hlt | heq | hgt
  · have hm := p4Q2JX_originalPosteriorMinor_pos_of_temporal_lt
      H b hb right e g h hlt
    exact mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hMon g h hlt.le)) hm.le
  · have hzero : M b hb.le right e g h = 0 := by
      rw [p4Q2JN_originalPosteriorMinor_exact_temporalFactor]
      rw [heq, sub_self]
      simp
    rw [hzero, mul_zero]
  · have hm := p4Q2JX_originalPosteriorMinor_neg_of_temporal_gt
      H b hb right e g h hgt
    exact mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr (hMon h g hgt.le)) hm.le

/-- The ORIGINAL interacting Wilson posterior gap has a nonpositive
sign against EVERY continuous temporal-order-preserving test, even
outside JP's small-positive frozen-coupling interval. -/
theorem p4Q2JY_originalPosteriorTestGap_nonpos_of_temporalMonotone
    (b : ℝ) (hb : 0 < b) (right : Cfg) (e : Link)
    (F : C(Gauge, ℝ))
    (hMon : ∀ g h : Gauge, D g ≤ D h → F g ≤ F h) :
    p4Q2JP_originalWilsonTwoPosteriorTemporalTestGap
      H b hb.le right e F ≤ 0 := by
  have hPair (g h : Gauge) :
      (F g - F h) * M b hb.le right e g h ≤ 0 :=
    p4Q2JY_originalPosteriorMonotonePair_nonpos
      H b hb right e F hMon g h
  have hInner (g : Gauge) :
      (∫ h : Gauge,
        (F g - F h) * M b hb.le right e g h ∂nu) ≤ 0 := by
    apply integral_nonpos
    intro h
    exact hPair g h
  have hDouble :
      (∫ g : Gauge, ∫ h : Gauge,
        (F g - F h) * M b hb.le right e g h ∂nu ∂nu) ≤ 0 := by
    apply integral_nonpos
    intro g
    exact hInner g
  rw [← p4Q2JY_originalPosteriorTestGap_antisymmetric
    H b hb.le right e F] at hDouble
  linarith

/-- EXACT original physical spatial Wilson source double-Haar moment
expressed by DIFFERENCES of the same true continuous physical receiver.
In particular its constant SU(2) component is invisible. -/
theorem p4Q2JY_originalSpatialWilsonMoment_antisymmetric
    (b : ℝ) (hb : 0 ≤ b) (e e' : Link)
    (z z' : Cfg × Cfg) :
    (2 : ℝ) *
      p4Q2JX_originalSpatialSourcePosteriorTwoPointMoment
        H b hb e e' z z' =
      ∫ g : Gauge, ∫ h : Gauge,
        (p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
          e' z' g -
         p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb
          (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
          e' z' h) *
          M b hb z'.2 e' g h ∂nu ∂nu := by
  let F := p4Q2JQ_originalPhysicalSourceLinkReceiver H b hb
    (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z) e' z'
  have h := p4Q2JY_originalPosteriorTestGap_antisymmetric
    H b hb z'.2 e' F
  rw [p4Q2JX_originalPosteriorTestGap_eq_iteratedMinor] at h
  exact h

end Frozen
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JY_originalPosteriorMinor_swap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JY_originalPosteriorTestGap_antisymmetric
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JY_originalPosteriorMonotonePair_nonpos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JY_originalPosteriorTestGap_nonpos_of_temporalMonotone
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JY_originalSpatialWilsonMoment_antisymmetric
