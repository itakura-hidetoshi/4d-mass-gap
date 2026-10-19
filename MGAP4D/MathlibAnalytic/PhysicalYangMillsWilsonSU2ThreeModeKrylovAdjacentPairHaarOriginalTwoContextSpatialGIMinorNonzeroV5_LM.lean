import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaugeNormalizedCenteredTransferV5_LK
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSourceLeftLinkFactorizationV5_LC
import Mathlib.Tactic

/-!
# P4-Q2-LM — TRUE original two-context static spatial Wilson GI minor is NONZERO

All steps are previously theorem-proved in genuine original SU(2)
Yang-Mills physical Hilbert space, using the literal Wilson one-slab
kernel and the TWO ACTUAL interacting Wilson posterior densities:

- LB: true physical constant-unit source is GI detected by some
  genuine left-link boundary, giving a NONZERO first GI anchor.
- JH and JU: the same constant physical Gauss-law source corresponds
  exactly to the Haar-L² continuous constant and its original
  frozen interacting-posterior GI response.
- JK and JU: the original static spatial Wilson 2-context determinant
  equals the nonzero anchor multiplied by the original physical
  GI response of the true anchor-centered spatial Wilson source.
- LI/LJ: the FULL original Wilson transfer has strictly positive
  Haar quadratic energy, hence this nonzero centered physical
  spatial Wilson source has nonzero original transfer somewhere.
- LK: gauge covariance and full spatial Haar invariance transport
  that nonzero transfer to a genuine right boundary with ANY
  specified right SU(2) link equal to the identity.
- LC: exact original left-link Perron half-density factorization
  and the proved SU(2) negative-exponential Haar transform
  injectivity convert the true nonzero centered physical transfer
  at identity right-link fiber to a NONZERO original physical
  two-interacting-Wilson-posterior GI response at some second
  genuine left boundary.
- JU: this is exactly the ORIGINAL spatial Wilson determinant's
  nonzero centered-response factor.

The resulting theorem says: for every finite spatial volume H,
positive Wilson coupling b, and every pair of actual spatial
links e and e', TWO genuine full SU(2) left/right boundary contexts
exist with a nonzero ORIGINAL two-source (1, spatial Wilson action)
two-GI-detector determinant. No imaginary source, no rank/frame
hypothesis, no independent-Haar posterior or artificial detector.

This is a POINTWISE finite-volume rank-two GI witness. It does NOT
establish a quantitative rank lower bound uniform in H, H1-C3
strong-limit closure, OS Hilbert identification, continuum Yang-Mills
existence or a positive continuum mass gap. No sorry/admit/new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic
open MeasureTheory
open scoped ENNReal Topology InnerProductSpace BigOperators
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2LM_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2LM_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2LM_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2LM_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2LM_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "U" => periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- JH's literal frozen original GI functional on Haar-L²
constant one IS EXACTLY the original two-interacting-posterior
physical GI response of the TRUE Gauss-law constant unit. -/
theorem p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    p4Q2JH_originalGIResponseCLM H b hb e z (L (1 : C(Cfg, ℝ))) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb U e z := by
  have hLp : ((U : Phys) : Lp ℝ 2 haar) =
      L (1 : C(Cfg, ℝ)) :=
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H
  have hRep :
      (fun A : Cfg => ((U : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar]
        (1 : C(Cfg, ℝ)) := by
    rw [hLp]
    exact (1 : C(Cfg, ℝ)).coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hAgree :=
    p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
      H b hb e z U (1 : C(Cfg, ℝ)) hRep
  rw [hLp] at hAgree
  exact hAgree

/-- For EVERY positive original Wilson coupling and any actual
spatial link e and frozen left/right backgrounds, the TRUE
physical constant unit has a NONZERO GI anchor at some original
left-link SU(2) insertion, not a synthetic anchor hypothesis. -/
theorem p4Q2LM_originalUnitGIAnchor_exists_nonzero
    (b : ℝ) (hb : 0 < b) (e : Link)
    (left₀ right₀ : Cfg) :
    ∃ z : Cfg × Cfg,
      p4Q2JH_originalGIResponseCLM H b hb.le e z
        (L (1 : C(Cfg, ℝ))) ≠ 0 := by
  obtain ⟨u, hu⟩ :=
    p4Q2LB_originalPhysicalUnitGI_nonzero_some_actualLeftBoundary
      H b hb left₀ right₀ e (1 : Gauge) (1 : Gauge)
  refine ⟨(Function.update left₀ e u, right₀), ?_⟩
  rw [p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI]
  exact hu

/-- At ANY true nonzero physical constant-unit anchor and any
SECOND original spatial link, the original two-context GI spatial
Wilson determinant has a genuine second full left/right boundary
context at which it is NONZERO. No quantitative lower bound is
asserted; the existential second context is supplied by actual
LK gauge-normalized centered transfer plus LC exponential
Wilson posterior detection. -/
theorem p4Q2LM_originalSpatialWilsonGIMinor_exists_second_of_anchor
    (b : ℝ) (hb : 0 < b) (e e' : Link)
    (z : Cfg × Cfg)
    (hAnchor :
      p4Q2JH_originalGIResponseCLM H b hb.le e z
        (L (1 : C(Cfg, ℝ))) ≠ 0) :
    ∃ z' : Cfg × Cfg,
      p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z' ≠ 0 := by
  obtain ⟨right, ht⟩ :=
    p4Q2LK_originalCenteredSpatialWilsonPhysicalTransfer_nonzero_at_identityFiber
      H b hb e e' z
  obtain ⟨u, hu⟩ :=
    p4Q2LC_originalSpatialWilsonMinor_nonzero_of_centeredTransfer_identity
      H b hb e e' z z.1 right (1 : Gauge) (1 : Gauge)
      hAnchor ht
  exact ⟨(Function.update z.1 e' u, right), hu⟩

/-- Original Wilson static two-source GI rank-TWO witness:
for EVERY finite spatial H, every real b>0, and EVERY
pair of actual physical spatial links e,e', there exist TWO
genuine complete SU(2) boundary contexts (z,z') with
NONZERO original (physical unit, original spatial Wilson action)
two-GI-row determinant. All sources and posteriors are
genuine and the determinant is the ORIGINAL JI minor. -/
theorem p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts
    (b : ℝ) (hb : 0 < b) (e e' : Link)
    (left₀ right₀ : Cfg) :
    ∃ z z' : Cfg × Cfg,
      p4Q2JI_originalGISpatialActionMinor H b hb.le e e' z z' ≠ 0 := by
  obtain ⟨z, hAnchor⟩ :=
    p4Q2LM_originalUnitGIAnchor_exists_nonzero H b hb e left₀ right₀
  obtain ⟨z', hz'⟩ :=
    p4Q2LM_originalSpatialWilsonGIMinor_exists_second_of_anchor
      H b hb e e' z hAnchor
  exact ⟨z, z', hz'⟩

end Spatial
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LM_originalUnitGIAnchor_eq_truePhysicalUnitGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LM_originalUnitGIAnchor_exists_nonzero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LM_originalSpatialWilsonGIMinor_exists_second_of_anchor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts
