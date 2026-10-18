import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalStaticGISpatialKernelV5_JK
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryPositiveHalfClosurePrimarySpatialWilsonActionInsertion
import Mathlib.Tactic

/-!
# P4-Q2-JU — the actual spatial Wilson action is an original Gauss-law physical source

The genuine spatial Wilson action W_H is an existing bounded continuous,
gauge-invariant finite-lattice observable. We realize its original spatial
Haar-L2 vector as a PHYSICAL GAUSS-LAW vector: apply the already formalized
physical Wilson-action multiplication operator to the actual physical
constant unit. This is not a synthetic detector direction.

The original Hilbert source has W_H as its genuine continuous Haar-a.e.
representative, and the original physical unit has constant one as such
a representative. The original JH theorem (not a new transfer law) then
identifies the original physical two-interacting-Wilson-posterior GI response
of this vector with the JK/JI Riesz detector applied to Haar-L2 W_H.

Subtract the exact JK GI-anchor slope as a scalar multiple of the ORIGINAL
physical constant unit. The result is an actual Gauss-law Hilbert source
whose spatial Haar-L2 vector is EXACTLY the original anchor-centered Wilson
action W_H-c_x*1. JH therefore identifies its original physical GI response
with the full frozen Wilson Riesz response used in the unsolved spatial
two-context minor. The minor equals nonzero original anchor times this
ACTUAL physical source GI response at a genuine second context.

No nonzero second context is assumed or found. No false replacement of the
interacting posteriors by independent Haar, hypothetical rank/frame, new
axiom, sorry/admit, H1-C3 closure or continuum YM mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2JU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2JU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2JU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2JU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2JU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

section Finite
variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Phys" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "haar" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 haar ℝ

/-- The ACTUAL physical Gauss-law spatial Wilson action vector: apply
the gauge-invariant Wilson observable multiplication operator to the
genuine physical constant unit, without an artificial Hilbert source. -/
noncomputable def p4Q2JU_originalSpatialWilsonPhysicalSource : Phys :=
  periodicHypercubicEvenSpecialUnitaryPhysicalSpatialWilsonActionMulOperator H 2
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)

/-- The original physical Wilson multiplication has exactly the original
continuous spatial plaquette action as its Haar-a.e. representative. -/
theorem p4Q2JU_originalSpatialWilsonPhysicalSource_ae :
    (fun A : Cfg =>
      ((p4Q2JU_originalSpatialWilsonPhysicalSource H : Phys) :
        Lp ℝ 2 haar) A) =ᵐ[haar]
      (fun A : Cfg => p4Q2JI_actualSpatialWilsonContinuous H A) := by
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let W := periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonActionBoundedObservable H 2
  have hMul :
      (fun A : Cfg =>
        ((p4Q2JU_originalSpatialWilsonPhysicalSource H : Phys) :
          Lp ℝ 2 haar) A) =ᵐ[haar]
        (fun A : Cfg => W A * (U : Lp ℝ 2 haar) A) := by
    change (fun A : Cfg =>
      (periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2
        H 2 W (U : Lp ℝ 2 haar)) A) =ᵐ[haar]
      (fun A : Cfg => W A * (U : Lp ℝ 2 haar) A)
    exact periodicHypercubicEvenSpecialUnitarySpatialSliceBoundedObservableMulL2_coeFn
      H 2 W (U : Lp ℝ 2 haar)
  have hU : (fun A : Cfg => (U : Lp ℝ 2 haar) A) =ᵐ[haar]
      (fun _ => (1 : ℝ)) := by
    change (fun A : Cfg => (Lp.const 2 haar (1 : ℝ)) A) =ᵐ[haar]
      (fun _ => (1 : ℝ))
    exact Lp.coeFn_const (μ := haar) (p := 2) (c := (1 : ℝ))
  filter_upwards [hMul, hU] with A hm hu
  rw [hm, hu]
  change W A * 1 = W A
  ring

/-- The physical source's original Haar-L2 vector is IDENTICALLY the
continuous spatial Wilson observable embedded by pinned mathlib toLp. -/
theorem p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp :
    ((p4Q2JU_originalSpatialWilsonPhysicalSource H : Phys) : Lp ℝ 2 haar) =
      L (p4Q2JI_actualSpatialWilsonContinuous H) := by
  apply Lp.ext
  exact (p4Q2JU_originalSpatialWilsonPhysicalSource_ae H).trans
    ((p4Q2JI_actualSpatialWilsonContinuous H).coeFn_toLp
      (p := 2) (𝕜 := ℝ) haar).symm

/-- The genuine physical Haar-L2 constant unit is exactly the
mathlib embedding of the continuous constant one. -/
theorem p4Q2JU_originalPhysicalUnit_coe_eq_toLp :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
        Phys) : Lp ℝ 2 haar) = L (1 : C(Cfg, ℝ)) := by
  apply Lp.ext
  have hU :
      (fun A : Cfg =>
        ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
          H 2 : Phys) : Lp ℝ 2 haar) A) =ᵐ[haar]
          (1 : C(Cfg, ℝ)) := by
    change (fun A : Cfg => (Lp.const 2 haar (1 : ℝ)) A) =ᵐ[haar]
      (fun _ => (1 : ℝ))
    exact Lp.coeFn_const (μ := haar) (p := 2) (c := (1 : ℝ))
  exact hU.trans ((1 : C(Cfg, ℝ)).coeFn_toLp
    (p := 2) (𝕜 := ℝ) haar).symm

/-- JH's REAL original Wilson Riesz functional is the actual physical
Gauss-law GI response of the truly gauge-invariant spatial Wilson action. -/
theorem p4Q2JU_originalSpatialWilsonGI_eq_actualPhysicalGI
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    p4Q2JH_originalGIResponseCLM H b hb e z
        (L (p4Q2JI_actualSpatialWilsonContinuous H)) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
        H b hb (p4Q2JU_originalSpatialWilsonPhysicalSource H) e z := by
  let P : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let W : C(Cfg, ℝ) := p4Q2JI_actualSpatialWilsonContinuous H
  have hRep :
      (fun A : Cfg => (P : Lp ℝ 2 haar) A) =ᵐ[haar] W :=
    p4Q2JU_originalSpatialWilsonPhysicalSource_ae H
  have hAgree :=
    p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
      H b hb e z P W hRep
  rw [p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H] at hAgree
  exact hAgree

/-- The genuinely physical centered spatial Wilson source associated
to a real original GI anchor (not a surrogate continuous test). -/
noncomputable def p4Q2JU_originalAnchorCenteredWilsonPhysicalSource
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) : Phys :=
  p4Q2JU_originalSpatialWilsonPhysicalSource H -
    p4Q2JK_originalWilsonAnchorSlope H b hb e z •
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2

/-- The true physical anchored source equals the original JK centered
spatial Wilson action AS AN L2 VECTOR, without ignoring gauge invariance. -/
theorem p4Q2JU_originalAnchorCenteredWilsonPhysicalSource_coe_eq_toLp
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (z : Cfg × Cfg) :
    ((p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z :
      Phys) : Lp ℝ 2 haar) =
      L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z) := by
  change
    ((p4Q2JU_originalSpatialWilsonPhysicalSource H -
      p4Q2JK_originalWilsonAnchorSlope H b hb e z •
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 : Phys) :
        Lp ℝ 2 haar) =
      L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z)
  rw [Submodule.coe_sub, Submodule.coe_smul,
    p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp,
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp,
    p4Q2JK_centeredWilson_toLp]

/-- The ORIGINAL physical two-interacting-Wilson-posterior GI gap of
the anchored physical Wilson source equals JK's Riesz response exactly. -/
theorem p4Q2JU_originalCenteredSpatialGI_eq_actualPhysicalGI
    (b : ℝ) (hb : 0 ≤ b)
    (e e' : Link) (z z' : Cfg × Cfg) :
    p4Q2JH_originalGIResponseCLM H b hb e' z'
        (L (p4Q2JK_anchorCenteredSpatialWilson H b hb e z)) =
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
        e' z' := by
  let P : Phys := p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z
  let W : C(Cfg, ℝ) := p4Q2JK_anchorCenteredSpatialWilson H b hb e z
  have hL :
      (P : Lp ℝ 2 haar) = L W :=
    p4Q2JU_originalAnchorCenteredWilsonPhysicalSource_coe_eq_toLp H b hb e z
  have hRep : (fun A : Cfg => (P : Lp ℝ 2 haar) A) =ᵐ[haar] W := by
    rw [hL]
    exact W.coeFn_toLp (p := 2) (𝕜 := ℝ) haar
  have hAgree :=
    p4Q2JH_originalGIResponseCLM_agrees_with_physicalGI
      H b hb e' z' P W hRep
  rw [hL] at hAgree
  exact hAgree

/-- The genuine original spatial Wilson 2-context determinant is an
ACTUAL PHYSICAL GAUSS-LAW GI response of the original anchored spatial
Wilson action, multiplied by the proven nonzero original anchor.
The existence of a nonzero SECOND physical context remains OPEN. -/
theorem p4Q2JU_originalSpatialMinor_eq_anchor_mul_physicalGI
    (b : ℝ) (hb : 0 ≤ b)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor :
      p4Q2JH_originalGIResponseCLM H b hb e z
        (L (1 : C(Cfg, ℝ))) ≠ 0) :
    p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' =
      p4Q2JH_originalGIResponseCLM H b hb e z
        (L (1 : C(Cfg, ℝ))) *
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
        e' z' := by
  rw [p4Q2JK_originalSpatialMinor_eq_anchor_mul_centeredGI
    H b hb e e' z z' hAnchor]
  rw [p4Q2JU_originalCenteredSpatialGI_eq_actualPhysicalGI]

/-- The still-open spatial Wilson nonzero minor is EXACTLY equivalent
to detection of a specific explicitly constructed ACTUAL physical
gauge-invariant centered Wilson Hilbert source, at one second context. -/
theorem p4Q2JU_originalSpatialMinor_ne_iff_physicalGI_ne
    (b : ℝ) (hb : 0 ≤ b)
    (e e' : Link) (z z' : Cfg × Cfg)
    (hAnchor :
      p4Q2JH_originalGIResponseCLM H b hb e z
        (L (1 : C(Cfg, ℝ))) ≠ 0) :
    p4Q2JI_originalGISpatialActionMinor H b hb e e' z z' ≠ 0 ↔
      p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap H b hb
        (p4Q2JU_originalAnchorCenteredWilsonPhysicalSource H b hb e z)
        e' z' ≠ 0 := by
  rw [p4Q2JU_originalSpatialMinor_eq_anchor_mul_physicalGI
    H b hb e e' z z' hAnchor]
  constructor
  · intro h hn
    apply h
    rw [hn, mul_zero]
  · exact mul_ne_zero hAnchor

end Finite
end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JU_originalSpatialWilsonPhysicalSource_ae
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JU_originalPhysicalUnit_coe_eq_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JU_originalSpatialWilsonGI_eq_actualPhysicalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JU_originalAnchorCenteredWilsonPhysicalSource_coe_eq_toLp
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JU_originalCenteredSpatialGI_eq_actualPhysicalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JU_originalSpatialMinor_eq_anchor_mul_physicalGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2JU_originalSpatialMinor_ne_iff_physicalGI_ne