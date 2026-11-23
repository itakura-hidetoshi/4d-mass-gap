import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedLeftFullSlabCharacterV5_PZ37AOK
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRowLocalLinearResponseV5_PZ37AOM
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AON — exact original zero-coupling local gap Haar coefficient

Source-bound candidate, never silently adopted before direct Lean, real MCP and
fresh exact-head independent CI. The original SU(2) Wilson action, genuine
spatial Haar probability and center-twist remain unchanged.

AOK supplies the exact fixed-left one-slab Haar first moment -1/8; AOM
supplies the exact original Haar antisymmetrization. The local center-twist
action difference therefore has exact first Haar coefficient -1/4 for all
finite H and fixed left A. A second theorem restores the literal Wilson
kernel at beta=0, without replacing the interacting coefficient at beta>0.

No normalized physical-top derivative, uniform beta slope, spectral gap,
continuum scaling or 4D Yang-Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AON_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AON_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AON_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AON_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AON_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AON_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem p4Q2PZ37AON_fixedLeftSlabAction_continuous
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    Continuous (fun B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  have hPair : Continuous (fun B : Cfg => (A, B)) :=
    (continuous_const : Continuous (fun _ : Cfg => A)).prodMk
      (continuous_id : Continuous (fun B : Cfg => B))
  have hCross : Continuous (fun B : Cfg =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 A B) := by
    change Continuous
      ((fun p : Cfg × Cfg =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2 p.1 p.2) ∘
        (fun B : Cfg => (A, B)))
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_continuous
      H 2).comp hPair
  have hWilson :
      Continuous (periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2) :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_continuous H 2
  dsimp [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction]
  exact (continuous_const.add hCross).add (continuous_const.mul hWilson)

/-- The original right center-twist action difference has Haar first-character
moment -1/4 for EVERY finite H and fixed left original configuration A.
No beta-dependent kernel or left-boundary averaging is substituted. -/
theorem p4Q2PZ37AON_originalFixedLeftCenterTwistGap_primaryHaar_eq_neg_quarter
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        -(1 / 4 : ℝ) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  let F : Cfg → ℝ := fun B =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B
  have hF : Continuous F := p4Q2PZ37AON_fixedLeftSlabAction_continuous H A
  have hAnti :=
    p4Q2PZ37AOM_originalHaarPrimaryCharacter_antisymmetrization H F hF
  change (-2 : ℝ) *
      (∫ B : Cfg, F B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) ∂mu) =
      -(∫ B : Cfg, (F B - F (tau B)) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) ∂mu)
    at hAnti
  have hMoment :
      (∫ B : Cfg, F B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) ∂mu) =
        -(1 / 8 : ℝ) :=
    p4Q2PZ37AOK_originalOneSlabAction_fixedLeft_primaryCharacter_haar_eq_neg_eighth
      H A
  rw [hMoment] at hAnti
  change (∫ B : Cfg, (F B - F (tau B)) *
    Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) ∂mu) =
      -(1 / 4 : ℝ)
  linarith only [hAnti]

/-- At beta=0 the genuine original Wilson one-slab kernel is exactly one,
so the same coefficient remains -1/4 with the literal flipped kernel present.
This does NOT evaluate the coefficient for positive beta. -/
theorem p4Q2PZ37AON_originalZeroCouplingFlippedKernelGap_primaryHaar_eq_neg_quarter
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    (∫ B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
      p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 (0 : ℝ) A
          (p4Q2PZ37ANV_singleLinkCenterTwist H
            (p4Q2PZ37AMS_primarySpatialSliceEdge H 0) B) *
      Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B)
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
        -(1 / 4 : ℝ) := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let mu := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let tau := p4Q2PZ37ANV_singleLinkCenterTwist H
    (p4Q2PZ37AMS_primarySpatialSliceEdge H 0)
  have hZeroKernel (B : Cfg) :
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 (0 : ℝ) A (tau B) = 1 := by
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    simp
  calc
    (∫ B : Cfg, p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 (0 : ℝ) A (tau B) *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) ∂mu) =
      (∫ B : Cfg, p4Q2PZ37AOH_originalRightCenterTwistActionGap H A B *
        Chi (p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy H 2 B) ∂mu) := by
        apply integral_congr_ae
        filter_upwards [] with B
        rw [hZeroKernel B]
        ring
    _ = -(1 / 4 : ℝ) :=
      p4Q2PZ37AON_originalFixedLeftCenterTwistGap_primaryHaar_eq_neg_quarter H A

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AON_originalFixedLeftCenterTwistGap_primaryHaar_eq_neg_quarter
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AON_originalZeroCouplingFlippedKernelGap_primaryHaar_eq_neg_quarter
