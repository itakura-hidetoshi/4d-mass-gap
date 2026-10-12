import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLeftFiberHilbertL2DefectSwap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSimpleCoreFubiniDensityBridge
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

/-!
# P4-Q2-DM: original pair-Haar endpoint swap interwines left/right L² projections

DL represents the original Wilson LEFT link Haar reference as the genuine
CR right-link Hilbert defect after swapping the real left/right physical
boundary configurations. We prove that the endpoint swap actually
preserves the ORIGINAL independent pair-Haar law and induces a genuine
real L² linear isometry U.

The ORIGINAL coordinate Haar averaging operators obey a pointwise
swap/right/left identity, proved directly on the measurable joint spatial
configuration using the actual finite-product coordinate equivalence
and Function.update. DA then identifies this literal Haar mean with the
real CR orthogonal conditional expectation on each bounded
strongly-measurable L² representative.

We finally extend the intertwining from that physical bounded
simple-function core to ALL actual pair-Haar Hilbert-L² vectors by the
already proved CW dense-core theorem and continuous linear operator
equality:

  P_right,i ∘ U = U ∘ P_left,i.

No interacting Wilson conditional projections are claimed to commute.
No substitute physical measure, additional axioms, or spectral/continuum
mass-gap claim enters this theorem.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section ActualPairHaar
variable (H N : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "G" => Matrix.specialUnitaryGroup (Fin N) ℂ
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N
local notation "Mean" => p4Q2CU_actualPairHaarCoordinateMean H N

/-- The physical left/right boundary swap genuinely preserves the SAME
original independent spatial pair-Haar probability measure. -/
theorem p4Q2DM_originalPairHaar_swap_measurePreserving :
    MeasurePreserving (Prod.swap : Joint → Joint) muPair muPair := by
  change MeasurePreserving (Prod.swap : Joint → Joint)
    ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
  exact MeasureTheory.Measure.measurePreserving_swap

/-- The authentic boundary swap on the original pair-Haar Hilbert space,
not a Wilson-interacting conditional projection or a proxy operator. -/
noncomputable def p4Q2DM_originalPairHaarSwapL2 : JH →ₗᵢ[ℝ] JH :=
  Lp.compMeasurePreservingₗᵢ ℝ
    (Prod.swap : Joint → Joint)
    (p4Q2DM_originalPairHaar_swap_measurePreserving H N)

/-- The spatial left link update is exactly the left summand update
of the physical joint measurable-coordinate equivalence. -/
theorem p4Q2DM_leftUpdate_eq_jointCoordinateUpdate
    (target : Link) (z : Joint) (u : G) :
    (Function.update z.1 target u, z.2) =
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
        H N).symm
        (Function.update
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
            H N z) (Sum.inl target) u) := by
  classical
  apply Prod.ext
  · funext j
    change (Function.update z.1 target u) j =
      (Function.update
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N z) (Sum.inl target) u) (Sum.inl j)
    by_cases hj : j = target
    · subst j
      simp
    · simp [hj]
  · funext j
    change z.2 j =
      (Function.update
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N z) (Sum.inl target) u) (Sum.inr j)
    simp

/-- Original literal Haar coordinate means intertwine with physical
endpoint swap POINTWISE on all original configurations, before L². -/
theorem p4Q2DM_actualCoordinateHaarMean_swap
    (target : Link) (F : Joint → ℝ) (z : Joint) :
    Mean (Sum.inr target) (fun w : Joint => F w.swap) z =
      Mean (Sum.inl target) F z.swap := by
  classical
  unfold p4Q2CU_actualPairHaarCoordinateMean
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    have hr :=
      p4Q2DK_rightUpdate_eq_jointCoordinateUpdate H N target z u
    have hl :=
      p4Q2DM_leftUpdate_eq_jointCoordinateUpdate H N target z.swap u
    change
      F ((periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N).symm
          (Function.update
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
              H N z) (Sum.inr target) u)).swap =
        F ((periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
          H N).symm
          (Function.update
            (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialCoordinateMeasurableEquiv
              H N z.swap) (Sum.inl target) u))
    rw [← hr, ← hl]
    rfl

/-- The actual swapped pair-Haar L² vector is represented almost
everywhere by composing any original representative with the literal
physical left/right swap; no quotient representatives are evaluated
on exceptional fibers. -/
theorem p4Q2DM_originalPairHaarSwapL2_ae
    (f : JH) :
    ((p4Q2DM_originalPairHaarSwapL2 H N f : JH) : Joint → ℝ) =ᵐ[muPair]
      (fun z : Joint => (f : Joint → ℝ) z.swap) := by
  change
    ((Lp.compMeasurePreserving
      (Prod.swap : Joint → Joint)
      (p4Q2DM_originalPairHaar_swap_measurePreserving H N) f : JH) :
        Joint → ℝ) =ᵐ[muPair]
      (fun z : Joint => (f : Joint → ℝ) z.swap)
  exact Lp.coeFn_compMeasurePreserving f
    (p4Q2DM_originalPairHaar_swap_measurePreserving H N)

/-- Core-level Hilbert intertwining for any bounded strongly measurable
physical representative F of the genuine pair-Haar L² class f. -/
theorem p4Q2DM_actualPairHaarProjection_swap_on_boundedRepresentative
    (target : Link) (f : JH)
    (F : Joint → ℝ) (hF : StronglyMeasurable F)
    (M : ℝ) (hM : ∀ z, ‖F z‖ ≤ M)
    (hEq : F =ᵐ[muPair] (f : Joint → ℝ)) :
    P (Sum.inr target) (p4Q2DM_originalPairHaarSwapL2 H N f) =
      p4Q2DM_originalPairHaarSwapL2 H N (P (Sum.inl target) f) := by
  let U := p4Q2DM_originalPairHaarSwapL2 H N
  let Fswap : Joint → ℝ := fun z => F z.swap
  have hFswap : StronglyMeasurable Fswap :=
    hF.comp_measurable measurable_swap
  have hBoundSwap : ∀ z : Joint, ‖Fswap z‖ ≤ M :=
    fun z => hM z.swap
  have hUa := p4Q2DM_originalPairHaarSwapL2_ae H N f
  have hPull :
      Fswap =ᵐ[muPair] (fun z : Joint => (f : Joint → ℝ) z.swap) := by
    simpa only [Fswap, Function.comp_def] using
      (p4Q2DM_originalPairHaar_swap_measurePreserving H N).quasiMeasurePreserving.ae_eq hEq
  have hEqSwap :
      Fswap =ᵐ[muPair] ((U f : JH) : Joint → ℝ) :=
    hPull.trans hUa.symm
  have hRight :=
    p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
      H N (Sum.inr target) (U f) Fswap hFswap M hBoundSwap hEqSwap
  have hLeft :=
    p4Q2DA_actualPairHaarProjection_ae_eq_CUmean
      H N (Sum.inl target) f F hF M hM hEq
  have hLeftSwap :
      (fun z : Joint =>
        ((P (Sum.inl target) f : JH) : Joint → ℝ) z.swap) =ᵐ[muPair]
      (fun z : Joint => Mean (Sum.inl target) F z.swap) := by
    simpa only [Function.comp_def] using
      (p4Q2DM_originalPairHaar_swap_measurePreserving H N).quasiMeasurePreserving.ae_eq hLeft
  have hULeft :=
    p4Q2DM_originalPairHaarSwapL2_ae H N (P (Sum.inl target) f)
  apply Lp.ext
  filter_upwards [hRight, hLeftSwap, hULeft] with z hz hls hu
  calc
    ((P (Sum.inr target) (U f) : JH) : Joint → ℝ) z =
      Mean (Sum.inr target) Fswap z := hz
    _ = Mean (Sum.inl target) F z.swap :=
      p4Q2DM_actualCoordinateHaarMean_swap H N target F z
    _ = ((P (Sum.inl target) f : JH) : Joint → ℝ) z.swap := hls.symm
    _ = ((U (P (Sum.inl target) f) : JH) : Joint → ℝ) z := hu.symm

/-- The ORIGINAL pair-Haar left/right coordinate orthogonal
projections intertwine with genuine endpoint swap on the ENTIRE
physical Hilbert-L², not only on bounded or simple representatives. -/
theorem p4Q2DM_actualPairHaarProjection_swap_intertwining
    (target : Link) (f : JH) :
    P (Sum.inr target) (p4Q2DM_originalPairHaarSwapL2 H N f) =
      p4Q2DM_originalPairHaarSwapL2 H N (P (Sum.inl target) f) := by
  let U := p4Q2DM_originalPairHaarSwapL2 H N
  have hCore : ∀ s : Lp.simpleFunc ℝ 2 muPair,
      P (Sum.inr target) (U (s : JH)) =
        U (P (Sum.inl target) (s : JH)) := by
    intro s
    obtain ⟨F, M, hF, hM, hEq⟩ :=
      p4Q2CW_actualPairHaarSimpleCore_boundedRepresentative H N s
    exact p4Q2DM_actualPairHaarProjection_swap_on_boundedRepresentative
      H N target (s : JH) F hF M hM hEq
  have hs : Dense (Lp.simpleFunc ℝ 2 muPair : Set JH) :=
    p4Q2CW_actualPairHaarSimpleCore_dense H N
  have hspan : Dense
      (↑(Submodule.span ℝ (Lp.simpleFunc ℝ 2 muPair : Set JH)) : Set JH) :=
    hs.mono (Submodule.subset_span)
  have heq :
      (P (Sum.inr target)).comp U.toContinuousLinearMap =
        U.toContinuousLinearMap.comp (P (Sum.inl target)) := by
    apply ContinuousLinearMap.ext_on hspan
    intro x hx
    change x ∈ (Lp.simpleFunc ℝ 2 muPair : Set JH) at hx
    simpa only [ContinuousLinearMap.comp_apply] using
      hCore ⟨x, hx⟩
  exact congrArg (fun T : JH →L[ℝ] JH => T f) heq

end ActualPairHaar
end

end MathlibAnalytic
end MGAP4D
