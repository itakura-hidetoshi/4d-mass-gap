import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixSpatialConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 2000000

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Retained information for updating one color on the *left* boundary:
all right-boundary coordinates together with every left coordinate outside the
selected spatial color.  This is the exact left/right counterpart of the
already constructed right-color sigma-algebra. -/
@[reducible] def
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    MeasurableSpace
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  MeasurableSpace.comap Prod.snd inferInstance ⊔
    MeasurableSpace.comap
      (fun z :
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpatialSliceOffColorRestriction color z.1)
      inferInstance

/-- The left-color retained sigma-algebra is contained in the ambient joint
product measurable structure. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N color ≤
      (inferInstance : MeasurableSpace
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)) := by
  apply sup_le
  · exact measurable_snd.comap_le
  · exact
      ((measurable_periodicHypercubicEvenSpecialUnitarySpatialSliceOffColorRestriction
        H N color).comp measurable_fst).comap_le

/-- The complete right-boundary sigma-algebra is retained by every left-color
conditional expectation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointRightMeasurableSpace_le_leftSpatialColor
    (H N : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    MeasurableSpace.comap Prod.snd
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)) ≤
      periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N color := by
  exact le_sup_left

/-- Genuine conditional expectation on the ground-state joint law which
updates one selected spatial color on the left boundary and retains the whole
right boundary. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
  (Submodule.subtypeL
      (lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta))).comp
    (condExpL2 ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
        H N color))

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
        H N hN beta hbeta color f =
      (condExpL2 ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
          H N color) f :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) := by
  rfl

/-- Every genuine left spatial-color conditional expectation is idempotent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_idempotent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
      H N hN beta hbeta color).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
        H N hN beta hbeta color) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
      H N hN beta hbeta color := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_apply]
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
      H N color
  letI : Fact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color ≤
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
    ⟨hm⟩
  let q : lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
    condExpL2 ℝ ℝ hm f
  change
    ((condExpL2 ℝ ℝ hm
      (q : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta)) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) = q
  have hq :
      (condExpL2 ℝ ℝ hm
        (q : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) :
        lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
            H N color) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta)) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q
  exact congrArg
    (fun x : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) =>
      (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)) hq

/-- Every genuine left spatial-color conditional expectation is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
      H N hN beta hbeta color :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta).IsSymmetric := by
  intro f g
  change
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
          H N hN beta hbeta color f) g =
      inner ℝ f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
          H N hN beta hbeta color g)
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_apply]
  exact inner_condExpL2_left_eq_right
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
      H N color)

/-- Every right-boundary pullback is measurable with respect to every left-color
retained sigma-algebra, because the complete right boundary is retained. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry_mem_leftSpatialColor_lpMeas
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (u : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
        H N hN beta hbeta u ∈
      lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  let X := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let π :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let JR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
      H N hN beta hbeta
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  have huMap :
      AEStronglyMeasurable (fun A : X => u A) (Measure.map Prod.snd π) := by
    rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_snd
      H N hN beta hbeta]
    exact Lp.aestronglyMeasurable u
  have hcomp :
      AEStronglyMeasurable[
        MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace X)]
        ((fun A : X => u A) ∘ Prod.snd) π :=
    AEStronglyMeasurable.comp_ae_measurable'
      huMap measurable_snd.aemeasurable
  have hcompColor :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color]
        ((fun A : X => u A) ∘ Prod.snd) π :=
    hcomp.mono
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointRightMeasurableSpace_le_leftSpatialColor
        H N color)
  have hJR : JR u =ᵐ[π] fun z => u z.2 := by
    simpa [JR, Function.comp_def] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving u
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_snd_measurePreserving
          H N hN beta hbeta))
  exact hcompColor.congr hJR.symm

/-- Every genuine left spatial-color conditional expectation fixes the complete
right-boundary subspace. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_rightBoundary_fixed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (u : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
        H N hN beta hbeta color
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
          H N hN beta hbeta u) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
        H N hN beta hbeta u := by
  let hm :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace_le
      H N color
  letI : Fact
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color ≤
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) :=
    ⟨hm⟩
  let q : lpMeas ℝ ℝ
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N color) 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
    ⟨periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
        H N hN beta hbeta u,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry_mem_leftSpatialColor_lpMeas
        H N hN beta hbeta color u⟩
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_apply]
  have hq :
      (condExpL2 ℝ ℝ hm
        (q : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) :
        lpMeas ℝ ℝ
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
            H N color) 2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta)) = q := by
    unfold condExpL2
    exact Submodule.orthogonalProjection_mem_subspace_eq_self q
  have hCoe := congrArg
    (fun x : lpMeas ℝ ℝ
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N color) 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) =>
      (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)) hq
  simpa [q] using hCoe

/-- The six genuine left-boundary spatial conditional expectations. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Fin 6 →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta :=
  fun c =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2
      H N hN beta hbeta
      (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

/-- Each member of the left six-color family is idempotent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2_idempotent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : Fin 6) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
      H N hN beta hbeta c).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
        H N hN beta hbeta c) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
      H N hN beta hbeta c :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_idempotent
    H N hN beta hbeta
    (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

/-- Each member of the left six-color family is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : Fin 6) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
      H N hN beta hbeta c :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta).IsSymmetric :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_symmetric
    H N hN beta hbeta
    (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)

/-- Every left six-color projection fixes every right-boundary lift. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2_rightBoundary_fixed
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : Fin 6)
    (u : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
        H N hN beta hbeta c
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
          H N hN beta hbeta u) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
        H N hN beta hbeta u := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSpatialColorCondExpL2_rightBoundary_fixed
      H N hN beta hbeta
      (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) u

/-- The two-sided spatial color type: six right-boundary updates and six
left-boundary updates.  Using a sum type keeps the two orientations explicit
instead of hiding them in arithmetic on a `Fin 12` index. -/
abbrev PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor : Type :=
  Sum (Fin 6) (Fin 6)

/-- The two-sided family of twelve genuine spatial conditional expectations on
the same ground-state joint `L²` carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta
  | Sum.inl c =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
        H N hN beta hbeta c
  | Sum.inr c =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
        H N hN beta hbeta c

/-- The two-sided spatial color type has exactly twelve members. -/
theorem periodicHypercubicEvenGroundStateTwoSidedSpatialColor_card :
    Fintype.card PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor = 12 := by
  simp [PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor]

/-- Every member of the twelve-color family is idempotent. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_idempotent
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
      H N hN beta hbeta c).comp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta c) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
      H N hN beta hbeta c := by
  cases c with
  | inl c =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_idempotent
          H N hN beta hbeta c
  | inr c =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2_idempotent
          H N hN beta hbeta c

/-- Every member of the twelve-color family is symmetric. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_symmetric
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor) :
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
      H N hN beta hbeta c :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →ₗ[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta).IsSymmetric := by
  cases c with
  | inl c =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_symmetric
          H N hN beta hbeta c
  | inr c =>
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2_symmetric
          H N hN beta hbeta c

/-- A vector is fixed by the full twelve-color family exactly when it is fixed
by both six-color halves.  This exposes the common-fixed geometry needed by the
next joint Poincare step. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_iff
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    (∀ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta c z = z) ↔
      (∀ c : Fin 6,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
          H N hN beta hbeta c z = z) ∧
      (∀ c : Fin 6,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
          H N hN beta hbeta c z = z) := by
  constructor
  · intro h
    constructor
    · intro c
      exact h (Sum.inl c)
    · intro c
      exact h (Sum.inr c)
  · rintro ⟨hright, hleft⟩ c
    cases c with
    | inl c => exact hright c
    | inr c => exact hleft c

end

end MathlibAnalytic
end MGAP4D
