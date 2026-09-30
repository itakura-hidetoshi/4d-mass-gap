import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPhysicalOrthogonalKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedConstantLineConvergence
import Mathlib.Tactic

/-!
# Physical top-orthogonal lifts are exactly centered at the intrinsic constant line

This is G2.

The existing physical-kernel file already identifies the transformed positive
top vector after right-boundary lift with the intrinsic joint constant-one
vector.  Here we use the actual Hilbert geometry rather than a name-level
identification:

* a physical vector in the orthogonal complement of the full top eigenspace is
  orthogonal to the chosen positive top vector;
* the Haar-to-vacuum map and right-boundary pullback are linear isometries, so
  that orthogonality transports to the genuine joint carrier;
* the resulting right-boundary lift is orthogonal to the intrinsic constant
  line;
* therefore the intrinsic constant-line orthogonal projection vanishes;
* the constant-centered norm is exactly the original physical-sector norm.

No simplicity of the top eigenspace and no qualitative kernel argument is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

local instance physicalTopOrthogonalCenteringSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalTopOrthogonalCenteringSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalTopOrthogonalCenteringSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalTopOrthogonalCenteringSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalTopOrthogonalCenteringSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalTopOrthogonalCenteringSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

section FiniteVolume

variable (H N : ℕ)
variable (hN : 0 < N)
variable (beta : ℝ)
variable (hbeta : 0 ≤ beta)

local instance physicalTopOrthogonalCenteringVacuumProbability :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure_isProbabilityMeasure
    H N hN beta hbeta

local instance physicalTopOrthogonalCenteringJointProbability :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "F" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
    H N hN beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta
local notation "J" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN beta hbeta
local notation "JR" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
    H N hN beta hbeta
local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta
local notation "C" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    H N hN beta hbeta
local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta
local notation "oneJ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
    H N hN beta hbeta 1

local instance physicalTopOrthogonalCenteringConstantLineHasOrthogonalProjection :
    C.HasOrthogonalProjection := by
  let C' := C
  change C'.HasOrthogonalProjection
  letI : FiniteDimensional ℝ C' := by
    unfold C'
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    infer_instance
  letI : CompleteSpace C' := FiniteDimensional.complete ℝ C'
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace C'

/-- The canonical positive top vector belongs to the full normalized physical
top eigenspace.  This packages the calculation already used in the qualitative
physical-kernel proof. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_mem_topEigenspace :
    Omega ∈ F := by
  have hnorm :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem]
  rw [periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen]
  rw [smul_smul, inv_mul_cancel₀ hnorm.ne', one_smul]

/-- A physical top-orthogonal vector stays orthogonal to the intrinsic
constant-one vector after the exact ground-state transform and right-boundary
isometric lift. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_topOrthogonal_inner_constant_one_eq_zero
    (x : K) :
    inner ℝ oneJ (R (U (((x : G) : HaarL2)))) = 0 := by
  have hxOrth : (x : G) ∈ Fᗮ := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal] using
      x.property
  have hOmegaF : Omega ∈ F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_mem_topEigenspace
      H N hN beta hbeta
  have hPhysical :
      inner ℝ (Omega : G) (x : G) = 0 :=
    (Submodule.mem_orthogonal F (x : G)).1 hxOrth Omega hOmegaF
  have hHaar :
      inner ℝ (((Omega : G) : HaarL2)) (((x : G) : HaarL2)) = 0 := by
    simpa using hPhysical
  rw [←
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_nonnegativeTop_eq_constantL2_one
      H N hN beta hbeta]
  calc
    inner ℝ
        (R (U ((Omega : G) : HaarL2)))
        (R (U (((x : G) : HaarL2)))) =
      inner ℝ
        (U ((Omega : G) : HaarL2))
        (U (((x : G) : HaarL2))) := by
          change
            inner ℝ
                (JR (U ((Omega : G) : HaarL2)))
                (JR (U (((x : G) : HaarL2)))) =
              _
          exact JR.inner_map_map _ _
    _ =
      inner ℝ (((Omega : G) : HaarL2)) (((x : G) : HaarL2)) :=
        U.inner_map_map _ _
    _ = 0 := hHaar

/-- The transformed physical top-orthogonal right-boundary lift belongs to the
orthogonal complement of the intrinsic joint constant line. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_topOrthogonal_mem_constantLine_orthogonal
    (x : K) :
    R (U (((x : G) : HaarL2))) ∈ Cᗮ := by
  have hinner :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_topOrthogonal_inner_constant_one_eq_zero
      H N hN beta hbeta x
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine] using
    (Submodule.mem_orthogonal_singleton_iff_inner_right
      (𝕜 := ℝ)
      (u := oneJ)
      (v := R (U (((x : G) : HaarL2))))).2 hinner

/-- G2a: the intrinsic joint constant-line projection vanishes exactly on every
right-boundary lift of the physical full-top-orthogonal sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_rightBoundary_topOrthogonal_eq_zero
    (x : K) :
    B (R (U (((x : G) : HaarL2)))) = 0 := by
  let z : J := R (U (((x : G) : HaarL2)))
  have hzOrth : z ∈ Cᗮ := by
    simpa [z] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_topOrthogonal_mem_constantLine_orthogonal
        H N hN beta hbeta x
  have hBmem : B z ∈ C := by
    change C.starProjection z ∈ C
    exact C.starProjection_apply_mem z
  have hrem : z - B z ∈ Cᗮ := by
    change z - C.starProjection z ∈ Cᗮ
    exact C.sub_starProjection_mem_orthogonal z
  have hBorth : B z ∈ Cᗮ := by
    have hsub := Cᗮ.sub_mem hzOrth hrem
    simpa only [sub_sub_cancel] using hsub
  have hbot : B z ∈ (⊥ : Submodule ℝ J) := by
    exact C.orthogonal_disjoint.le_bot ⟨hBmem, hBorth⟩
  have hzero : B z = 0 := by
    simpa using hbot
  simpa [z] using hzero

/-- G2b: after subtracting the intrinsic constant projection, the genuine joint
right-boundary lift has exactly the norm of the original physical
top-orthogonal vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_topOrthogonal_constantCentered_norm_eq
    (x : K) :
    ‖R (U (((x : G) : HaarL2))) -
        B (R (U (((x : G) : HaarL2))))‖ =
      ‖x‖ := by
  have hBzero :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_rightBoundary_topOrthogonal_eq_zero
      H N hN beta hbeta x
  have hRnorm :
      ‖R (U (((x : G) : HaarL2)))‖ =
        ‖U (((x : G) : HaarL2))‖ := by
    change
      ‖JR (U (((x : G) : HaarL2)))‖ =
        ‖U (((x : G) : HaarL2))‖
    exact JR.norm_map _
  have hUnorm :
      ‖U (((x : G) : HaarL2))‖ =
        ‖(((x : G) : HaarL2))‖ :=
    U.norm_map _
  rw [hBzero, sub_zero, hRnorm, hUnorm]
  rfl

/-- Squared-norm form used directly by the twelve-spatial Poincare receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_topOrthogonal_constantCentered_norm_sq_eq
    (x : K) :
    ‖R (U (((x : G) : HaarL2))) -
        B (R (U (((x : G) : HaarL2))))‖ ^ 2 =
      ‖x‖ ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_topOrthogonal_constantCentered_norm_eq
      H N hN beta hbeta x]

end FiniteVolume

end

end MathlibAnalytic
end MGAP4D
