import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialRelativeFrame
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPhysicalOrthogonalKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap
import Mathlib.Tactic

/-!
# From the intrinsic constant center to the physical top-orthogonal sector

PR #4980 proves a volume/rank-independent twelve-spatial relative Poincare
inequality around the intrinsic constant line on the genuine ground-state joint
L2 carrier.

This file closes G2 and the finite-volume part of G3.

For a physical vector in the orthogonal complement of the FULL normalized
transfer top eigenspace, the ground-state transform followed by the genuine
right-boundary lift is orthogonal to the intrinsic joint constant line.  The
reason is exact:

* the nonnegative physical top eigenvector belongs to the full top eigenspace;
* the Haar-to-vacuum transform sends it to constant one;
* the right-boundary isometry sends that vector to the intrinsic joint
  constant-one vector;
* both maps preserve inner products.

Therefore the intrinsic constant projection of the lifted excitation is zero,
and its centered joint norm is exactly the original physical norm.  Feeding
#4980 into the already-existing conventional twelve-spatial receiver gives an
explicit positive-beta finite-volume transfer-gap lower bound.

No simplicity of the top eigenspace and no identification by name of distinct
vacuum/constant/top spaces is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance twoSidedTwelvePhysicalGapSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoSidedTwelvePhysicalGapSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance twoSidedTwelvePhysicalGapSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoSidedTwelvePhysicalGapSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoSidedTwelvePhysicalGapSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance twoSidedTwelvePhysicalGapSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

section FiniteVolume

variable (H N : ℕ)
variable (hN : 0 < N)
variable (beta : ℝ)
variable (hbeta : 0 ≤ beta)

local instance twoSidedTwelvePhysicalGapConstantLineHasOrthogonalProjection :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta).HasOrthogonalProjection := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  change C.HasOrthogonalProjection
  letI : FiniteDimensional ℝ C := by
    unfold C
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    infer_instance
  letI : CompleteSpace C := FiniteDimensional.complete ℝ C
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace C

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

local notation "V" =>
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateVacuumL2
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

local notation "B" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta

local notation "Omega" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H N hN beta hbeta

/-- The distinguished nonnegative physical top eigenvector belongs to the full
normalized-transfer top eigenspace.  This does not assert simplicity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_mem_topEigenspace :
    Omega ∈ F := by
  have hnorm :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem]
  rw [
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_apply,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen]
  rw [smul_smul, inv_mul_cancel₀ hnorm.ne', one_smul]

/-- A physical top-orthogonal vector stays orthogonal to constant one after
the two exact isometric transports into the genuine joint carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_topOrthogonal_inner_constantL2_one_eq_zero
    (x : K) :
    inner ℝ
        (R (U (((x : G) : HaarL2))))
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
          H N hN beta hbeta 1) = 0 := by
  let JR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
      H N hN beta hbeta
  have hxOrth : (x : G) ∈ Fᗮ := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal] using
      x.property
  rw [Submodule.mem_orthogonal] at hxOrth
  have hOmegaF : Omega ∈ F :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_mem_topEigenspace
      H N hN beta hbeta
  have hOmegaX : inner ℝ (Omega : G) (x : G) = 0 :=
    hxOrth Omega hOmegaF
  have hLift :
      inner ℝ
          (JR (U ((Omega : G) : HaarL2)))
          (JR (U (((x : G) : HaarL2)))) = 0 := by
    calc
      inner ℝ
          (JR (U ((Omega : G) : HaarL2)))
          (JR (U (((x : G) : HaarL2)))) =
        inner ℝ
          (U ((Omega : G) : HaarL2))
          (U (((x : G) : HaarL2))) :=
        JR.inner_map_map _ _
      _ = inner ℝ ((Omega : G) : HaarL2) (((x : G) : HaarL2) :=
        U.inner_map_map _ _
      _ = inner ℝ (Omega : G) (x : G) := rfl
      _ = 0 := hOmegaX
  have hTopConst :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_nonnegativeTop_eq_constantL2_one
      H N hN beta hbeta
  have hLift' :
      inner ℝ
          (R (U ((Omega : G) : HaarL2)))
          (R (U (((x : G) : HaarL2)))) = 0 := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift,
      JR] using hLift
  rw [← hTopConst]
  rw [real_inner_comm]
  exact hLift'

/-- G2 core identity: the intrinsic joint constant projection annihilates every
ground-state transformed right-boundary lift of the FULL physical
top-orthogonal sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_rightBoundary_topOrthogonal_eq_zero
    (x : K) :
    B (R (U (((x : G) : HaarL2)))) = 0 := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  let z : J := R (U (((x : G) : HaarL2)))
  have hInner :
      inner ℝ z
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
          H N hN beta hbeta 1) = 0 := by
    simpa [z] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundary_topOrthogonal_inner_constantL2_one_eq_zero
        H N hN beta hbeta x
  change C.starProjection z = 0
  apply ext_inner_right ℝ
  intro g
  have hMem : C.starProjection g ∈ C :=
    C.starProjection_apply_mem g
  change
    C.starProjection g ∈
      (ℝ ∙
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
          H N hN beta hbeta 1) at hMem
  rcases Submodule.mem_span_singleton.mp hMem with ⟨c, hc⟩
  calc
    inner ℝ (C.starProjection z) g =
        inner ℝ z (C.starProjection g) :=
      Submodule.inner_starProjection_left_eq_right C z g
    _ =
        inner ℝ z
          (c •
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
              H N hN beta hbeta 1) := by
      rw [hc]
    _ = c * inner ℝ z
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantL2
            H N hN beta hbeta 1) := by
      rw [real_inner_smul_right]
    _ = 0 := by rw [hInner, mul_zero]
    _ = inner ℝ (0 : J) g := by simp

/-- On the physical top-orthogonal sector, constant-centering of the genuine
joint right-boundary lift changes nothing and the squared norm is exactly the
original physical squared norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantCenteredNormSq_rightBoundary_topOrthogonal_eq_physical
    (x : K) :
    ‖R (U (((x : G) : HaarL2))) -
        B (R (U (((x : G) : HaarL2))))‖ ^ 2 =
      ‖(x : G)‖ ^ 2 := by
  let JR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryL2Isometry
      H N hN beta hbeta
  have hB :
      B (R (U (((x : G) : HaarL2)))) = 0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_rightBoundary_topOrthogonal_eq_zero
      H N hN beta hbeta x
  have hRnorm :
      ‖R (U (((x : G) : HaarL2)))‖ =
        ‖U (((x : G) : HaarL2))‖ := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift,
      JR] using
      JR.norm_map (U (((x : G) : HaarL2)))
  have hUnorm :
      ‖U (((x : G) : HaarL2))‖ =
        ‖((x : G) : HaarL2)‖ :=
    U.norm_map _
  rw [hB, sub_zero, hRnorm, hUnorm]
  rfl

namespace GroundStateSourceFixedPairEnergy

/-- The G1 coefficient is automatically far below the receiver's harmless
normalization threshold one half. -/
theorem twoSidedTwelveSpatialRelativeFrameCoefficient_le_half
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ twoSidedTwelveSpatialFrameCutoff s hs) :
    twoSidedTwelveSpatialRelativeFrameCoefficient s beta ≤ 1 / 2 := by
  have hcutTwo :
      beta ≤ twoBoundaryOrderedLossContractionCutoff s hs :=
    hcut.trans
      (twoSidedTwelveSpatialFrameCutoff_le_twoBoundary s hs)
  have hEta :=
    twoBoundaryOrderedLossRatio_nonneg_lt_one
      s hs beta hbeta hcutTwo
  let r := Real.sqrt (twoBoundaryOrderedLossRatio s beta)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = twoBoundaryOrderedLossRatio s beta := by
    dsimp [r]
    exact Real.sq_sqrt hEta.1
  have hr1 : r < 1 := by
    nlinarith [hEta.2, hrSq]
  have hOneMinus0 : 0 ≤ 1 - r := by
    linarith
  have hOneMinus1 : 1 - r ≤ 1 := by
    linarith
  have hSquare : (1 - r) ^ 2 ≤ 1 := by
    nlinarith
  unfold twoSidedTwelveSpatialRelativeFrameCoefficient
  change (1 - r) ^ 2 / 576 ≤ 1 / 2
  nlinarith

end GroundStateSourceFixedPairEnergy

/-- G2 -> G3 bridge: #4980 becomes an ordinary conventional twelve-spatial
Poincare inequality on the actual physical top-orthogonal right-boundary
lifts, with exactly the same volume-free coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialPoincare_on_topOrthogonal
    (s : ℝ)
    (hs : 8 < s)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs)
    (x : K) :
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
          s beta *
        ‖(x : G)‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
        H N hN beta hbeta
        (R (U (((x : G) : HaarL2)))) := by
  have hFrame :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatial_ordered_relativePoincare
      H N hN beta hbeta s hs hcut
      (R (U (((x : G) : HaarL2))))
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantCenteredNormSq_rightBoundary_topOrthogonal_eq_physical
      H N hN beta hbeta x] at hFrame
  exact hFrame

/-- G3 finite-volume endpoint: the G1/G2 coefficient gives the explicit
positive-beta physical transfer-gap lower bound through the already-existing
twelve-spatial receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialRelativeFrame_implies_transferGap
    (s : ℝ)
    (hs : 8 < s)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs) :
    3 *
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
            s beta / 4 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  let kappa :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
      s beta
  have hkappaPos :
      0 < kappa := by
    dsimp [kappa]
    exact
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient_pos
        s hs beta hbeta hcut
  have hkappaHalf :
      kappa ≤ 1 / 2 := by
    dsimp [kappa]
    exact
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient_le_half
        s hs beta hbeta hcut
  have hPoincare :
      ∀ x : K,
        kappa * ‖(x : G)‖ ^ 2 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
            H N hN beta hbeta
            (R (U (((x : G) : HaarL2)))) := by
    intro x
    simpa [kappa] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialPoincare_on_topOrthogonal
        H N hN beta hbeta s hs hcut x
  simpa [kappa] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialPoincare_implies_transferGap
      H N hN beta hbeta
      kappa hkappaPos.le hkappaHalf hPoincare

/-- In particular, the certified high-temperature interval from G1 has a
strictly positive physical transfer gap at every finite volume and rank. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialRelativeFrame_positive_transferGap
    (s : ℝ)
    (hs : 8 < s)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff s hs) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have hkappa :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient_pos
      s hs beta hbeta hcut
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialRelativeFrame_implies_transferGap
      H N hN beta hbeta s hs hcut
  have hpos :
      0 <
        3 *
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
            s beta / 4 := by
    positivity
  exact lt_of_lt_of_le hpos hgap

end FiniteVolume

end

end MathlibAnalytic
end MGAP4D
