import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOrderedRelativeFrame
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateSixSpatialFrameGap

/-!
# Ordered relative six-color frame to physical-gap receiver

The merged ordered six-color theorem gives a positive, volume-uniform frame
relative to the complete retained left boundary.  This file isolates the one
remaining cross-boundary quantitative input needed to turn that relative frame
into physical top-orthogonal coercivity:

  || E[f(right) | left] ||^2 <= rho ||f||^2,   rho < 1.

No claim that this contraction is already proved is made here.  Given it, exact
projection Pythagoras converts the retained-centered norm into
(1-rho)||x||^2.  The existing six-spatial frame-to-transfer-gap receiver then
closes the finite-volume physical gap.

A scale-uniform receiver is also packaged with explicit uniform bounds q<1/2
for the ordered Schur coefficient and rho<1 for the retained-boundary
contraction.  These are the only new quantitative inputs in that receiver.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype

namespace GroundStateSourceFixedPairEnergy

section FiniteVolume

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
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
local notation "Cleft" =>
  allRightLeftRetainedCondExpL2 H N hN beta hbeta
local notation "P6" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
    H N hN beta hbeta

/-- Specialize the merged all-joint-L2 relative frame to a genuine
right-boundary lift. -/
theorem sixSpatial_ordered_relativePoincare_rightBoundary
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (u : V) :
    ((1 - 2 * jointLeakageSchurCoefficient s beta) ^ 2 / 36) *
        ‖R u - Cleft (R u)‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
        H N hN beta hbeta u := by
  have h :=
    sixSpatial_ordered_relativePoincare H N hN beta hbeta s hs hcut (R u)
  change
    ((1 - 2 * jointLeakageSchurCoefficient s beta) ^ 2 / 36) *
        ‖R u - Cleft (R u)‖ ^ 2 ≤
      groundStateJointColorNormalizedResidualEnergy P6 (R u)
  exact h

/-- If the retained-left projection contracts the transformed physical
top-orthogonal sector by rho<1, the ordered relative frame becomes a genuine
six-spatial physical frame with coefficient
  ((1-2Q)^2/36) * (1-rho).
-/
theorem sixSpatial_ordered_relativeFrame_of_retainedContraction
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ∀ x : K,
      ‖Cleft
        (R
          (U (((x : G) : HaarL2))))‖ ^ 2 ≤
        rho * ‖(x : G)‖ ^ 2)
    (x : K) :
    (((1 - 2 * jointLeakageSchurCoefficient s beta) ^ 2 / 36) * (1 - rho)) *
        ‖(x : G)‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
        H N hN beta hbeta
        (U (((x : G) : HaarL2))) := by
  let u : V := U (((x : G) : HaarL2))
  let q := jointLeakageSchurCoefficient s beta
  let gamma : ℝ := (1 - 2 * q) ^ 2 / 36
  have hq := jointLeakageSchurCoefficient_nonneg_lt_half s hs beta hbeta hcut
  have hgamma0 : 0 ≤ gamma := by
    dsimp [gamma]
    positivity
  have hPyth :
      ‖R u - Cleft (R u)‖ ^ 2 =
        ‖R u‖ ^ 2 - ‖Cleft (R u)‖ ^ 2 := by
    exact realHilbertProjection_residual_norm_sq
      Cleft
      (allRightLeftRetained_idempotent H N hN beta hbeta)
      (allRightLeftRetained_symmetric H N hN beta hbeta)
      (R u)
  have hRunorm : ‖R u‖ ^ 2 = ‖(x : G)‖ ^ 2 := by
    calc
      ‖R u‖ ^ 2 = ‖u‖ ^ 2 :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift_norm_sq
          H N hN beta hbeta u
      _ = ‖(x : G)‖ ^ 2 := by
        have hU :
            ‖u‖ = ‖(x : G)‖ := by
          dsimp [u]
          calc
            ‖U (((x : G) : HaarL2))‖ = ‖(((x : G) : HaarL2))‖ := by
              exact
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
                  H N hN beta hbeta).norm_map _
            _ = ‖(x : G)‖ := rfl
        rw [hU]
  have hcenter :
      (1 - rho) * ‖(x : G)‖ ^ 2 ≤ ‖R u - Cleft (R u)‖ ^ 2 := by
    rw [hPyth, hRunorm]
    have hc : ‖Cleft (R u)‖ ^ 2 ≤ rho * ‖(x : G)‖ ^ 2 := by
      simpa [u] using hcontract x
    nlinarith
  have hrelative :=
    sixSpatial_ordered_relativePoincare_rightBoundary
      H N hN beta hbeta s hs hcut u
  change (gamma * (1 - rho)) * ‖(x : G)‖ ^ 2 ≤ _
  calc
    (gamma * (1 - rho)) * ‖(x : G)‖ ^ 2 =
        gamma * ((1 - rho) * ‖(x : G)‖ ^ 2) := by ring
    _ ≤ gamma * ‖R u - Cleft (R u)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hcenter hgamma0
    _ ≤ _ := by
      simpa [gamma, q, u] using hrelative

/-- The retained-boundary contraction receiver gives a strictly positive
finite-volume physical transfer gap. -/
theorem sixSpatial_ordered_relativeFrame_implies_transferGap_of_retainedContraction
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (rho : ℝ) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ∀ x : K,
      ‖Cleft
        (R
          (U (((x : G) : HaarL2))))‖ ^ 2 ≤
        rho * ‖(x : G)‖ ^ 2) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  let q := jointLeakageSchurCoefficient s beta
  let gamma : ℝ := (1 - 2 * q) ^ 2 / 36
  let kappa : ℝ := gamma * (1 - rho)
  have hq := jointLeakageSchurCoefficient_nonneg_lt_half s hs beta hbeta hcut
  have ha0 : 0 ≤ 1 - 2 * q := by
    dsimp [q]
    linarith [hq.2]
  have ha1 : 1 - 2 * q ≤ 1 := by
    dsimp [q]
    linarith [hq.1]
  have hsquare : (1 - 2 * q) ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ ha0 (by norm_num : (0 : ℝ) ≤ 1)).2 ha1
    simpa using h
  have hgamma0 : 0 ≤ gamma := by
    dsimp [gamma]
    positivity
  have hgamma1 : gamma ≤ 1 := by
    dsimp [gamma]
    nlinarith
  have honeRho0 : 0 ≤ 1 - rho := by linarith
  have honeRho1 : 1 - rho ≤ 1 := by linarith
  have hkappa0 : 0 < kappa := by
    dsimp [kappa, gamma, q]
    have hqpos : 0 < 1 - 2 * jointLeakageSchurCoefficient s beta := by
      linarith [hq.2]
    exact
      mul_pos
        (div_pos (pow_pos hqpos 2) (by norm_num))
        (sub_pos.mpr hrho1)
  have hkappa1 : kappa ≤ 1 := by
    dsimp [kappa]
    calc
      gamma * (1 - rho) ≤ 1 * (1 - rho) :=
        mul_le_mul_of_nonneg_right hgamma1 honeRho0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left honeRho1 (by norm_num)
      _ = 1 := by norm_num
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialFrame_positive_transferGap
      H N hN beta hbeta kappa hkappa0 hkappa1
      (fun x => by
        simpa [kappa, gamma, q] using
          sixSpatial_ordered_relativeFrame_of_retainedContraction
            H N hN beta hbeta s hs hcut rho hrho0 hrho1 hcontract x)

end FiniteVolume

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (s : ℝ) (hs : 8 < s)

/-- Uniform cross-boundary input for the ordered route.

Besides one retained-boundary contraction factor rho<1, this records one
uniform upper bound q<1/2 for the already-defined ordered Schur coefficient.
The cutoff and both quantitative constants precede every scale/vector choice.
-/
def PeriodicHypercubicEvenSpecialUnitaryHasUniformOrderedRetainedBoundaryContraction : Prop :=
  ∃ q rho : ℝ,
    0 ≤ q ∧ q < 1 / 2 ∧
    0 ≤ rho ∧ rho < 1 ∧
    ∀ n : ℕ,
      beta n ≤ jointLeakageLossContractionCutoff s hs ∧
      jointLeakageSchurCoefficient s (beta n) ≤ q ∧
      ∀ x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n),
        ‖allRightLeftRetainedCondExpL2
          (halfExtent n) N hN (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
            (halfExtent n) N hN (beta n) (hbeta n)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
              (halfExtent n) N hN (beta n) (hbeta n)
              (((x :
                periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                  (halfExtent n) N) :
                Lp ℝ 2
                  (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                    (halfExtent n) N)))))‖ ^ 2 ≤
          rho *
            ‖(x :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                (halfExtent n) N)‖ ^ 2

/-- A scale-independent ordered Schur margin and retained-boundary contraction
produce the existing uniform six-spatial frame, hence a uniform physical
transfer gap. -/
theorem periodicHypercubicEvenSpecialUnitary_uniformOrderedRetainedBoundaryContraction_implies_uniformTransferGap
    (hcontract :
      PeriodicHypercubicEvenSpecialUnitaryHasUniformOrderedRetainedBoundaryContraction
        halfExtent N hN beta hbeta s hs) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta := by
  rcases hcontract with ⟨q, rho, hq0, hqhalf, hrho0, hrho1, hall⟩
  let gamma : ℝ := (1 - 2 * q) ^ 2 / 36
  let kappa : ℝ := gamma * (1 - rho)
  have ha0 : 0 ≤ 1 - 2 * q := by linarith
  have ha1 : 1 - 2 * q ≤ 1 := by linarith
  have hsquare : (1 - 2 * q) ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ ha0 (by norm_num : (0 : ℝ) ≤ 1)).2 ha1
    simpa using h
  have hgamma0 : 0 ≤ gamma := by
    dsimp [gamma]
    positivity
  have hgamma1 : gamma ≤ 1 := by
    dsimp [gamma]
    nlinarith
  have honeRho0 : 0 ≤ 1 - rho := by linarith
  have honeRho1 : 1 - rho ≤ 1 := by linarith
  have hkappa0 : 0 < kappa := by
    dsimp [kappa, gamma]
    have hqmargin : 0 < 1 - 2 * q := by linarith
    exact
      mul_pos
        (div_pos (pow_pos hqmargin 2) (by norm_num))
        (sub_pos.mpr hrho1)
  have hkappa1 : kappa ≤ 1 := by
    dsimp [kappa]
    calc
      gamma * (1 - rho) ≤ 1 * (1 - rho) :=
        mul_le_mul_of_nonneg_right hgamma1 honeRho0
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left honeRho1 (by norm_num)
      _ = 1 := by norm_num
  have hframe :
      PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateSixSpatialFrame
        halfExtent N hN beta hbeta := by
    refine ⟨kappa, hkappa0, hkappa1, ?_⟩
    intro n x
    rcases hall n with ⟨hcut, hqn, hret⟩
    have hqActual :=
      jointLeakageSchurCoefficient_nonneg_lt_half
        s hs (beta n) (hbeta n) hcut
    let qn := jointLeakageSchurCoefficient s (beta n)
    let gamman : ℝ := (1 - 2 * qn) ^ 2 / 36
    have hbn0 : 0 ≤ 1 - 2 * q := by linarith
    have han0 : 0 ≤ 1 - 2 * qn := by
      dsimp [qn]
      linarith [hqActual.2]
    have hbase : 1 - 2 * q ≤ 1 - 2 * qn := by
      dsimp [qn]
      linarith
    have hsquares : (1 - 2 * q) ^ 2 ≤ (1 - 2 * qn) ^ 2 :=
      (sq_le_sq₀ hbn0 han0).2 hbase
    have hgamma : gamma ≤ gamman := by
      dsimp [gamma, gamman]
      nlinarith
    have hkappan : kappa ≤ gamman * (1 - rho) := by
      dsimp [kappa]
      exact mul_le_mul_of_nonneg_right hgamma honeRho0
    have hactual :=
      sixSpatial_ordered_relativeFrame_of_retainedContraction
        (halfExtent n) N hN (beta n) (hbeta n)
        s hs hcut rho hrho0 hrho1 hret x
    calc
      kappa *
          ‖(x :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N)‖ ^ 2 ≤
        (gamman * (1 - rho)) *
          ‖(x :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
              (halfExtent n) N)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hkappan (sq_nonneg _)
      _ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
          (halfExtent n) N hN (beta n) (hbeta n)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
            (halfExtent n) N hN (beta n) (hbeta n)
            (((x :
              periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
                (halfExtent n) N) :
              Lp ℝ 2
                (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
                  (halfExtent n) N)))) := by
        simpa [gamman, qn] using hactual
  exact
    periodicHypercubicEvenSpecialUnitary_uniformGroundStateSixSpatialFrame_implies_uniformTransferGap
      halfExtent N hN beta hbeta hframe

end ScalingFamily

end GroundStateSourceFixedPairEnergy

end

end MGAP4D.MathlibAnalytic
