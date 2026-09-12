import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointCoordinateProfileSeparationBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- A strict endpoint-transport profile expressed by replacing one complete
trajectory coordinate while leaving every other coordinate unchanged. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  ∃ rank : Finset.Iic (Fintype.card C.base.geometry.Edge),
    ∃ gLower gUpper : C.base.Gauge,
      ∃ a b : ℝ,
        a < b ∧
        (∀ x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier,
          T (Function.update x rank gLower) ≤ a) ∧
        (∀ y : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier,
          b ≤ T (Function.update y rank gUpper))

/-- A uniform coordinate-update profile supplies the strict coordinate-fiber
profile from the previous layer. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_coordinate_profile_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF
      target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
    at hWitness
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF
  dsimp only at hWitness ⊢
  rcases hWitness with
    ⟨rank, gLower, gUpper, a, b, hab, hLowerUpdate, hUpperUpdate⟩
  refine ⟨rank, gLower, gUpper, a, b, hab, ?_, ?_⟩
  · intro x hx
    have hBound := hLowerUpdate x
    have hUpdate : Function.update x rank gLower = x := by
      funext i
      by_cases hi : i = rank
      · subst i
        simp [hx]
      · simp [Function.update, hi]
    rw [hUpdate] at hBound
    exact hBound
  · intro y hy
    have hBound := hUpperUpdate y
    have hUpdate : Function.update y rank gUpper = y := by
      funext i
      by_cases hi : i = rank
      · subst i
        simp [hy]
      · simp [Function.update, hi]
    rw [hUpdate] at hBound
    exact hBound

/-- On a Hausdorff compact Gauge space, a uniform coordinate-update profile
produces two nonempty open Gauge regions with cross-cylinder endpoint separation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_open_region_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_open_region_witness
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_coordinate_profile_witness
        C target O z hWitness)

/-- A strict coordinate-update profile forces positive endpoint innovation mass
on the fixed original-pair fiber. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_innovationMass_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberInnovationMassBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_innovationMass_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_coordinate_profile_witness
        C target O z hWitness)

/-- A strict coordinate-update profile forces positive fixed-fiber conditional
variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_gap_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_coordinate_profile_witness
        C target O z hWitness)

/-- A strict coordinate-update profile forces positive fixed-fiber iid double
endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateProfileSeparationWitnessBCF_implies_double_energy_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_coordinate_profile_witness
        C target O z hWitness)

/-- A non-null Gibbs-pair family carrying strict coordinate-update profiles. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
      target O z

/-- A non-null family of strict coordinate-update profiles produces the
coordinate-profile witness family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_fiberwise_coordinate_profile_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF
      target O := by
  exact hWitness.mono fun z hz =>
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_coordinate_profile_witness
      C target O z hz

/-- A non-null family of strict coordinate-update profiles forces positive global
conditional variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_gap_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_fiberwise_coordinate_profile_witness
        C target O hWitness)

/-- A non-null family of strict coordinate-update profiles forces positive global
iid double endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_double_energy_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_double_energy_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_fiberwise_coordinate_profile_witness
        C target O hWitness)

/-- With positive native energy, a non-null family of strict coordinate-update
profiles forces the exact endpoint correlation ratio below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_correlationRatio_lt_one
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_fiberwise_coordinate_profile_witness
        C target O hWitness)

/-- With positive native energy, a non-null family of strict coordinate-update
profiles produces a strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateProfileSeparationWitnessBCF_implies_exists_strict_correlation_factor
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_fiberwise_coordinate_profile_witness
        C target O hWitness)

end

end MathlibAnalytic
end MGAP4D
