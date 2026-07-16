import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointCoordinateUpdateProfileBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- Rank zero in the complete endpoint-trajectory carrier. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialRankBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Finset.Iic (Fintype.card C.base.geometry.Edge) :=
  ⟨0, Finset.mem_Iic.2 (Nat.zero_le _)⟩

/-- The full rank in the complete endpoint-trajectory carrier. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalRankBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Finset.Iic (Fintype.card C.base.geometry.Edge) :=
  ⟨Fintype.card C.base.geometry.Edge, Finset.mem_Iic.2 le_rfl⟩

@[simp]
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialRankBCF_val
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF.val = 0 :=
  rfl

@[simp]
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalRankBCF_val
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF.val =
      Fintype.card C.base.geometry.Edge :=
  rfl

/-- Updating a trajectory coordinate away from both endpoint ranks leaves the
endpoint transport unchanged. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_eq_of_ne_endpoint_ranks
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (rank : Finset.Iic (Fintype.card C.base.geometry.Edge))
    (g : C.base.Gauge)
    (x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier)
    (hInitial :
      rank ≠ C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF)
    (hFinal :
      rank ≠ C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF) :
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
        target O z (Function.update x rank g) =
      C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
        target O z x := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_eq_fiber_initial_sub_final]
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_eq_fiber_initial_sub_final]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
  have hInitial' :
      C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF ≠ rank :=
    Ne.symm hInitial
  have hFinal' :
      C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF ≠ rank :=
    Ne.symm hFinal
  have hInitialConcrete :
      (⟨0, Finset.mem_Iic.2 (Nat.zero_le _)⟩ :
        Finset.Iic (Fintype.card C.base.geometry.Edge)) ≠ rank := by
    simpa [
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialRankBCF] using hInitial'
  have hFinalConcrete :
      (⟨Fintype.card C.base.geometry.Edge, Finset.mem_Iic.2 le_rfl⟩ :
        Finset.Iic (Fintype.card C.base.geometry.Edge)) ≠ rank := by
    simpa [
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalRankBCF] using hFinal'
  simp only [Function.update, hInitialConcrete, hFinalConcrete, if_false]

/-- Exact endpoint-transport formula after replacing the initial trajectory
coordinate. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_initialRank_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (g : C.base.Gauge)
    (x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier) :
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
        target O z
        (Function.update x
          C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF g) =
      O (C.base.replaceLink
          (C.independentPairHybridConfiguration z.1 z.2 0) target g) -
        C.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
          target O z
          (Function.update x
            C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF g) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_eq_fiber_initial_sub_final]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
  simp [
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialRankBCF]

/-- Exact endpoint-transport formula after replacing the full-rank trajectory
coordinate. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_finalRank_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (g : C.base.Gauge)
    (x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier) :
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
        target O z
        (Function.update x
          C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF g) =
      C.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
          target O z
          (Function.update x
            C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF g) -
        O (C.base.replaceLink
          (C.independentPairHybridConfiguration z.1 z.2
            (Fintype.card C.base.geometry.Edge)) target g) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_eq_fiber_initial_sub_final]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
  simp [
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalRankBCF]

/-- A strict coordinate-update profile located specifically at rank zero. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialUpdateProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  ∃ gLower gUpper : C.base.Gauge,
    ∃ a b : ℝ,
      a < b ∧
      (∀ x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier,
        T (Function.update x
          C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF gLower) ≤ a) ∧
      (∀ y : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier,
        b ≤ T (Function.update y
          C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF gUpper))

/-- A strict coordinate-update profile located specifically at the full rank. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalUpdateProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let T :=
    C.independentPairHybridTargetTrajectoryEndpointFiberTransportBCF target O z
  ∃ gLower gUpper : C.base.Gauge,
    ∃ a b : ℝ,
      a < b ∧
      (∀ x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier,
        T (Function.update x
          C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF gLower) ≤ a) ∧
      (∀ y : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier,
        b ≤ T (Function.update y
          C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF gUpper))

/-- Endpoint-rank update separation: the strict update profile occurs either at
rank zero or at the full trajectory rank. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  C.independentPairHybridTargetTrajectoryEndpointInitialUpdateProfileSeparationWitnessBCF
      target O z ∨
    C.independentPairHybridTargetTrajectoryEndpointFinalUpdateProfileSeparationWitnessBCF
      target O z

/-- Every strict coordinate-update profile must occur at rank zero or at the full
rank, because every other coordinate update leaves endpoint transport unchanged. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_endpoint_rank_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
      target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
    at hWitness
  dsimp only at hWitness
  rcases hWitness with
    ⟨rank, gLower, gUpper, a, b, hab, hLower, hUpper⟩
  have hEndpoint :
      rank = C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF ∨
        rank = C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF := by
    by_contra hNotEndpoint
    have hInitial :
        rank ≠ C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF := by
      intro hrank
      exact hNotEndpoint (Or.inl hrank)
    have hFinal :
        rank ≠ C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF := by
      intro hrank
      exact hNotEndpoint (Or.inr hrank)
    let x0 : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier :=
      fun _ => 1
    have hLower0 := hLower x0
    have hUpper0 := hUpper x0
    rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_eq_of_ne_endpoint_ranks
      C target O z rank gLower x0 hInitial hFinal] at hLower0
    rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_eq_of_ne_endpoint_ranks
      C target O z rank gUpper x0 hInitial hFinal] at hUpper0
    linarith
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
  rcases hEndpoint with hInitial | hFinal
  · left
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialUpdateProfileSeparationWitnessBCF
    dsimp only
    subst rank
    exact ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩
  · right
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalUpdateProfileSeparationWitnessBCF
    dsimp only
    subst rank
    exact ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩

/-- Conversely, either endpoint-rank update profile is a coordinate-update profile. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF_implies_coordinate_update_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
      target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
    at hWitness
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
  dsimp only
  rcases hWitness with hInitial | hFinal
  · unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialUpdateProfileSeparationWitnessBCF
      at hInitial
    dsimp only at hInitial
    rcases hInitial with ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩
    exact
      ⟨C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF,
        gLower, gUpper, a, b, hab, hLower, hUpper⟩
  · unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalUpdateProfileSeparationWitnessBCF
      at hFinal
    dsimp only at hFinal
    rcases hFinal with ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩
    exact
      ⟨C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF,
        gLower, gUpper, a, b, hab, hLower, hUpper⟩

/-- Strict coordinate-update separation is exactly endpoint-rank update
separation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_iff_endpoint_rank_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
        target O z := by
  constructor
  · exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_endpoint_rank_witness
        C target O z
  · exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF_implies_coordinate_update_witness
        C target O z

/-- On a Hausdorff compact Gauge space, endpoint-rank update separation produces
nonempty open cross-cylinder innovation regions. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF_implies_open_region_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_open_region_witness
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF_implies_coordinate_update_witness
        C target O z hWitness)

/-- Endpoint-rank update separation forces positive fixed-fiber conditional
variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_implies_gap_pos
      C target O z
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF_implies_coordinate_update_witness
        C target O z hWitness)

/-- A non-null Gibbs-pair family carrying endpoint-rank update separation. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
      target O z

/-- A non-null endpoint-rank update family supplies the previous coordinate-update
witness family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_fiberwise_coordinate_update_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF
      target O := by
  exact hWitness.mono fun z hz =>
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF_implies_coordinate_update_witness
      C target O z hz

/-- A non-null endpoint-rank update family forces positive global conditional
variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_gap_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_fiberwise_coordinate_update_witness
        C target O hWitness)

/-- With positive native energy, a non-null endpoint-rank update family forces the
exact endpoint correlation ratio below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_correlationRatio_lt_one
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_fiberwise_coordinate_update_witness
        C target O hWitness)

/-- With positive native energy, a non-null endpoint-rank update family produces a
strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseCoordinateUpdateProfileSeparationWitnessBCF_implies_exists_strict_correlation_factor
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_fiberwise_coordinate_update_witness
        C target O hWitness)

end

end MathlibAnalytic
end MGAP4D
