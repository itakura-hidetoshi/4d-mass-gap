import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointUpdateRankReductionBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators ENNReal

noncomputable section

/-- The rank-zero endpoint insertion profile as a function of the inserted Gauge
value. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (g : C.base.Gauge) : ℝ :=
  O (C.base.replaceLink
    (C.independentPairHybridConfiguration z.1 z.2 0) target g)

/-- The full-rank endpoint insertion profile as a function of the inserted Gauge
value. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (g : C.base.Gauge) : ℝ :=
  O (C.base.replaceLink
    (C.independentPairHybridConfiguration z.1 z.2
      (Fintype.card C.base.geometry.Edge)) target g)

/-- The initial insertion profile is continuous on the compact Gauge space. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    Continuous
      (C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
        target O z) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
  exact O.continuous.comp
    ((continuous_compact_oriented_replaceLink_uncurry C target).comp
      (continuous_const.prodMk continuous_id))

/-- The final insertion profile is continuous on the compact Gauge space. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    Continuous
      (C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
        target O z) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
  exact O.continuous.comp
    ((continuous_compact_oriented_replaceLink_uncurry C target).comp
      (continuous_const.prodMk continuous_id))

/-- The existence of the target edge forces rank zero and the full trajectory rank
to be distinct. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialRankBCF_ne_finalRankBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF ≠
      C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF := by
  intro hRanks
  have hVal := congrArg Subtype.val hRanks
  change 0 = Fintype.card C.base.geometry.Edge at hVal
  have hCard : 0 < Fintype.card C.base.geometry.Edge :=
    Fintype.card_pos_iff.mpr ⟨target⟩
  exact (Nat.ne_of_lt hCard) hVal

/-- After updating rank zero, endpoint transport is exactly the initial insertion
profile at the new value minus the final insertion profile at the unchanged final
coordinate. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_initialRank_eq_insertion_profiles
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
      C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
          target O z g -
        C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
          target O z
          (x C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF) := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_initialRank_eq]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberFinalObservableBCF
  have hCard : 0 < Fintype.card C.base.geometry.Edge :=
    Fintype.card_pos_iff.mpr ⟨target⟩
  have hCardNe : Fintype.card C.base.geometry.Edge ≠ 0 :=
    Nat.ne_of_gt hCard
  simp [Function.update,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialRankBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalRankBCF,
    hCardNe, Ne.symm hCardNe]

/-- After updating the full rank, endpoint transport is exactly the initial
insertion profile at the unchanged initial coordinate minus the final insertion
profile at the new value. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_finalRank_eq_insertion_profiles
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
      C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
          target O z
          (x C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF) -
        C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
          target O z g := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_finalRank_eq]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFiberInitialObservableBCF
  have hCard : 0 < Fintype.card C.base.geometry.Edge :=
    Fintype.card_pos_iff.mpr ⟨target⟩
  have hCardNe : Fintype.card C.base.geometry.Edge ≠ 0 :=
    Nat.ne_of_gt hCard
  simp [Function.update,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialRankBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalRankBCF,
    hCardNe, Ne.symm hCardNe]

/-- Uniform strict separation obtained by fixing two initial insertion values while
allowing the final insertion value to vary arbitrarily. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let I :=
    C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
      target O z
  let F :=
    C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
      target O z
  ∃ gLower gUpper : C.base.Gauge,
    ∃ a b : ℝ,
      a < b ∧
      (∀ h : C.base.Gauge, I gLower - F h ≤ a) ∧
      (∀ h : C.base.Gauge, b ≤ I gUpper - F h)

/-- Uniform strict separation obtained by fixing two final insertion values while
allowing the initial insertion value to vary arbitrarily. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  let I :=
    C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileBCF
      target O z
  let F :=
    C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileBCF
      target O z
  ∃ gLower gUpper : C.base.Gauge,
    ∃ a b : ℝ,
      a < b ∧
      (∀ h : C.base.Gauge, I h - F gLower ≤ a) ∧
      (∀ h : C.base.Gauge, b ≤ I h - F gUpper)

/-- Endpoint insertion-profile separation occurs at either the initial or final
insertion variable. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : Prop :=
  C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF
      target O z ∨
    C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF
      target O z

/-- Initial insertion-profile separation is exactly the rank-zero update-profile
witness. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF_iff_initial_update_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointInitialUpdateProfileSeparationWitnessBCF
        target O z := by
  constructor
  · intro hWitness
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF
      at hWitness
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialUpdateProfileSeparationWitnessBCF
    dsimp only at hWitness ⊢
    rcases hWitness with
      ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩
    refine ⟨gLower, gUpper, a, b, hab, ?_, ?_⟩
    · intro x
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_initialRank_eq_insertion_profiles]
      exact hLower
        (x C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF)
    · intro x
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_initialRank_eq_insertion_profiles]
      exact hUpper
        (x C.independentPairHybridTargetTrajectoryEndpointFinalRankBCF)
  · intro hWitness
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialUpdateProfileSeparationWitnessBCF
      at hWitness
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF
    dsimp only at hWitness ⊢
    rcases hWitness with
      ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩
    refine ⟨gLower, gUpper, a, b, hab, ?_, ?_⟩
    · intro h
      let x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier :=
        fun _ => h
      have hx := hLower x
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_initialRank_eq_insertion_profiles]
        at hx
      simpa [x] using hx
    · intro h
      let x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier :=
        fun _ => h
      have hx := hUpper x
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_initialRank_eq_insertion_profiles]
        at hx
      simpa [x] using hx

/-- Final insertion-profile separation is exactly the full-rank update-profile
witness. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF_iff_final_update_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointFinalUpdateProfileSeparationWitnessBCF
        target O z := by
  constructor
  · intro hWitness
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF
      at hWitness
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalUpdateProfileSeparationWitnessBCF
    dsimp only at hWitness ⊢
    rcases hWitness with
      ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩
    refine ⟨gLower, gUpper, a, b, hab, ?_, ?_⟩
    · intro x
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_finalRank_eq_insertion_profiles]
      exact hLower
        (x C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF)
    · intro x
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_finalRank_eq_insertion_profiles]
      exact hUpper
        (x C.independentPairHybridTargetTrajectoryEndpointInitialRankBCF)
  · intro hWitness
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalUpdateProfileSeparationWitnessBCF
      at hWitness
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF
    dsimp only at hWitness ⊢
    rcases hWitness with
      ⟨gLower, gUpper, a, b, hab, hLower, hUpper⟩
    refine ⟨gLower, gUpper, a, b, hab, ?_, ?_⟩
    · intro h
      let x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier :=
        fun _ => h
      have hx := hLower x
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_finalRank_eq_insertion_profiles]
        at hx
      simpa [x] using hx
    · intro h
      let x : C.independentPairHybridTargetTrajectoryEndpointFiberCarrier :=
        fun _ => h
      have hx := hUpper x
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberTransportBCF_update_finalRank_eq_insertion_profiles]
        at hx
      simpa [x] using hx

/-- Endpoint insertion-profile separation is exactly endpoint-rank update
separation. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_endpoint_rank_update_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
        target O z := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInitialInsertionProfileSeparationWitnessBCF_iff_initial_update_witness,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFinalInsertionProfileSeparationWitnessBCF_iff_final_update_witness]

/-- Equivalently, the original generic coordinate-update witness is exactly an
endpoint insertion-profile separation witness. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_iff_insertion_profile_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF
        target O z ↔
      C.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
        target O z := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCoordinateUpdateProfileSeparationWitnessBCF_iff_endpoint_rank_witness
      C target O z).trans
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_endpoint_rank_update_witness
        C target O z).symm

/-- On a Hausdorff compact Gauge space, insertion-profile separation produces
nonempty open cross-cylinder innovation regions. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_implies_open_region_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
        target O z) :
    C.independentPairHybridTargetTrajectoryEndpointOpenRegionInnovationWitnessBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF_implies_open_region_witness
      C target O z
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_endpoint_rank_update_witness
        C target O z).mp hWitness)

/-- Insertion-profile separation forces positive fixed-fiber conditional variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
        target O z) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
      target O z := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointRankUpdateProfileSeparationWitnessBCF_implies_gap_pos
      C target O z
      ((continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_endpoint_rank_update_witness
        C target O z).mp hWitness)

/-- A non-null Gibbs-pair family carrying endpoint insertion-profile separation. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : Prop :=
  ∃ᵐ z ∂(C.gibbsMeasure.prod C.gibbsMeasure),
    C.independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF
      target O z

/-- A non-null insertion-profile family supplies the endpoint-rank update witness
family. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_fiberwise_endpoint_rank_witness
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF
      target O := by
  exact hWitness.mono fun z hz =>
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointInsertionProfileSeparationWitnessBCF_iff_endpoint_rank_update_witness
      C target O z).mp hz

/-- A non-null insertion-profile family forces positive global conditional
variance. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF
        target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
      target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_gap_pos
      C target O
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_fiberwise_endpoint_rank_witness
        C target O hWitness)

/-- With positive native energy, a non-null insertion-profile family forces the
exact endpoint correlation ratio below one. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_correlationRatio_lt_one
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF
        target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_correlationRatio_lt_one
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_fiberwise_endpoint_rank_witness
        C target O hWitness)

/-- With positive native energy, a non-null insertion-profile family produces a
strict endpoint correlation factor. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O)
    (hWitness :
      C.independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF
        target O) :
    ∃ ρ : ℝ, ρ < 1 ∧
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O ≤
        ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseEndpointRankUpdateProfileSeparationWitnessBCF_implies_exists_strict_correlation_factor
      C target O hNative
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportFiberwiseInsertionProfileSeparationWitnessBCF_implies_fiberwise_endpoint_rank_witness
        C target O hWitness)

end

end MathlibAnalytic
end MGAP4D
