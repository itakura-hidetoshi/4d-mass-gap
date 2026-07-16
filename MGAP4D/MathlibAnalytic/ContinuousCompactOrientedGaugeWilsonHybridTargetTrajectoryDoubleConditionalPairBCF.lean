import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointGibbsMarginalsBCF
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryNativeConditionalPairReferenceBCF
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Two conditionally independent copies of the complete Gibbs-indexed target
trajectory, indexed by the same original configuration pair. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
        ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge)) :=
  C.independentPairHybridTargetTrajectoryKernel target
      (Fintype.card C.base.geometry.Edge) ×ₖ
    C.independentPairHybridTargetTrajectoryKernel target
      (Fintype.card C.base.geometry.Edge)

instance continuousCompactOriented_independentPairHybridTargetTrajectoryDoubleKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.independentPairHybridTargetTrajectoryDoubleKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleKernel
  infer_instance

/-- Every double-trajectory fiber is the product of two copies of the fixed-pair
complete trajectory law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleKernel target z =
      (C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)).prod
      (C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleKernel
  rw [Kernel.prod_apply,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryKernel_apply_of_le
      C target (Fintype.card C.base.geometry.Edge) le_rfl z]

/-- Joint law of an independent Gibbs configuration pair and two conditionally
independent complete target trajectories over that same pair. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleJointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Measure ((C.base.Configuration × C.base.Configuration) ×
      (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
        ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge))) :=
  (C.gibbsMeasure.prod C.gibbsMeasure) ⊗ₘ
    C.independentPairHybridTargetTrajectoryDoubleKernel target

instance continuousCompactOriented_independentPairHybridTargetTrajectoryDoubleJointMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.independentPairHybridTargetTrajectoryDoubleJointMeasure target) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleJointMeasure
  infer_instance

/-- At one canonical rank, reconstruct two full configurations on the same
hybrid background from the corresponding values of the two trajectories. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration)
    (xy :
      (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
        ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge))) :
    C.base.Configuration × C.base.Configuration :=
  let background := C.independentPairHybridConfiguration z.1 z.2 r
  (C.base.replaceLink background target
      (xy.1 ⟨r, Finset.mem_Iic.2 hr⟩),
    C.base.replaceLink background target
      (xy.2 ⟨r, Finset.mem_Iic.2 hr⟩))

/-- The fixed-original-pair rank reconstruction is continuous in both complete
trajectories. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    Continuous
      (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap
        target r hr z) := by
  have hLeft : Continuous
      (fun xy :
          (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
            ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge)) =>
        xy.1 ⟨r, Finset.mem_Iic.2 hr⟩) :=
    (continuous_apply _).comp continuous_fst
  have hRight : Continuous
      (fun xy :
          (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
            ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge)) =>
        xy.2 ⟨r, Finset.mem_Iic.2 hr⟩) :=
    (continuous_apply _).comp continuous_snd
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap
  exact
    ((continuous_compact_oriented_replaceLink
      C (C.independentPairHybridConfiguration z.1 z.2 r) target).comp hLeft).prodMk
      ((continuous_compact_oriented_replaceLink
        C (C.independentPairHybridConfiguration z.1 z.2 r) target).comp hRight)

/-- Fixed-pair rank law obtained from two independent complete trajectories. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    Measure (C.base.Configuration × C.base.Configuration) :=
  Measure.map
    (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap
      target r hr z)
    ((C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)).prod
      (C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target
        (Fintype.card C.base.geometry.Edge)))

/-- At every canonical rank, two independent trajectories reconstruct exactly
the native independent conditional-pair kernel of the rank background. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMeasure_eq_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMeasure
        target r hr z =
      C.singleLinkHeatBathIndependentPairKernel target
        (C.independentPairHybridConfiguration z.1 z.2 r) := by
  let n := Fintype.card C.base.geometry.Edge
  let trajectory :=
    C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target n
  let evalRank : ((i : Finset.Iic n) → C.base.Gauge) → C.base.Gauge :=
    fun x => x ⟨r, Finset.mem_Iic.2 hr⟩
  let pairEval :
      (((i : Finset.Iic n) → C.base.Gauge) ×
        ((i : Finset.Iic n) → C.base.Gauge)) →
      C.base.Gauge × C.base.Gauge :=
    fun xy => (evalRank xy.1, evalRank xy.2)
  let background := C.independentPairHybridConfiguration z.1 z.2 r
  have hEval : Measurable evalRank := measurable_pi_apply _
  have hPairEval : Measurable pairEval :=
    (hEval.comp measurable_fst).prodMk (hEval.comp measurable_snd)
  have hPairConfiguration : Measurable
      (C.singleLinkConditionalPairConfigurationMap background target) :=
    (continuous_compact_oriented_singleLinkConditionalPairConfigurationMap_continuous
      C background target).measurable
  have hCoordinate : Measure.map evalRank trajectory =
      C.singleLinkConditionalMeasure background target := by
    simpa [n, trajectory, evalRank, background] using
      continuous_compact_oriented_map_coordinate_independentPairHybridTargetTrajectoryMeasure
        C z.1 z.2 target r n hr
  have hMapProd :
      Measure.map (Prod.map evalRank evalRank) (trajectory.prod trajectory) =
        (Measure.map evalRank trajectory).prod
          (Measure.map evalRank trajectory) :=
    Measure.map_prod_map trajectory trajectory hEval hEval
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMeasure
  change Measure.map
      ((C.singleLinkConditionalPairConfigurationMap background target) ∘ pairEval)
      (trajectory.prod trajectory) = _
  rw [← Measure.map_map hPairConfiguration hPairEval]
  change Measure.map
      (C.singleLinkConditionalPairConfigurationMap background target)
      (Measure.map (Prod.map evalRank evalRank) (trajectory.prod trajectory)) = _
  rw [hMapProd, hCoordinate]
  rw [continuous_compact_oriented_singleLinkHeatBathIndependentPairKernel_apply]

/-- Global rank reconstruction map on the original-pair/double-trajectory
carrier. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge)
    (w : (C.base.Configuration × C.base.Configuration) ×
      (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
        ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge))) :
    C.base.Configuration × C.base.Configuration :=
  C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap
    target r hr w.1 w.2

/-- The global rank reconstruction map is continuous. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge) :
    Continuous
      (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
        target r hr) := by
  have hBackground : Continuous
      (fun w : (C.base.Configuration × C.base.Configuration) ×
          (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
            ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge)) =>
        C.independentPairHybridConfiguration w.1.1 w.1.2 r) :=
    (continuous_compact_oriented_independentPairHybridConfiguration C r).comp
      continuous_fst
  have hLeft : Continuous
      (fun w : (C.base.Configuration × C.base.Configuration) ×
          (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
            ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge)) =>
        w.2.1 ⟨r, Finset.mem_Iic.2 hr⟩) :=
    ((continuous_apply _).comp continuous_fst).comp continuous_snd
  have hRight : Continuous
      (fun w : (C.base.Configuration × C.base.Configuration) ×
          (((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge) ×
            ((i : Finset.Iic (Fintype.card C.base.geometry.Edge)) → C.base.Gauge)) =>
        w.2.2 ⟨r, Finset.mem_Iic.2 hr⟩) :=
    ((continuous_apply _).comp continuous_snd).comp continuous_snd
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap
  exact
    ((continuous_compact_oriented_replaceLink_uncurry C target).comp
      (hBackground.prodMk hLeft)).prodMk
      ((continuous_compact_oriented_replaceLink_uncurry C target).comp
        (hBackground.prodMk hRight))

/-- Rank-pair Markov kernel obtained from two complete target trajectories. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      (C.base.Configuration × C.base.Configuration) :=
  ((Kernel.id ×ₖ C.independentPairHybridTargetTrajectoryDoubleKernel target).map
    (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
      target r hr))

instance continuousCompactOriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge) :
    IsMarkovKernel
      (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel
        target r hr) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel
  exact Kernel.IsMarkovKernel.map _
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap_continuous
      C target r hr).measurable

/-- Every rank-pair kernel fiber is the fixed-pair rank reconstruction law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel
        target r hr z =
      C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMeasure
        target r hr z := by
  have hGlobal : Measurable
      (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
        target r hr) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap_continuous
      C target r hr).measurable
  have hFiber : Measurable
      (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap
        target r hr z) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMap_continuous
      C target r hr z).measurable
  ext s hs
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMeasure
  rw [Kernel.map_apply' _ hGlobal z hs]
  rw [Kernel.id_prod_apply' _ z (hGlobal hs)]
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleKernel_apply]
  rw [Measure.map_apply hFiber hs]
  rfl

/-- The rank-pair kernel is exactly the native independent conditional-pair
kernel pulled back by the rank hybrid background. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel_eq_native_comap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel
        target r hr =
      (C.singleLinkHeatBathIndependentPairKernel target).comap
        (fun z : C.base.Configuration × C.base.Configuration =>
          C.independentPairHybridConfiguration z.1 z.2 r)
        (continuous_compact_oriented_independentPairHybridConfiguration C r).measurable := by
  ext z : 1
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel_apply,
    continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairFiberMeasure_eq_native]
  rfl

/-- Global rank-pair law induced by the double complete trajectory. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge) :
    Measure (C.base.Configuration × C.base.Configuration) :=
  C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel
      target r hr ∘ₘ
    (C.gibbsMeasure.prod C.gibbsMeasure)

instance continuousCompactOriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure
        target r hr) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure
  infer_instance

/-- The global rank-pair law is exactly the pushforward of the double-trajectory
joint law by rank reconstruction. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure_eq_map_doubleJoint
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (r : ℕ)
    (hr : r ≤ Fintype.card C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure
        target r hr =
      Measure.map
        (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
          target r hr)
        (C.independentPairHybridTargetTrajectoryDoubleJointMeasure target) := by
  have hRank : Measurable
      (C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap
        target r hr) :=
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMap_continuous
      C target r hr).measurable
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleJointMeasure
  rw [Measure.compProd_eq_comp_prod]
  symm
  exact Measure.map_comp
    (C.gibbsMeasure.prod C.gibbsMeasure)
    (Kernel.id ×ₖ C.independentPairHybridTargetTrajectoryDoubleKernel target)
    hRank

/-- At rank zero the double-trajectory rank-pair law is the existing Gibbs-
averaged native independent conditional-pair reference law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure_zero_eq_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure
        target 0 (Nat.zero_le _) =
      C.singleLinkHeatBathIndependentPairMeasure target := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure]
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel_eq_native_comap]
  calc
    ((C.singleLinkHeatBathIndependentPairKernel target).comap
        (fun z : C.base.Configuration × C.base.Configuration =>
          C.independentPairHybridConfiguration z.1 z.2 0)
        (continuous_compact_oriented_independentPairHybridConfiguration C 0).measurable) ∘ₘ μ =
      C.singleLinkHeatBathIndependentPairKernel target ∘ₘ
        Measure.map
          (fun z : C.base.Configuration × C.base.Configuration =>
            C.independentPairHybridConfiguration z.1 z.2 0) μ :=
      HybridTargetTrajectory.comap_comp_measure_eq_comp_map
        μ (C.singleLinkHeatBathIndependentPairKernel target)
        (fun z : C.base.Configuration × C.base.Configuration =>
          C.independentPairHybridConfiguration z.1 z.2 0)
        (continuous_compact_oriented_independentPairHybridConfiguration C 0).measurable
    _ = C.singleLinkHeatBathIndependentPairKernel target ∘ₘ
        Measure.map Prod.fst μ := by
      rw [show (fun z : C.base.Configuration × C.base.Configuration =>
          C.independentPairHybridConfiguration z.1 z.2 0) = Prod.fst by
        funext z
        simp]
    _ = C.singleLinkHeatBathIndependentPairKernel target ∘ₘ C.gibbsMeasure := by
      unfold μ
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    _ = C.singleLinkHeatBathIndependentPairMeasure target := by
      rfl

/-- At the complete canonical rank the double-trajectory rank-pair law is again
the existing native independent conditional-pair reference law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure_card_eq_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure
        target (Fintype.card C.base.geometry.Edge) le_rfl =
      C.singleLinkHeatBathIndependentPairMeasure target := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryDoubleRankConfigurationPairMeasure]
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryDoubleRankConfigurationPairKernel_eq_native_comap]
  calc
    ((C.singleLinkHeatBathIndependentPairKernel target).comap
        (fun z : C.base.Configuration × C.base.Configuration =>
          C.independentPairHybridConfiguration z.1 z.2
            (Fintype.card C.base.geometry.Edge))
        (continuous_compact_oriented_independentPairHybridConfiguration C
          (Fintype.card C.base.geometry.Edge)).measurable) ∘ₘ μ =
      C.singleLinkHeatBathIndependentPairKernel target ∘ₘ
        Measure.map
          (fun z : C.base.Configuration × C.base.Configuration =>
            C.independentPairHybridConfiguration z.1 z.2
              (Fintype.card C.base.geometry.Edge)) μ :=
      HybridTargetTrajectory.comap_comp_measure_eq_comp_map
        μ (C.singleLinkHeatBathIndependentPairKernel target)
        (fun z : C.base.Configuration × C.base.Configuration =>
          C.independentPairHybridConfiguration z.1 z.2
            (Fintype.card C.base.geometry.Edge))
        (continuous_compact_oriented_independentPairHybridConfiguration C
          (Fintype.card C.base.geometry.Edge)).measurable
    _ = C.singleLinkHeatBathIndependentPairKernel target ∘ₘ
        Measure.map Prod.snd μ := by
      rw [show (fun z : C.base.Configuration × C.base.Configuration =>
          C.independentPairHybridConfiguration z.1 z.2
            (Fintype.card C.base.geometry.Edge)) = Prod.snd by
        funext z
        simp]
    _ = C.singleLinkHeatBathIndependentPairKernel target ∘ₘ C.gibbsMeasure := by
      unfold μ
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = C.singleLinkHeatBathIndependentPairMeasure target := by
      rfl

end

end MathlibAnalytic
end MGAP4D
