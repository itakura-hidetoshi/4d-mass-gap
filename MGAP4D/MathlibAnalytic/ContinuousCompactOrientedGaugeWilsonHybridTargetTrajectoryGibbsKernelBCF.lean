import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryFullRankRowBridgeBCF
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- The measurable initial target-value kernel indexed by the original pair of
Gibbs configurations.  It is obtained as the first marginal of the already
constructed measurable overlap-coupling kernel. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialGaugeKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration) C.base.Gauge :=
  (C.configurationPairConditionalOverlapCouplingKernel target).map Prod.fst

instance continuousCompactOriented_independentPairHybridTargetInitialGaugeKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.independentPairHybridTargetInitialGaugeKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialGaugeKernel
  exact Kernel.IsMarkovKernel.map _ measurable_fst

/-- Every fiber of the initial gauge kernel is exactly the left endpoint's
single-link conditional law. -/
theorem continuous_compact_oriented_independentPairHybridTargetInitialGaugeKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetInitialGaugeKernel target z =
      C.singleLinkConditionalMeasure z.1 target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialGaugeKernel
  rw [Kernel.map_apply _ measurable_fst z]
  exact
    continuous_compact_oriented_map_fst_configurationPairConditionalOverlapCouplingKernel_apply
      C target z

/-- The measurable time-zero history kernel indexed by the original Gibbs pair. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialHistoryKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    Kernel (C.base.Configuration × C.base.Configuration)
      ((i : Finset.Iic 0) → C.base.Gauge) :=
  (C.independentPairHybridTargetInitialGaugeKernel target).map
    (fun g : C.base.Gauge => fun _ : Finset.Iic 0 => g)

instance continuousCompactOriented_independentPairHybridTargetInitialHistoryKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    IsMarkovKernel (C.independentPairHybridTargetInitialHistoryKernel target) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialHistoryKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Every time-zero history-kernel fiber is exactly the fixed-pair initial
history measure used by the original trajectory construction. -/
theorem continuous_compact_oriented_independentPairHybridTargetInitialHistoryKernel_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetInitialHistoryKernel target z =
      C.independentPairHybridTargetInitialHistoryMeasure z.1 target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialHistoryKernel
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialHistoryMeasure
  rw [Kernel.map_apply _ (by fun_prop) z,
    continuous_compact_oriented_independentPairHybridTargetInitialGaugeKernel_apply]

/-- Given the original Gibbs pair and a target-value history through rank `k`,
sample the next target value using the measurable global anchored transition
kernel at the corresponding consecutive canonical backgrounds. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetNextGaugeKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    Kernel
      ((C.base.Configuration × C.base.Configuration) ×
        ((i : Finset.Iic k) → C.base.Gauge))
      C.base.Gauge :=
  (C.configurationPairConditionalAnchoredOverlapTransitionKernel target).comap
    (fun w =>
      (C.independentPairHybridEndpointPairMap
          (C.hybridTargetTrajectorySourceAtRank target k) w.1,
        w.2 ⟨k, Finset.mem_Iic.2 le_rfl⟩))
    (((continuous_compact_oriented_independentPairHybridEndpointPairMap_measurable
        C (C.hybridTargetTrajectorySourceAtRank target k)).comp measurable_fst).prodMk
      ((measurable_pi_apply _).comp measurable_snd))

instance continuousCompactOriented_independentPairHybridTargetNextGaugeKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    IsMarkovKernel (C.independentPairHybridTargetNextGaugeKernel target k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetNextGaugeKernel
  infer_instance

/-- At every genuine canonical rank, the parameterized next-value kernel is
fiberwise exactly the fixed-pair history kernel from the original trajectory law. -/
theorem continuous_compact_oriented_independentPairHybridTargetNextGaugeKernel_apply_of_lt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : ℕ)
    (hk : k < Fintype.card C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration)
    (x : (i : Finset.Iic k) → C.base.Gauge) :
    C.independentPairHybridTargetNextGaugeKernel target k (z, x) =
      C.independentPairHybridTargetHistoryKernel z.1 z.2 target k x := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetNextGaugeKernel
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetHistoryKernel
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTransitionKernelAtStep
    ContinuousCompactOrientedGaugeWilsonSystem.configurationPairConditionalAnchoredOverlapTransitionKernelAt
  change
    C.configurationPairConditionalAnchoredOverlapTransitionKernel target
        (C.independentPairHybridEndpointPairMap
            (C.hybridTargetTrajectorySourceAtRank target k) z,
          x ⟨k, Finset.mem_Iic.2 le_rfl⟩) =
      C.configurationPairConditionalAnchoredOverlapTransitionKernel target
        ((C.independentPairHybridConfiguration z.1 z.2 k,
            C.independentPairHybridConfiguration z.1 z.2 (k + 1)),
          x ⟨k, Finset.mem_Iic.2 le_rfl⟩)
  rw [continuous_compact_oriented_independentPairHybridEndpointPairMap_hybridTargetTrajectorySourceAtRank_of_lt
    C z.1 z.2 target k hk]

/-- One measurable parameterized extension from a history through rank `k` to a
history through rank `k+1`.  The original Gibbs pair is used only as a parameter
and is not retained in the output carrier. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryExtensionKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    Kernel
      ((C.base.Configuration × C.base.Configuration) ×
        ((i : Finset.Iic k) → C.base.Gauge))
      ((i : Finset.Iic (k + 1)) → C.base.Gauge) :=
  (((Kernel.deterministic Prod.snd measurable_snd) ×ₖ
      (C.independentPairHybridTargetNextGaugeKernel target k).map
        (MeasurableEquiv.piSingleton (X := fun _ => C.base.Gauge) k)).map
    (IicProdIoc (X := fun _ => C.base.Gauge) k (k + 1)))

instance continuousCompactOriented_independentPairHybridTargetTrajectoryExtensionKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    IsMarkovKernel
      (C.independentPairHybridTargetTrajectoryExtensionKernel target k) := by
  letI : IsMarkovKernel
      ((C.independentPairHybridTargetNextGaugeKernel target k).map
        (MeasurableEquiv.piSingleton (X := fun _ => C.base.Gauge) k)) :=
    Kernel.IsMarkovKernel.map _
      (MeasurableEquiv.piSingleton (X := fun _ => C.base.Gauge) k).measurable
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryExtensionKernel
  exact Kernel.IsMarkovKernel.map _
    (measurable_IicProdIoc (X := fun _ => C.base.Gauge))

/-- At a genuine rank, the parameterized extension fiber is exactly the
one-step `partialTraj` kernel of the original fixed-pair history construction. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryExtensionKernel_apply_of_lt
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (k : ℕ)
    (hk : k < Fintype.card C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration)
    (x : (i : Finset.Iic k) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectoryExtensionKernel target k (z, x) =
      Kernel.partialTraj
        (X := fun _ => C.base.Gauge)
        (C.independentPairHybridTargetHistoryKernel z.1 z.2 target)
        k (k + 1) x := by
  let singleton := MeasurableEquiv.piSingleton (X := fun _ => C.base.Gauge) k
  let glue := IicProdIoc (X := fun _ => C.base.Gauge) k (k + 1)
  have hGlue : Measurable glue :=
    measurable_IicProdIoc (X := fun _ => C.base.Gauge)
  rw [Kernel.partialTraj_succ_self]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryExtensionKernel
  change
    ((((Kernel.deterministic Prod.snd measurable_snd) ×ₖ
        (C.independentPairHybridTargetNextGaugeKernel target k).map singleton).map
      glue) (z, x)) = _
  rw [Kernel.map_apply _ hGlue (z, x), Kernel.map_apply _ hGlue x]
  congr 1
  rw [Kernel.prod_apply, Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.id_apply,
    Kernel.map_apply _ singleton.measurable (z, x),
    Kernel.map_apply _ singleton.measurable x,
    continuous_compact_oriented_independentPairHybridTargetNextGaugeKernel_apply_of_lt
      C target k hk z x]

/-- Measurable finite target-trajectory kernel indexed by the original independent
Gibbs configuration pair. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    (m : ℕ) → Kernel
      (C.base.Configuration × C.base.Configuration)
      ((i : Finset.Iic m) → C.base.Gauge)
  | 0 => C.independentPairHybridTargetInitialHistoryKernel target
  | m + 1 =>
      C.independentPairHybridTargetTrajectoryExtensionKernel target m ∘ₖ
        (Kernel.id ×ₖ C.independentPairHybridTargetTrajectoryKernel target m)

instance continuousCompactOriented_independentPairHybridTargetTrajectoryKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (m : ℕ) :
    IsMarkovKernel (C.independentPairHybridTargetTrajectoryKernel target m) := by
  induction m with
  | zero =>
      rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryKernel]
      infer_instance
  | succ m ih =>
      letI : IsMarkovKernel
          (C.independentPairHybridTargetTrajectoryKernel target m) := ih
      rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryKernel]
      infer_instance

/-- Up to the full canonical edge count, every fiber of the measurable
configuration-pair trajectory kernel is exactly the previously constructed
fixed-pair finite trajectory measure. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryKernel_apply_of_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (m : ℕ)
    (hm : m ≤ Fintype.card C.base.geometry.Edge)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryKernel target m z =
      C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target m := by
  induction m with
  | zero =>
      rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryKernel,
        continuous_compact_oriented_independentPairHybridTargetInitialHistoryKernel_apply,
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryMeasure,
        Kernel.partialTraj_self, Measure.id_comp]
  | succ m ih =>
      have hmCard : m < Fintype.card C.base.geometry.Edge :=
        Nat.lt_of_succ_le hm
      have hmLe : m ≤ Fintype.card C.base.geometry.Edge :=
        Nat.le_of_succ_le hm
      rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryKernel,
        continuous_compact_oriented_independentPairHybridTargetTrajectoryMeasure_succ]
      ext s hs
      rw [Kernel.comp_apply' _ _ _ hs]
      rw [Kernel.lintegral_id_prod
        (Kernel.measurable_coe
          (C.independentPairHybridTargetTrajectoryExtensionKernel target m) hs)
        (C.independentPairHybridTargetTrajectoryKernel target m) z]
      simp_rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryExtensionKernel_apply_of_lt
        C target m hmCard z]
      rw [ih hmLe]
      exact (Measure.bind_apply hs (Kernel.aemeasurable _)).symm

/-- Joint law of an independent Gibbs configuration pair and its coupled finite
target-value trajectory. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryJointMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (m : ℕ) :
    Measure
      ((C.base.Configuration × C.base.Configuration) ×
        ((i : Finset.Iic m) → C.base.Gauge)) :=
  (C.gibbsMeasure.prod C.gibbsMeasure) ⊗ₘ
    C.independentPairHybridTargetTrajectoryKernel target m

instance continuousCompactOriented_independentPairHybridTargetTrajectoryJointMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (m : ℕ) :
    IsProbabilityMeasure
      (C.independentPairHybridTargetTrajectoryJointMeasure target m) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryJointMeasure
  infer_instance

end

end MathlibAnalytic
end MGAP4D
