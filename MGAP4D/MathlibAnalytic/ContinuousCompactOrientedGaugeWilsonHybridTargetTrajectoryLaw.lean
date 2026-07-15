import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTransitionPath
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory

noncomputable section

namespace HybridTargetTrajectory

/-- Composing a pulled-back kernel against a measure is the same as composing the
original kernel against the pushforward measure. -/
theorem comap_comp_measure_eq_comp_map
    {α β γ : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    [MeasurableSpace γ]
    (μ : Measure γ)
    (κ : Kernel α β)
    (f : γ → α)
    (hf : Measurable f) :
    κ.comap f hf ∘ₘ μ = κ ∘ₘ μ.map f := by
  rw [Measure.comp_eq_comp_const_apply, Measure.comp_eq_comp_const_apply,
    ← Kernel.map_const μ hf, Kernel.comp_map]

/-- A deterministic first coordinate paired with a pulled-back second-coordinate
kernel, integrated against the original measure, is the usual composition-product
after pushing the first coordinate forward. -/
theorem deterministic_prod_comap_comp_measure_eq_compProd_map
    {α β γ : Type*}
    [MeasurableSpace α]
    [MeasurableSpace β]
    [MeasurableSpace γ]
    (μ : Measure γ)
    [SFinite μ]
    (κ : Kernel α β)
    [IsSFiniteKernel κ]
    (f : γ → α)
    (hf : Measurable f) :
    ((Kernel.deterministic f hf) ×ₖ (κ.comap f hf)) ∘ₘ μ =
      (μ.map f) ⊗ₘ κ := by
  rw [Measure.compProd_eq_comp_prod,
    ← Measure.deterministic_comp_eq_map hf,
    Measure.comp_assoc,
    Kernel.comp_deterministic_eq_comap,
    Kernel.comap_prod,
    Kernel.id_comap]

end HybridTargetTrajectory

/-- History-dependent Markov kernel used by Ionescu--Tulcea: at time `k`, only
the last target value in the history is read, and the explicit anchored transition
produces the value at time `k + 1`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetHistoryKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    Kernel ((i : Iic k) → C.base.Gauge) C.base.Gauge :=
  (C.independentPairHybridTargetTransitionKernelAtStep A B target k).comap
    (fun x => x ⟨k, mem_Iic.2 le_rfl⟩)
    (measurable_pi_apply _)

/-- Every history-dependent target kernel is Markov. -/
instance continuousCompactOriented_independentPairHybridTargetHistoryKernel_isMarkov
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    IsMarkovKernel
      (C.independentPairHybridTargetHistoryKernel A B target k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetHistoryKernel
  infer_instance

/-- Initial length-one trajectory law whose unique time-zero coordinate has the
exact left endpoint target-link conditional distribution. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialHistoryMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure ((i : Iic 0) → C.base.Gauge) :=
  Measure.map (fun g : C.base.Gauge => fun _ => g)
    (C.singleLinkConditionalMeasure A target)

instance continuousCompactOriented_independentPairHybridTargetInitialHistoryMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    IsProbabilityMeasure
      (C.independentPairHybridTargetInitialHistoryMeasure A target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialHistoryMeasure
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Finite trajectory law of target-link values along the first `m` anchored
hybrid transitions. Its carrier stores all values from time `0` through time
`m`. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (m : ℕ) :
    Measure ((i : Iic m) → C.base.Gauge) :=
  Kernel.partialTraj
      (X := fun _ => C.base.Gauge)
      (C.independentPairHybridTargetHistoryKernel A B target) 0 m ∘ₘ
    C.independentPairHybridTargetInitialHistoryMeasure A target

instance continuousCompactOriented_independentPairHybridTargetTrajectoryMeasure_isProbability
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (m : ℕ) :
    IsProbabilityMeasure
      (C.independentPairHybridTargetTrajectoryMeasure A B target m) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryMeasure
  infer_instance

/-- Evaluating the initial one-coordinate history at time zero recovers the
exact left endpoint conditional law. -/
theorem continuous_compact_oriented_map_zero_independentPairHybridTargetInitialHistoryMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Measure.map
        (fun x : (i : Iic 0) → C.base.Gauge =>
          x ⟨0, mem_Iic.2 le_rfl⟩)
        (C.independentPairHybridTargetInitialHistoryMeasure A target) =
      C.singleLinkConditionalMeasure A target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetInitialHistoryMeasure
  have hEmbed : Measurable
      (fun g : C.base.Gauge => fun _ : Iic 0 => g) := by
    exact measurable_pi_lambda _ (fun _ => measurable_id)
  have hEval : Measurable
      (fun x : (i : Iic 0) → C.base.Gauge =>
        x ⟨0, mem_Iic.2 le_rfl⟩) :=
    measurable_pi_apply _
  rw [Measure.map_map hEval hEmbed]
  simpa only [Function.comp_apply] using
    (Measure.map_id :
      Measure.map (id : C.base.Gauge → C.base.Gauge)
          (C.singleLinkConditionalMeasure A target) =
        C.singleLinkConditionalMeasure A target)

/-- The trajectory law at time `m + 1` is obtained by extending the trajectory
law at time `m` with one more history-dependent anchored transition. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryMeasure_succ
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (m : ℕ) :
    C.independentPairHybridTargetTrajectoryMeasure A B target (m + 1) =
      Kernel.partialTraj
          (X := fun _ => C.base.Gauge)
          (C.independentPairHybridTargetHistoryKernel A B target) m (m + 1) ∘ₘ
        C.independentPairHybridTargetTrajectoryMeasure A B target m := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryMeasure
  rw [Measure.comp_assoc]
  rw [Kernel.partialTraj_comp_partialTraj
    (X := fun _ => C.base.Gauge)
    (κ := C.independentPairHybridTargetHistoryKernel A B target)
    (a := 0) (b := m) (c := m + 1)
    (hab := zero_le m) (hbc := m.le_succ)]

/-- Restricting a longer finite trajectory to an earlier time gives exactly the
earlier trajectory law. -/
theorem continuous_compact_oriented_map_frestrictLe₂_independentPairHybridTargetTrajectoryMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (b m : ℕ)
    (hbm : b ≤ m) :
    Measure.map
        (Preorder.frestrictLe₂ (π := fun _ => C.base.Gauge) hbm)
        (C.independentPairHybridTargetTrajectoryMeasure A B target m) =
      C.independentPairHybridTargetTrajectoryMeasure A B target b := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryMeasure
  rw [Measure.map_comp _ _
    (measurable_frestrictLe₂ (X := fun _ => C.base.Gauge) hbm)]
  rw [Kernel.partialTraj_map_frestrictLe₂
    (X := fun _ => C.base.Gauge)
    (κ := C.independentPairHybridTargetHistoryKernel A B target)
    (a := 0) (b := b) (c := m) (hbc := hbm)]

/-- The last coordinate of the finite trajectory at time `m` has exactly the
single-link conditional law corresponding to the rank-`m` hybrid background. -/
theorem continuous_compact_oriented_map_last_independentPairHybridTargetTrajectoryMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (m : ℕ) :
    Measure.map
        (fun x : (i : Iic m) → C.base.Gauge =>
          x ⟨m, mem_Iic.2 le_rfl⟩)
        (C.independentPairHybridTargetTrajectoryMeasure A B target m) =
      C.singleLinkConditionalMeasure
        (C.independentPairHybridConfiguration A B m) target := by
  induction m with
  | zero =>
      rw [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryMeasure,
        Kernel.partialTraj_self, Measure.id_comp,
        continuous_compact_oriented_map_zero_independentPairHybridTargetInitialHistoryMeasure,
        continuous_compact_oriented_independentPairHybridConfiguration_zero]
  | succ m ih =>
      have hEval : Measurable
          (fun x : (i : Iic (m + 1)) → C.base.Gauge =>
            x ⟨m + 1, mem_Iic.2 le_rfl⟩) :=
        measurable_pi_apply _
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryMeasure_succ]
      rw [Measure.map_comp _ _ hEval]
      rw [Kernel.map_partialTraj_succ_self
        (X := fun _ => C.base.Gauge)
        (κ := C.independentPairHybridTargetHistoryKernel A B target) m]
      unfold
        ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetHistoryKernel
      rw [HybridTargetTrajectory.comap_comp_measure_eq_comp_map,
        ih,
        continuous_compact_oriented_independentPairHybridTargetTransitionKernelAtStep_comp_measure]

/-- Every coordinate of a longer finite trajectory has its corresponding exact
hybrid conditional marginal. -/
theorem continuous_compact_oriented_map_coordinate_independentPairHybridTargetTrajectoryMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k m : ℕ)
    (hkm : k ≤ m) :
    Measure.map
        (fun x : (i : Iic m) → C.base.Gauge =>
          x ⟨k, mem_Iic.2 hkm⟩)
        (C.independentPairHybridTargetTrajectoryMeasure A B target m) =
      C.singleLinkConditionalMeasure
        (C.independentPairHybridConfiguration A B k) target := by
  let restrict : ((i : Iic m) → C.base.Gauge) →
      ((i : Iic k) → C.base.Gauge) :=
    Preorder.frestrictLe₂ (π := fun _ => C.base.Gauge) hkm
  let evalM : ((i : Iic m) → C.base.Gauge) → C.base.Gauge :=
    fun x => x ⟨k, mem_Iic.2 hkm⟩
  let evalK : ((i : Iic k) → C.base.Gauge) → C.base.Gauge :=
    fun x => x ⟨k, mem_Iic.2 le_rfl⟩
  have hRestrict : Measurable restrict :=
    measurable_frestrictLe₂ (X := fun _ => C.base.Gauge) hkm
  have hEvalM : Measurable evalM := measurable_pi_apply _
  have hEvalK : Measurable evalK := measurable_pi_apply _
  have hComp : evalK ∘ restrict = evalM := by
    funext x
    rfl
  change Measure.map evalM
      (C.independentPairHybridTargetTrajectoryMeasure A B target m) = _
  calc
    Measure.map evalM
        (C.independentPairHybridTargetTrajectoryMeasure A B target m) =
      Measure.map evalK
        (Measure.map restrict
          (C.independentPairHybridTargetTrajectoryMeasure A B target m)) := by
            rw [Measure.map_map hEvalK hRestrict]
            rw [hComp]
    _ = Measure.map evalK
        (C.independentPairHybridTargetTrajectoryMeasure A B target k) := by
          rw [show restrict =
              Preorder.frestrictLe₂ (π := fun _ => C.base.Gauge) hkm from rfl,
            continuous_compact_oriented_map_frestrictLe₂_independentPairHybridTargetTrajectoryMeasure
              C A B target k m hkm]
    _ = C.singleLinkConditionalMeasure
        (C.independentPairHybridConfiguration A B k) target := by
      change Measure.map
          (fun x : (i : Iic k) → C.base.Gauge =>
            x ⟨k, mem_Iic.2 le_rfl⟩)
          (C.independentPairHybridTargetTrajectoryMeasure A B target k) = _
      exact
        continuous_compact_oriented_map_last_independentPairHybridTargetTrajectoryMeasure
          C A B target k

/-- Mapping one one-step partial trajectory to its last old value and its new
value gives the deterministic-last-coordinate/product kernel. -/
theorem continuous_compact_oriented_map_adjacent_partialTraj_independentPairHybridTargetHistoryKernel
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    (Kernel.partialTraj
        (X := fun _ => C.base.Gauge)
        (C.independentPairHybridTargetHistoryKernel A B target) k (k + 1)).map
      (fun x : (i : Iic (k + 1)) → C.base.Gauge =>
        (x ⟨k, mem_Iic.2 k.le_succ⟩,
          x ⟨k + 1, mem_Iic.2 le_rfl⟩)) =
      (Kernel.deterministic
          (fun x : (i : Iic k) → C.base.Gauge =>
            x ⟨k, mem_Iic.2 le_rfl⟩)
          (measurable_pi_apply _)) ×ₖ
        C.independentPairHybridTargetHistoryKernel A B target k := by
  let last : ((i : Iic k) → C.base.Gauge) → C.base.Gauge :=
    fun x => x ⟨k, mem_Iic.2 le_rfl⟩
  let pairAt : ((i : Iic (k + 1)) → C.base.Gauge) →
      C.base.Gauge × C.base.Gauge :=
    fun x =>
      (x ⟨k, mem_Iic.2 k.le_succ⟩,
        x ⟨k + 1, mem_Iic.2 le_rfl⟩)
  let singleton :=
    MeasurableEquiv.piSingleton (X := fun _ => C.base.Gauge) k
  have hLast : Measurable last := measurable_pi_apply _
  have hPair : Measurable pairAt :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hGlue : Measurable
      (IicProdIoc (X := fun _ => C.base.Gauge) k (k + 1)) :=
    measurable_IicProdIoc (X := fun _ => C.base.Gauge)
  have hComp :
      pairAt ∘ IicProdIoc (X := fun _ => C.base.Gauge) k (k + 1) =
        Prod.map last singleton.symm := by
    funext p
    apply Prod.ext
    · simp [pairAt, last, singleton, _root_.IicProdIoc]
    · simp [pairAt, singleton, _root_.IicProdIoc,
        MeasurableEquiv.piSingleton]
  have hSingleton :
      (singleton.symm :
          ((i : Ioc k (k + 1)) → C.base.Gauge) → C.base.Gauge) ∘
          (singleton :
            C.base.Gauge → ((i : Ioc k (k + 1)) → C.base.Gauge)) = id :=
    singleton.symm_comp_self
  change
    (Kernel.partialTraj
        (X := fun _ => C.base.Gauge)
        (C.independentPairHybridTargetHistoryKernel A B target) k (k + 1)).map
      pairAt =
      (Kernel.deterministic last hLast) ×ₖ
        C.independentPairHybridTargetHistoryKernel A B target k
  rw [Kernel.partialTraj_succ_self
    (X := fun _ => C.base.Gauge)
    (κ := C.independentPairHybridTargetHistoryKernel A B target) k]
  rw [← Kernel.map_comp_right _ hGlue hPair]
  rw [hComp]
  rw [← Kernel.map_prod_map _ _ hLast singleton.symm.measurable]
  rw [Kernel.id_map hLast]
  rw [← Kernel.map_comp_right _ singleton.measurable singleton.symm.measurable]
  rw [hSingleton, Kernel.map_id]

/-- Under the trajectory law through time `k + 1`, the adjacent target values
have exactly the explicit anchored overlap-coupling law for the two consecutive
hybrid backgrounds. -/
theorem continuous_compact_oriented_map_adjacent_independentPairHybridTargetTrajectoryMeasure_succ
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k : ℕ) :
    Measure.map
        (fun x : (i : Iic (k + 1)) → C.base.Gauge =>
          (x ⟨k, mem_Iic.2 k.le_succ⟩,
            x ⟨k + 1, mem_Iic.2 le_rfl⟩))
        (C.independentPairHybridTargetTrajectoryMeasure A B target (k + 1)) =
      C.singleLinkConditionalAnchoredOverlapCouplingMeasure
        (C.independentPairHybridConfiguration A B k)
        (C.independentPairHybridConfiguration A B (k + 1))
        target := by
  have hPair : Measurable
      (fun x : (i : Iic (k + 1)) → C.base.Gauge =>
        (x ⟨k, mem_Iic.2 k.le_succ⟩,
          x ⟨k + 1, mem_Iic.2 le_rfl⟩)) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryMeasure_succ]
  rw [Measure.map_comp _ _ hPair]
  rw [continuous_compact_oriented_map_adjacent_partialTraj_independentPairHybridTargetHistoryKernel]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetHistoryKernel
  rw [HybridTargetTrajectory.deterministic_prod_comap_comp_measure_eq_compProd_map,
    continuous_compact_oriented_map_last_independentPairHybridTargetTrajectoryMeasure]
  rfl

/-- Every adjacent pair inside any longer finite trajectory has the exact
anchored overlap-coupling law for the corresponding consecutive hybrid
backgrounds. -/
theorem continuous_compact_oriented_map_adjacent_independentPairHybridTargetTrajectoryMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k m : ℕ)
    (hkm : k + 1 ≤ m) :
    Measure.map
        (fun x : (i : Iic m) → C.base.Gauge =>
          (x ⟨k, mem_Iic.2 (k.le_succ.trans hkm)⟩,
            x ⟨k + 1, mem_Iic.2 hkm⟩))
        (C.independentPairHybridTargetTrajectoryMeasure A B target m) =
      C.singleLinkConditionalAnchoredOverlapCouplingMeasure
        (C.independentPairHybridConfiguration A B k)
        (C.independentPairHybridConfiguration A B (k + 1))
        target := by
  let restrict : ((i : Iic m) → C.base.Gauge) →
      ((i : Iic (k + 1)) → C.base.Gauge) :=
    Preorder.frestrictLe₂ (π := fun _ => C.base.Gauge) hkm
  let pairM : ((i : Iic m) → C.base.Gauge) →
      C.base.Gauge × C.base.Gauge :=
    fun x =>
      (x ⟨k, mem_Iic.2 (k.le_succ.trans hkm)⟩,
        x ⟨k + 1, mem_Iic.2 hkm⟩)
  let pairK : ((i : Iic (k + 1)) → C.base.Gauge) →
      C.base.Gauge × C.base.Gauge :=
    fun x =>
      (x ⟨k, mem_Iic.2 k.le_succ⟩,
        x ⟨k + 1, mem_Iic.2 le_rfl⟩)
  have hRestrict : Measurable restrict :=
    measurable_frestrictLe₂ (X := fun _ => C.base.Gauge) hkm
  have hPairM : Measurable pairM :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hPairK : Measurable pairK :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hComp : pairK ∘ restrict = pairM := by
    funext x
    rfl
  change Measure.map pairM
      (C.independentPairHybridTargetTrajectoryMeasure A B target m) = _
  calc
    Measure.map pairM
        (C.independentPairHybridTargetTrajectoryMeasure A B target m) =
      Measure.map pairK
        (Measure.map restrict
          (C.independentPairHybridTargetTrajectoryMeasure A B target m)) := by
            rw [Measure.map_map hPairK hRestrict]
            rw [hComp]
    _ = Measure.map pairK
        (C.independentPairHybridTargetTrajectoryMeasure A B target (k + 1)) := by
          rw [show restrict =
              Preorder.frestrictLe₂ (π := fun _ => C.base.Gauge) hkm from rfl,
            continuous_compact_oriented_map_frestrictLe₂_independentPairHybridTargetTrajectoryMeasure
              C A B target (k + 1) m hkm]
    _ = C.singleLinkConditionalAnchoredOverlapCouplingMeasure
        (C.independentPairHybridConfiguration A B k)
        (C.independentPairHybridConfiguration A B (k + 1))
        target := by
      change Measure.map
          (fun x : (i : Iic (k + 1)) → C.base.Gauge =>
            (x ⟨k, mem_Iic.2 k.le_succ⟩,
              x ⟨k + 1, mem_Iic.2 le_rfl⟩))
          (C.independentPairHybridTargetTrajectoryMeasure A B target (k + 1)) = _
      exact
        continuous_compact_oriented_map_adjacent_independentPairHybridTargetTrajectoryMeasure_succ
          C A B target k

/-- The same adjacent pair marginal is exactly the previously constructed
common-overlap plus normalized-residual coupling measure. -/
theorem continuous_compact_oriented_map_adjacent_independentPairHybridTargetTrajectoryMeasure_eq_overlap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (k m : ℕ)
    (hkm : k + 1 ≤ m) :
    Measure.map
        (fun x : (i : Iic m) → C.base.Gauge =>
          (x ⟨k, mem_Iic.2 (k.le_succ.trans hkm)⟩,
            x ⟨k + 1, mem_Iic.2 hkm⟩))
        (C.independentPairHybridTargetTrajectoryMeasure A B target m) =
      C.singleLinkConditionalOverlapCouplingMeasure
        (C.independentPairHybridConfiguration A B k)
        (C.independentPairHybridConfiguration A B (k + 1))
        target := by
  rw [continuous_compact_oriented_map_adjacent_independentPairHybridTargetTrajectoryMeasure
      C A B target k m hkm,
    continuous_compact_oriented_singleLinkConditionalAnchoredOverlapCouplingMeasure_eq_overlapCouplingMeasure]

end

end MathlibAnalytic
end MGAP4D