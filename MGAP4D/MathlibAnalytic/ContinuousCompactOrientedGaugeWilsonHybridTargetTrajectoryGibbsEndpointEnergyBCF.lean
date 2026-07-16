import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryGibbsKernelBCF
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Canonical source-background endpoint transport on the joint carrier of an
original configuration pair and its coupled finite target trajectory. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (w : (C.base.Configuration × C.base.Configuration) ×
      ((i : Finset.Iic m) → C.base.Gauge)) : ℝ :=
  C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
    (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
    target O m w.2

/-- The canonical joint endpoint transport is continuous simultaneously in the
original Gibbs pair and every finite trajectory coordinate. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
        target O m) := by
  have hAt : ∀ k (hkm : k ≤ m), Continuous
      (fun w : (C.base.Configuration × C.base.Configuration) ×
          ((i : Finset.Iic m) → C.base.Gauge) =>
        O (C.base.replaceLink
          (C.independentPairHybridConfiguration w.1.1 w.1.2 k)
          target (w.2 ⟨k, Finset.mem_Iic.2 hkm⟩))) := by
    intro k hkm
    have hBackground : Continuous
        (fun w : (C.base.Configuration × C.base.Configuration) ×
            ((i : Finset.Iic m) → C.base.Gauge) =>
          C.independentPairHybridConfiguration w.1.1 w.1.2 k) :=
      (continuous_compact_oriented_independentPairHybridConfiguration C k).comp
        continuous_fst
    have hGauge : Continuous
        (fun w : (C.base.Configuration × C.base.Configuration) ×
            ((i : Finset.Iic m) → C.base.Gauge) =>
          w.2 ⟨k, Finset.mem_Iic.2 hkm⟩) :=
      (continuous_apply (⟨k, Finset.mem_Iic.2 hkm⟩ : Finset.Iic m)).comp
        continuous_snd
    exact O.continuous.comp
      ((continuous_compact_oriented_replaceLink_uncurry C target).comp
        (hBackground.prodMk hGauge))
  change Continuous
    (fun w : (C.base.Configuration × C.base.Configuration) ×
        ((i : Finset.Iic m) → C.base.Gauge) =>
      O (C.base.replaceLink
          (C.independentPairHybridConfiguration w.1.1 w.1.2 0)
          target (w.2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩)) -
        O (C.base.replaceLink
          (C.independentPairHybridConfiguration w.1.1 w.1.2 m)
          target (w.2 ⟨m, Finset.mem_Iic.2 le_rfl⟩)))
  exact (hAt 0 (Nat.zero_le m)).sub (hAt m le_rfl)

/-- The joint canonical endpoint transport is uniformly bounded by twice the
bounded-continuous observable norm. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (w : (C.base.Configuration × C.base.Configuration) ×
      ((i : Finset.Iic m) → C.base.Gauge)) :
    |C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
        target O m w| ≤ 2 * ‖O‖ := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O m 0 (Nat.zero_le m) w.2,
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
      target O m m le_rfl w.2]
  calc
    |O (C.base.replaceLink
          (C.independentPairHybridConfiguration w.1.1 w.1.2 0)
          target (w.2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩)) -
        O (C.base.replaceLink
          (C.independentPairHybridConfiguration w.1.1 w.1.2 m)
          target (w.2 ⟨m, Finset.mem_Iic.2 le_rfl⟩))| ≤
      |O (C.base.replaceLink
          (C.independentPairHybridConfiguration w.1.1 w.1.2 0)
          target (w.2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩))| +
        |O (C.base.replaceLink
          (C.independentPairHybridConfiguration w.1.1 w.1.2 m)
          target (w.2 ⟨m, Finset.mem_Iic.2 le_rfl⟩))| := abs_sub _ _
    _ ≤ ‖O‖ + ‖O‖ := by
      exact add_le_add
        (by
          simpa [Real.norm_eq_abs] using
            (O.norm_coe_le_norm
              (C.base.replaceLink
                (C.independentPairHybridConfiguration w.1.1 w.1.2 0)
                target (w.2 ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩))))
        (by
          simpa [Real.norm_eq_abs] using
            (O.norm_coe_le_norm
              (C.base.replaceLink
                (C.independentPairHybridConfiguration w.1.1 w.1.2 m)
                target (w.2 ⟨m, Finset.mem_Iic.2 le_rfl⟩))))
    _ = 2 * ‖O‖ := (two_mul ‖O‖).symm

/-- Pointwise squared endpoint cost on the joint Gibbs-pair/trajectory carrier. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (w : (C.base.Configuration × C.base.Configuration) ×
      ((i : Finset.Iic m) → C.base.Gauge)) : ℝ :=
  (C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF
    target O m w) ^ 2

/-- The joint canonical endpoint square integrand is continuous. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF
        target O m) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointTransportBCF_continuous
      C target O m).pow 2

/-- The canonical endpoint square is integrable on the joint probability law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    Integrable
      (C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF
        target O m)
      (C.independentPairHybridTargetTrajectoryJointMeasure target m) := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF_continuous
      C target O m).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Jointly averaged canonical source-background endpoint trajectory energy. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) : ℝ :=
  ∫ w,
    C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF
      target O m w
    ∂C.independentPairHybridTargetTrajectoryJointMeasure target m

/-- Fixed-pair endpoint energy retained as a function of the original Gibbs pair. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
    z.1 z.2 (fun r => C.independentPairHybridConfiguration z.1 z.2 r)
    target O m

/-- Exact disintegration of the joint endpoint energy into the previously proved
fixed-pair endpoint trajectory energies. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_eq_integral_fiber
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (hm : m ≤ Fintype.card C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
        target O m =
      ∫ z : C.base.Configuration × C.base.Configuration,
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
          target O m z
        ∂(C.gibbsMeasure.prod C.gibbsMeasure) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let κ := C.independentPairHybridTargetTrajectoryKernel target m
  let f :=
    C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF
      target O m
  have hJointNamed :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF_integrable
      C target O m
  have hJoint : Integrable f (μ ⊗ₘ κ) := by
    simpa [μ, κ, f,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryJointMeasure]
      using hJointNamed
  have hFubini := Measure.integral_compProd hJoint
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
  change (∫ w, f w ∂(μ ⊗ₘ κ)) = _
  calc
    (∫ w, f w ∂(μ ⊗ₘ κ)) =
      ∫ z, ∫ x, f (z, x) ∂κ z ∂μ := hFubini
    _ = ∫ z,
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
          target O m z ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (∫ x, f (z, x) ∂κ z) =
          C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
            target O m z
        rw [show κ z =
          C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target m from
            continuous_compact_oriented_independentPairHybridTargetTrajectoryKernel_apply_of_le
              C target m hm z]
        unfold f
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
        rfl

/-- The fixed-pair endpoint-energy function is integrable under the independent
Gibbs-pair law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (hm : m ≤ Fintype.card C.base.geometry.Edge) :
    Integrable
      (C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
        target O m)
      (C.gibbsMeasure.prod C.gibbsMeasure) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let κ := C.independentPairHybridTargetTrajectoryKernel target m
  let f :=
    C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF
      target O m
  have hJointNamed :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF_integrable
      C target O m
  have hJoint : Integrable f (μ ⊗ₘ κ) := by
    simpa [μ, κ, f,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryJointMeasure]
      using hJointNamed
  have hOuter : Integrable (fun z => ∫ x, f (z, x) ∂κ z) μ := by
    simpa using hJoint.integral_compProd
  apply hOuter.congr
  exact Filter.Eventually.of_forall fun z => by
    change (∫ x, f (z, x) ∂κ z) =
      C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
        target O m z
    rw [show κ z =
      C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target m from
        continuous_compact_oriented_independentPairHybridTargetTrajectoryKernel_apply_of_le
          C target m hm z]
    unfold f
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointIntegrandBCF
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
    rfl

/-- Joint square integrand for one canonical fixed-left overlap step. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (w : (C.base.Configuration × C.base.Configuration) ×
      ((i : Finset.Iic m) → C.base.Gauge)) : ℝ :=
  (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
    (fun r => C.independentPairHybridConfiguration w.1.1 w.1.2 r)
    target O m k w.2) ^ 2

/-- Every canonical fixed-left overlap square is jointly continuous in the
configuration pair and trajectory coordinates. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF
        target O m k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
  split_ifs with hkm
  · have hBackground : Continuous
        (fun w : (C.base.Configuration × C.base.Configuration) ×
            ((i : Finset.Iic m) → C.base.Gauge) =>
          C.independentPairHybridConfiguration w.1.1 w.1.2 k) :=
      (continuous_compact_oriented_independentPairHybridConfiguration C k).comp
        continuous_fst
    have hLeftGauge : Continuous
        (fun w : (C.base.Configuration × C.base.Configuration) ×
            ((i : Finset.Iic m) → C.base.Gauge) =>
          w.2 ⟨k, Finset.mem_Iic.2 (k.le_succ.trans hkm)⟩) :=
      (continuous_apply
        (⟨k, Finset.mem_Iic.2 (k.le_succ.trans hkm)⟩ : Finset.Iic m)).comp
          continuous_snd
    have hRightGauge : Continuous
        (fun w : (C.base.Configuration × C.base.Configuration) ×
            ((i : Finset.Iic m) → C.base.Gauge) =>
          w.2 ⟨k + 1, Finset.mem_Iic.2 hkm⟩) :=
      (continuous_apply
        (⟨k + 1, Finset.mem_Iic.2 hkm⟩ : Finset.Iic m)).comp
          continuous_snd
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportBCF
    exact
      ((O.continuous.comp
        ((continuous_compact_oriented_replaceLink_uncurry C target).comp
          (hBackground.prodMk hLeftGauge))).sub
        (O.continuous.comp
          ((continuous_compact_oriented_replaceLink_uncurry C target).comp
            (hBackground.prodMk hRightGauge)))).pow 2
  · exact continuous_const

/-- Every canonical fixed-left joint square is integrable. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Integrable
      (C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF
        target O m k)
      (C.independentPairHybridTargetTrajectoryJointMeasure target m) := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF_continuous
      C target O m k).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Each canonical fixed-left overlap fiber is integrable as a function of the
original Gibbs configuration pair. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (hkm : k + 1 ≤ m)
    (hm : m ≤ Fintype.card C.base.geometry.Edge) :
    Integrable
      (C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
        target O k)
      (C.gibbsMeasure.prod C.gibbsMeasure) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  let κ := C.independentPairHybridTargetTrajectoryKernel target m
  let f :=
    C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF
      target O m k
  have hJointNamed :=
    continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF_integrable
      C target O m k
  have hJoint : Integrable f (μ ⊗ₘ κ) := by
    simpa [μ, κ, f,
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryJointMeasure]
      using hJointNamed
  have hOuter : Integrable (fun z => ∫ x, f (z, x) ∂κ z) μ := by
    simpa using hJoint.integral_compProd
  apply hOuter.congr
  exact Filter.Eventually.of_forall fun z => by
    change (∫ x, f (z, x) ∂κ z) =
      C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
        target O k z
    rw [show κ z =
      C.independentPairHybridTargetTrajectoryMeasure z.1 z.2 target m from
        continuous_compact_oriented_independentPairHybridTargetTrajectoryKernel_apply_of_le
          C target m hm z]
    unfold f
      ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapJointIntegrandBCF
    change
      C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportEnergyBCF
          z.1 z.2 (fun r => C.independentPairHybridConfiguration z.1 z.2 r)
          target O m k =
        C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
          target O k z
    rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportEnergyBCF_eq_overlap
      C z.1 z.2 (fun r => C.independentPairHybridConfiguration z.1 z.2 r)
      target O m k hkm]
    rfl

/-- Gibbs averaging the fixed-pair trajectory estimate gives a finite-prefix
bound by the established source-indexed overlap energies and the canonical
variation-square profile. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_le_sum_sourceOverlap_add_variation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (m : ℕ)
    (hm : m ≤ Fintype.card C.base.geometry.Edge) :
    C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
        target O m ≤
      (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 * C.independentPairHybridSourceOverlapTransportEnergyBCF
              target (C.hybridTargetTrajectorySourceAtRank target k) O +
            2 * (P.variation
              (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2) := by
  letI : IsProbabilityMeasure C.gibbsMeasure :=
    continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure C
  let μ := C.gibbsMeasure.prod C.gibbsMeasure
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hLeft : Integrable
      (C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
        target O m) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF_integrable
        C target O m hm
  have hFixed : ∀ k ∈ Finset.range m, Integrable
      (C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
        target O k) μ := by
    intro k hk
    have hkm : k + 1 ≤ m :=
      Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF_integrable
        C target O m k hkm hm
  have hSummand : ∀ k ∈ Finset.range m, Integrable
      (fun z : C.base.Configuration × C.base.Configuration =>
        2 *
            C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
              target O k z +
          2 * (P.variation
            (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2) μ := by
    intro k hk
    exact ((hFixed k hk).const_mul 2).add (integrable_const _)
  have hSum : Integrable
      (fun z : C.base.Configuration × C.base.Configuration =>
        ∑ k ∈ Finset.range m,
          (2 *
              C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
                target O k z +
            2 * (P.variation
              (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2)) μ :=
    integrable_finset_sum _ hSummand
  have hRight : Integrable
      (fun z : C.base.Configuration × C.base.Configuration =>
        (m : ℝ) *
          ∑ k ∈ Finset.range m,
            (2 *
                C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
                  target O k z +
              2 * (P.variation
                (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2)) μ :=
    hSum.const_mul _
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_eq_integral_fiber
    C target O m hm]
  change (∫ z,
      C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
        target O m z ∂μ) ≤ _
  calc
    (∫ z,
        C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF
          target O m z ∂μ) ≤
      ∫ z, (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 *
              C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
                target O k z +
            2 * (P.variation
              (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2) ∂μ := by
        apply integral_mono hLeft hRight
        intro z
        simpa [
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointFiberEnergyBCF,
          ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF]
          using
            continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalBackgroundEndpointTransportEnergyBCF_le_sum_overlap_add_variation
              C z.1 z.2 target O P m hm
    _ = (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 * C.independentPairHybridSourceOverlapTransportEnergyBCF
              target (C.hybridTargetTrajectorySourceAtRank target k) O +
            2 * (P.variation
              (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2) := by
      rw [integral_const_mul]
      rw [integral_finset_sum _ hSummand]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      have hFiber := hFixed k hk
      have hkCard : k < Fintype.card C.base.geometry.Edge :=
        lt_of_lt_of_le (Finset.mem_range.mp hk) hm
      have hPullback :=
        continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_eq_integral_canonicalFixedLeftOverlapFiber
          C target O k hkCard
      calc
        (∫ z,
            (2 *
                C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
                  target O k z +
              2 * (P.variation
                (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2) ∂μ) =
          2 * (∫ z,
              C.independentPairHybridTargetTrajectoryCanonicalFixedLeftOverlapFiberEnergyBCF
                target O k z ∂μ) +
            2 * (P.variation
              (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2 := by
                rw [integral_add (hFiber.const_mul 2) (integrable_const _),
                  integral_const_mul]
                simp
        _ = 2 * C.independentPairHybridSourceOverlapTransportEnergyBCF
              target (C.hybridTargetTrajectorySourceAtRank target k) O +
            2 * (P.variation
              (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2 := by
                rw [← hPullback]

/-- At full canonical rank, the finite variation-square selector sum is exactly
the sum over all physical source links. -/
theorem continuous_compact_oriented_hybridTargetTrajectoryVariation_sq_sum_fullRank_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O) :
    (∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
      (P.variation (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2) =
      ∑ source : C.base.geometry.Edge, (P.variation source) ^ 2 := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  simpa [
    ContinuousCompactOrientedGaugeWilsonSystem.hybridTargetTrajectorySourceAtRank]
    using
      (C.canonicalEdgeOrder.symm.bijective.sum_comp
        (fun source : C.base.geometry.Edge => (P.variation source) ^ 2))

/-- Full-rank Gibbs-averaged endpoint trajectory energy is controlled by the
established hybrid boundary residual source-overlap path energy plus the complete
observable-specific source-variation square budget. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_le_boundaryResidualPath_add_variation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    [T2Space C.base.Gauge]
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O) :
    C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
        target O (Fintype.card C.base.geometry.Edge) ≤
      (Fintype.card C.base.geometry.Edge : ℝ) *
        (2 * C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O +
          2 * ∑ source : C.base.geometry.Edge,
            (P.variation source) ^ 2) := by
  calc
    C.independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF
        target O (Fintype.card C.base.geometry.Edge) ≤
      (Fintype.card C.base.geometry.Edge : ℝ) *
        ∑ k ∈ Finset.range (Fintype.card C.base.geometry.Edge),
          (2 * C.independentPairHybridSourceOverlapTransportEnergyBCF
              target (C.hybridTargetTrajectorySourceAtRank target k) O +
            2 * (P.variation
              (C.hybridTargetTrajectorySourceAtRank target k)) ^ 2) :=
        continuous_compact_oriented_independentPairHybridTargetTrajectoryCanonicalSourceBackgroundEndpointJointEnergyBCF_le_sum_sourceOverlap_add_variation
          C target O P (Fintype.card C.base.geometry.Edge) le_rfl
    _ = (Fintype.card C.base.geometry.Edge : ℝ) *
        (2 * C.hybridBoundaryResidualSourceOverlapPathEnergyBCF target O +
          2 * ∑ source : C.base.geometry.Edge,
            (P.variation source) ^ 2) := by
      congr 1
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [continuous_compact_oriented_independentPairHybridSourceOverlapTransportEnergyBCF_sum_fullRank_eq_boundaryResidualPath
        C target O]
      rw [continuous_compact_oriented_hybridTargetTrajectoryVariation_sq_sum_fullRank_eq
        C target O P]

end

end MathlibAnalytic
end MGAP4D
