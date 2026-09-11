import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryBackgroundChangeBCF
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Every source-background inserted observable coordinate is continuous on the
finite target-trajectory carrier. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF
        backgroundAt target O m k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF
  split_ifs with h
  · exact O.continuous.comp
      ((continuous_compact_oriented_replaceLink_uncurry C target).comp
        (continuous_const.prodMk
          (continuous_apply (⟨k, Finset.mem_Iic.2 h⟩ : Finset.Iic m))))
  · exact continuous_const

/-- Source-background endpoint transport is continuous. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
        backgroundAt target O m) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_continuous
      C backgroundAt target O m 0).sub
      (continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_continuous
        C backgroundAt target O m m)

/-- The fixed-left part of every adjacent decomposition is continuous. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
        backgroundAt target O m k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
  split_ifs with h
  · exact
      (continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_continuous
        C (backgroundAt k) target O).comp
        ((continuous_apply
            (⟨k, Finset.mem_Iic.2 (k.le_succ.trans h)⟩ : Finset.Iic m)).prodMk
          (continuous_apply
            (⟨k + 1, Finset.mem_Iic.2 h⟩ : Finset.Iic m)))
  · exact continuous_const

/-- The explicit background-change residual is continuous. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
        backgroundAt target O m k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
  split_ifs with h
  · have hEval : Continuous
        (fun x : (i : Finset.Iic m) → C.base.Gauge =>
          x ⟨k + 1, Finset.mem_Iic.2 h⟩) :=
      continuous_apply (⟨k + 1, Finset.mem_Iic.2 h⟩ : Finset.Iic m)
    have hLeft : Continuous
        (fun x : (i : Finset.Iic m) → C.base.Gauge =>
          C.base.replaceLink (backgroundAt k) target
            (x ⟨k + 1, Finset.mem_Iic.2 h⟩)) :=
      (continuous_compact_oriented_replaceLink_uncurry C target).comp
        (continuous_const.prodMk hEval)
    have hRight : Continuous
        (fun x : (i : Finset.Iic m) → C.base.Gauge =>
          C.base.replaceLink (backgroundAt (k + 1)) target
            (x ⟨k + 1, Finset.mem_Iic.2 h⟩)) :=
      (continuous_compact_oriented_replaceLink_uncurry C target).comp
        (continuous_const.prodMk hEval)
    exact (O.continuous.comp hLeft).sub (O.continuous.comp hRight)
  · exact continuous_const

/-- Expected square source-background endpoint transport. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) : ℝ :=
  ∫ x,
    (C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
      backgroundAt target O m x) ^ 2
    ∂C.independentPairHybridTargetTrajectoryMeasure A B target m

/-- Expected square fixed-left overlap transport at one adjacent trajectory step. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) : ℝ :=
  ∫ x,
    (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
      backgroundAt target O m k x) ^ 2
    ∂C.independentPairHybridTargetTrajectoryMeasure A B target m

/-- Expected square of the explicit adjacent background-change residual. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) : ℝ :=
  ∫ x,
    (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
      backgroundAt target O m k x) ^ 2
    ∂C.independentPairHybridTargetTrajectoryMeasure A B target m

/-- The endpoint square transport is integrable under the finite trajectory law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    Integrable
      (fun x =>
        (C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
          backgroundAt target O m x) ^ 2)
      (C.independentPairHybridTargetTrajectoryMeasure A B target m) := by
  exact
    ((continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_continuous
      C backgroundAt target O m).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Every fixed-left adjacent square transport is integrable. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Integrable
      (fun x =>
        (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
          backgroundAt target O m k x) ^ 2)
      (C.independentPairHybridTargetTrajectoryMeasure A B target m) := by
  exact
    ((continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF_continuous
      C backgroundAt target O m k).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Every adjacent background-change square residual is integrable. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Integrable
      (fun x =>
        (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
          backgroundAt target O m k x) ^ 2)
      (C.independentPairHybridTargetTrajectoryMeasure A B target m) := by
  exact
    ((continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF_continuous
      C backgroundAt target O m k).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Endpoint source-background transport energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    0 ≤ C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
      A B backgroundAt target O m := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
  exact integral_nonneg fun x => sq_nonneg _

/-- Adjacent background-change energy is nonnegative. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF_nonneg
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    0 ≤ C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
      A B backgroundAt target O m k := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
  exact integral_nonneg fun x => sq_nonneg _

/-- On a genuine adjacent step, the total fixed-left transport is the fixed-background
adjacent transport already used in the trajectory-energy layer. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF_eq_adjacent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (hkm : k + 1 ≤ m)
    (x : (i : Finset.Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
        backgroundAt target O m k x =
      C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
        (backgroundAt k) target O m k x := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportBCF_eq
    C (backgroundAt k) target O m k hkm x]
  simp
    [ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF,
      hkm]

/-- The expected fixed-left square at a genuine adjacent step is exactly the
existing fixed-background overlap transport energy for that step. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportEnergyBCF_eq_overlap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (hkm : k + 1 ≤ m) :
    C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportEnergyBCF
        A B backgroundAt target O m k =
      C.singleLinkConditionalOverlapObservableTransportEnergyBCF
        (C.independentPairHybridConfiguration A B k)
        (C.independentPairHybridConfiguration A B (k + 1))
        (backgroundAt k) target O := by
  calc
    C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportEnergyBCF
        A B backgroundAt target O m k =
      C.independentPairHybridTargetTrajectoryAdjacentTransportEnergyBCF
        A B (backgroundAt k) target O m k := by
          unfold
            ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportEnergyBCF
            ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentTransportEnergyBCF
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x =>
            congrArg (fun y : ℝ => y ^ 2)
              (continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF_eq_adjacent
                C backgroundAt target O m k hkm x)
    _ = C.singleLinkConditionalOverlapObservableTransportEnergyBCF
        (C.independentPairHybridConfiguration A B k)
        (C.independentPairHybridConfiguration A B (k + 1))
        (backgroundAt k) target O :=
      continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportEnergyBCF_eq_overlap
        C A B (backgroundAt k) target O m k hkm

/-- Integrating the pointwise background-change decomposition gives an endpoint
energy bound by the exact fixed-left overlap energies plus the new explicit
background-change energies. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF_le_sum_overlap_add_backgroundChange
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
        A B backgroundAt target O m ≤
      (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 *
              C.singleLinkConditionalOverlapObservableTransportEnergyBCF
                (C.independentPairHybridConfiguration A B k)
                (C.independentPairHybridConfiguration A B (k + 1))
                (backgroundAt k) target O +
            2 *
              C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
                A B backgroundAt target O m k) := by
  let μ := C.independentPairHybridTargetTrajectoryMeasure A B target m
  have hLeft : Integrable
      (fun x =>
        (C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
          backgroundAt target O m x) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_sq_integrable
        C A B backgroundAt target O m
  have hRightContinuous : Continuous
      (fun x : (i : Finset.Iic m) → C.base.Gauge =>
        (m : ℝ) *
          ∑ k ∈ Finset.range m,
            (2 *
                (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
                  backgroundAt target O m k x) ^ 2 +
              2 *
                (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
                  backgroundAt target O m k x) ^ 2)) := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro k _hk
    exact
      (continuous_const.mul
        ((continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF_continuous
          C backgroundAt target O m k).pow 2)).add
        (continuous_const.mul
          ((continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF_continuous
            C backgroundAt target O m k).pow 2))
  have hRight : Integrable
      (fun x : (i : Finset.Iic m) → C.base.Gauge =>
        (m : ℝ) *
          ∑ k ∈ Finset.range m,
            (2 *
                (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
                  backgroundAt target O m k x) ^ 2 +
              2 *
                (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
                  backgroundAt target O m k x) ^ 2)) μ :=
    hRightContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportEnergyBCF
  calc
    (∫ x,
        (C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
          backgroundAt target O m x) ^ 2 ∂μ) ≤
      ∫ x,
        (m : ℝ) *
          ∑ k ∈ Finset.range m,
            (2 *
                (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
                  backgroundAt target O m k x) ^ 2 +
              2 *
                (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
                  backgroundAt target O m k x) ^ 2) ∂μ := by
        apply integral_mono hLeft hRight
        intro x
        exact
          continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_sq_le
            C backgroundAt target O m x
    _ = (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 *
              C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportEnergyBCF
                A B backgroundAt target O m k +
            2 *
              C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
                A B backgroundAt target O m k) := by
      rw [integral_const_mul]
      congr 1
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro k _hk
        have hFixedScaled : Integrable
            (fun x : (i : Finset.Iic m) → C.base.Gauge =>
              (2 : ℝ) *
                (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
                  backgroundAt target O m k x) ^ 2) μ :=
          (continuous_const.mul
            ((continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF_continuous
              C backgroundAt target O m k).pow 2)).integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)
        have hBackgroundScaled : Integrable
            (fun x : (i : Finset.Iic m) → C.base.Gauge =>
              (2 : ℝ) *
                (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
                  backgroundAt target O m k x) ^ 2) μ :=
          (continuous_const.mul
            ((continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF_continuous
              C backgroundAt target O m k).pow 2)).integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)
        rw [integral_add hFixedScaled hBackgroundScaled,
          integral_const_mul, integral_const_mul]
        rfl
      · intro k _hk
        exact
          ((continuous_const.mul
              ((continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF_continuous
                C backgroundAt target O m k).pow 2)).add
            (continuous_const.mul
              ((continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF_continuous
                C backgroundAt target O m k).pow 2))).integrable_of_hasCompactSupport
                  (HasCompactSupport.of_compactSpace _)
    _ = (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 *
              C.singleLinkConditionalOverlapObservableTransportEnergyBCF
                (C.independentPairHybridConfiguration A B k)
                (C.independentPairHybridConfiguration A B (k + 1))
                (backgroundAt k) target O +
            2 *
              C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeEnergyBCF
                A B backgroundAt target O m k) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryFixedLeftOverlapTransportEnergyBCF_eq_overlap
        C A B backgroundAt target O m k
        (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))]

end

end MathlibAnalytic
end MGAP4D
