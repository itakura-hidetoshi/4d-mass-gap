import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryLaw
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonConditionalOverlapTransportEnergyBCF
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function Set
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- The observable value obtained by inserting trajectory coordinate `k` into one
fixed common background.  The zero fallback makes this a total function of a
natural-number index; all path theorems below use only indices at most `m`. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryInsertedObservableValueBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (x : (i : Iic m) → C.base.Gauge) : ℝ :=
  if h : k ≤ m then
    O (C.base.replaceLink background target x⟨k, mem_Iic.2 h⟩)
  else 0

/-- On an index inside the finite trajectory, the total inserted observable value
reduces to the expected coordinate insertion. -/
@[simp]
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryInsertedObservableValueBCF_of_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (hkm : k ≤ m)
    (x : (i : Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectoryInsertedObservableValueBCF
        background target O m k x =
      O (C.base.replaceLink background target x⟨k, mem_Iic.2 hkm⟩) := by
  simp [
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryInsertedObservableValueBCF,
    hkm]

/-- Every fixed trajectory coordinate gives a continuous inserted observable. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryInsertedObservableValueBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryInsertedObservableValueBCF
        background target O m k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryInsertedObservableValueBCF
  split_ifs with h
  · exact O.continuous.comp
      ((continuous_compact_oriented_replaceLink_uncurry C target).comp
        (continuous_const.prodMk (by fun_prop)))
  · exact continuous_const

/-- Fixed-background observable transport between the first and last values of a
finite target trajectory. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (x : (i : Iic m) → C.base.Gauge) : ℝ :=
  C.independentPairHybridTargetTrajectoryInsertedObservableValueBCF
      background target O m 0 x -
    C.independentPairHybridTargetTrajectoryInsertedObservableValueBCF
      background target O m m x

/-- Fixed-background observable transport across one adjacent trajectory step. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (x : (i : Iic m) → C.base.Gauge) : ℝ :=
  C.independentPairHybridTargetTrajectoryInsertedObservableValueBCF
      background target O m k x -
    C.independentPairHybridTargetTrajectoryInsertedObservableValueBCF
      background target O m (k + 1) x

/-- The endpoint transport has the explicit first/last coordinate formula. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportBCF_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (x : (i : Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectoryEndpointTransportBCF
        background target O m x =
      C.singleLinkConditionalOverlapObservableTransportBCF
        background target O
        (x⟨0, mem_Iic.2 (zero_le m)⟩,
          x⟨m, mem_Iic.2 le_rfl⟩) := by
  simp [
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportBCF]

/-- An adjacent transport inside the trajectory is exactly the existing
fixed-background overlap observable transport applied to that coordinate pair. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportBCF_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (hkm : k + 1 ≤ m)
    (x : (i : Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
        background target O m k x =
      C.singleLinkConditionalOverlapObservableTransportBCF
        background target O
        (x⟨k, mem_Iic.2 (k.le_succ.trans hkm)⟩,
          x⟨k + 1, mem_Iic.2 hkm⟩) := by
  simp [
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentTransportBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportBCF,
    hkm,
    k.le_succ.trans hkm]

/-- Endpoint transport is continuous on the finite trajectory space. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryEndpointTransportBCF
        background target O m) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportBCF
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryInsertedObservableValueBCF_continuous
      C background target O m 0).sub
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryInsertedObservableValueBCF_continuous
        C background target O m m)

/-- Every adjacent transport is continuous on the finite trajectory space. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportBCF_continuous
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Continuous
      (C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
        background target O m k) := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentTransportBCF
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryInsertedObservableValueBCF_continuous
      C background target O m k).sub
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryInsertedObservableValueBCF_continuous
        C background target O m (k + 1))

/-- Exact pointwise telescoping of the fixed-background target observable along
one finite trajectory. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportBCF_eq_sum_adjacent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (x : (i : Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectoryEndpointTransportBCF
        background target O m x =
      ∑ k ∈ Finset.range m,
        C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
          background target O m k x := by
  have hTel := Finset.sum_range_sub
    (fun k =>
      -C.independentPairHybridTargetTrajectoryInsertedObservableValueBCF
        background target O m k x) m
  simpa [
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportBCF,
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentTransportBCF]
    using hTel.symm

/-- Finite Cauchy--Schwarz converts exact telescoping into a pointwise square
bound by the sum of adjacent square transports. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportBCF_sq_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (x : (i : Iic m) → C.base.Gauge) :
    (C.independentPairHybridTargetTrajectoryEndpointTransportBCF
        background target O m x) ^ 2 ≤
      (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
            background target O m k x) ^ 2 := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportBCF_eq_sum_adjacent]
  simpa using
    (sq_sum_le_card_mul_sum_sq
      (s := Finset.range m)
      (f := fun k =>
        C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
          background target O m k x))

/-- Expected square endpoint transport under the finite target trajectory law. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) : ℝ :=
  ∫ x,
    (C.independentPairHybridTargetTrajectoryEndpointTransportBCF
      background target O m x) ^ 2
    ∂C.independentPairHybridTargetTrajectoryMeasure A B target m

/-- Expected square transport of one adjacent step under the finite target
trajectory law. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentTransportEnergyBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) : ℝ :=
  ∫ x,
    (C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
      background target O m k x) ^ 2
    ∂C.independentPairHybridTargetTrajectoryMeasure A B target m

/-- The endpoint square transport is integrable under the trajectory law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    Integrable
      (fun x =>
        (C.independentPairHybridTargetTrajectoryEndpointTransportBCF
          background target O m x) ^ 2)
      (C.independentPairHybridTargetTrajectoryMeasure A B target m) := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportBCF_continuous
      C background target O m).pow 2 |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Every adjacent square transport is integrable under the trajectory law. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportBCF_sq_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ) :
    Integrable
      (fun x =>
        (C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
          background target O m k x) ^ 2)
      (C.independentPairHybridTargetTrajectoryMeasure A B target m) := by
  exact
    (continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportBCF_continuous
      C background target O m k).pow 2 |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- The expected square of one genuine adjacent trajectory step is exactly the
fixed-background overlap transport energy for the corresponding consecutive
hybrid conditional laws. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportEnergyBCF_eq_overlap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (hkm : k + 1 ≤ m) :
    C.independentPairHybridTargetTrajectoryAdjacentTransportEnergyBCF
        A B background target O m k =
      C.singleLinkConditionalOverlapObservableTransportEnergyBCF
        (C.independentPairHybridConfiguration A B k)
        (C.independentPairHybridConfiguration A B (k + 1))
        background target O := by
  let pairMap : ((i : Iic m) → C.base.Gauge) →
      C.base.Gauge × C.base.Gauge :=
    fun x =>
      (x⟨k, mem_Iic.2 (k.le_succ.trans hkm)⟩,
        x⟨k + 1, mem_Iic.2 hkm⟩)
  have hPair : Measurable pairMap :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hIntegrand : StronglyMeasurable
      (fun z : C.base.Gauge × C.base.Gauge =>
        (C.singleLinkConditionalOverlapObservableTransportBCF
          background target O z) ^ 2) :=
    (continuous_compact_oriented_singleLinkConditionalOverlapObservableTransportBCF_continuous
      C background target O).pow 2 |>.stronglyMeasurable
  have hAdjacent :
      (fun x : (i : Iic m) → C.base.Gauge =>
        (C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
          background target O m k x) ^ 2) =
        fun x =>
          (C.singleLinkConditionalOverlapObservableTransportBCF
            background target O (pairMap x)) ^ 2 := by
    funext x
    rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportBCF_eq
      C background target O m k hkm x]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentTransportEnergyBCF
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportEnergyBCF
  rw [hAdjacent]
  rw [← MeasureTheory.integral_map hPair.aemeasurable
    hIntegrand.aestronglyMeasurable]
  rw [continuous_compact_oriented_map_adjacent_independentPairHybridTargetTrajectoryMeasure_eq_overlap
    C A B target k m hkm]

/-- The endpoint square transport energy is bounded by the finite-path length
times the exact sum of consecutive fixed-background overlap transport energies. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportEnergyBCF_le_sum_overlap
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B background : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ) :
    C.independentPairHybridTargetTrajectoryEndpointTransportEnergyBCF
        A B background target O m ≤
      (m : ℝ) *
        ∑ k ∈ Finset.range m,
          C.singleLinkConditionalOverlapObservableTransportEnergyBCF
            (C.independentPairHybridConfiguration A B k)
            (C.independentPairHybridConfiguration A B (k + 1))
            background target O := by
  let μ := C.independentPairHybridTargetTrajectoryMeasure A B target m
  have hLeft : Integrable
      (fun x =>
        (C.independentPairHybridTargetTrajectoryEndpointTransportBCF
          background target O m x) ^ 2) μ := by
    simpa [μ] using
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportBCF_sq_integrable
        C A B background target O m
  have hRightContinuous : Continuous
      (fun x : (i : Iic m) → C.base.Gauge =>
        (m : ℝ) *
          ∑ k ∈ Finset.range m,
            (C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
              background target O m k x) ^ 2) := by
    apply continuous_const.mul
    apply continuous_finset_sum
    intro k _hk
    exact
      (continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportBCF_continuous
        C background target O m k).pow 2
  have hRight : Integrable
      (fun x : (i : Iic m) → C.base.Gauge =>
        (m : ℝ) *
          ∑ k ∈ Finset.range m,
            (C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
              background target O m k x) ^ 2) μ :=
    hRightContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointTransportEnergyBCF
  calc
    (∫ x,
        (C.independentPairHybridTargetTrajectoryEndpointTransportBCF
          background target O m x) ^ 2 ∂μ) ≤
      ∫ x,
        (m : ℝ) *
          ∑ k ∈ Finset.range m,
            (C.independentPairHybridTargetTrajectoryAdjacentTransportBCF
              background target O m k x) ^ 2 ∂μ := by
        apply integral_mono hLeft hRight
        intro x
        exact
          continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointTransportBCF_sq_le
            C background target O m x
    _ = (m : ℝ) *
        ∑ k ∈ Finset.range m,
          C.independentPairHybridTargetTrajectoryAdjacentTransportEnergyBCF
            A B background target O m k := by
      rw [integral_const_mul]
      congr 1
      rw [integral_finset_sum]
      intro k _hk
      exact
        continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportBCF_sq_integrable
          C A B background target O m k
    _ = (m : ℝ) *
        ∑ k ∈ Finset.range m,
          C.singleLinkConditionalOverlapObservableTransportEnergyBCF
            (C.independentPairHybridConfiguration A B k)
            (C.independentPairHybridConfiguration A B (k + 1))
            background target O := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryAdjacentTransportEnergyBCF_eq_overlap
        C A B background target O m k
        (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))]

end

end MathlibAnalytic
end MGAP4D
