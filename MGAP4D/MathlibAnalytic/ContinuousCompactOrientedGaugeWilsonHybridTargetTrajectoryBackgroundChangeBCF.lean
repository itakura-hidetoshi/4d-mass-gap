import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryTransportEnergyBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

/-- Observable value obtained by inserting trajectory coordinate `k` into the
step-dependent background `backgroundAt k`.  As in the fixed-background layer,
the zero fallback only totalizes the natural-number index. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (x : (i : Finset.Iic m) → C.base.Gauge) : ℝ :=
  if h : k ≤ m then
    O (C.base.replaceLink (backgroundAt k) target
      (x ⟨k, Finset.mem_Iic.2 h⟩))
  else 0

@[simp]
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (hkm : k ≤ m)
    (x : (i : Finset.Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF
        backgroundAt target O m k x =
      O (C.base.replaceLink (backgroundAt k) target
        (x ⟨k, Finset.mem_Iic.2 hkm⟩)) := by
  simp [
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF,
    hkm]

/-- Endpoint observable transport when each trajectory coordinate is interpreted
in its own source-dependent background. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (x : (i : Finset.Iic m) → C.base.Gauge) : ℝ :=
  C.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF
      backgroundAt target O m 0 x -
    C.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF
      backgroundAt target O m m x

/-- One adjacent source-background trajectory increment. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (x : (i : Finset.Iic m) → C.base.Gauge) : ℝ :=
  C.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF
      backgroundAt target O m k x -
    C.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF
      backgroundAt target O m (k + 1) x

/-- The fixed-left-background target transport on one genuine adjacent step.
The range-zero fallback keeps the natural-number index total. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (x : (i : Finset.Iic m) → C.base.Gauge) : ℝ :=
  if h : k + 1 ≤ m then
    C.singleLinkConditionalOverlapObservableTransportBCF
      (backgroundAt k) target O
      (x ⟨k, Finset.mem_Iic.2 (k.le_succ.trans h)⟩,
        x ⟨k + 1, Finset.mem_Iic.2 h⟩)
  else 0

/-- The residual generated solely by changing the observable background from
`backgroundAt k` to `backgroundAt (k + 1)`, while keeping the newly sampled
target-link value fixed. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (x : (i : Finset.Iic m) → C.base.Gauge) : ℝ :=
  if h : k + 1 ≤ m then
    O (C.base.replaceLink (backgroundAt k) target
        (x ⟨k + 1, Finset.mem_Iic.2 h⟩)) -
      O (C.base.replaceLink (backgroundAt (k + 1)) target
        (x ⟨k + 1, Finset.mem_Iic.2 h⟩))
  else 0

/-- Exact adjacent-step decomposition: source-dependent transport equals the
existing fixed-left-background overlap transport plus one explicit background
change residual.  No invariance of the observable under background replacement
is assumed. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF_eq_fixedLeft_add_backgroundChange
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m k : ℕ)
    (hkm : k + 1 ≤ m)
    (x : (i : Finset.Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF
        backgroundAt target O m k x =
      C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
          backgroundAt target O m k x +
        C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
          backgroundAt target O m k x := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF
  rw [
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C backgroundAt target O m k (k.le_succ.trans hkm) x,
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF_of_le
      C backgroundAt target O m (k + 1) hkm x]
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalOverlapObservableTransportBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
  simp [hkm]

/-- Exact telescoping remains valid with step-dependent backgrounds because the
coordinate values themselves still form one finite scalar path. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_eq_sum_adjacent
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (x : (i : Finset.Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
        backgroundAt target O m x =
      ∑ k ∈ Finset.range m,
        C.independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF
          backgroundAt target O m k x := by
  let v : ℕ → ℝ := fun k =>
    C.independentPairHybridTargetTrajectorySourceBackgroundInsertedObservableValueBCF
      backgroundAt target O m k x
  have hTel := Finset.sum_range_sub (fun k => -v k) m
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF
  change v 0 - v m = ∑ k ∈ Finset.range m, (v k - v (k + 1))
  calc
    v 0 - v m = (-v m) - (-v 0) := by ring
    _ = ∑ k ∈ Finset.range m, ((-v (k + 1)) - (-v k)) := hTel.symm
    _ = ∑ k ∈ Finset.range m, (v k - v (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      ring

/-- The full source-background endpoint transport is exactly the sum of the
fixed-left overlap transports plus the explicit background-change residuals. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_eq_sum_fixedLeft_add_backgroundChange
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (x : (i : Finset.Iic m) → C.base.Gauge) :
    C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
        backgroundAt target O m x =
      ∑ k ∈ Finset.range m,
        (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
            backgroundAt target O m k x +
          C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
            backgroundAt target O m k x) := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_eq_sum_adjacent]
  apply Finset.sum_congr rfl
  intro k hk
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundAdjacentTransportBCF_eq_fixedLeft_add_backgroundChange
      C backgroundAt target O m k
      (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)) x

/-- Finite Cauchy--Schwarz plus `(a+b)^2 ≤ 2a^2+2b^2` isolates the additional
energy that must be controlled when moving from a common observable background
to source-dependent backgrounds. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_sq_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (backgroundAt : ℕ → C.base.Configuration)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (m : ℕ)
    (x : (i : Finset.Iic m) → C.base.Gauge) :
    (C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
        backgroundAt target O m x) ^ 2 ≤
      (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 *
              (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
                backgroundAt target O m k x) ^ 2 +
            2 *
              (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
                backgroundAt target O m k x) ^ 2) := by
  let a : ℕ → ℝ := fun k =>
    C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
      backgroundAt target O m k x
  let b : ℕ → ℝ := fun k =>
    C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
      backgroundAt target O m k x
  have hEndpoint :
      C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
          backgroundAt target O m x =
        ∑ k ∈ Finset.range m, (a k + b k) := by
    simpa [a, b] using
      continuous_compact_oriented_independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF_eq_sum_fixedLeft_add_backgroundChange
        C backgroundAt target O m x
  have hCS :=
    sq_sum_le_card_mul_sum_sq
      (s := Finset.range m)
      (f := fun k => a k + b k)
  calc
    (C.independentPairHybridTargetTrajectorySourceBackgroundEndpointTransportBCF
        backgroundAt target O m x) ^ 2 =
      (∑ k ∈ Finset.range m, (a k + b k)) ^ 2 := by rw [hEndpoint]
    _ ≤ (m : ℝ) * ∑ k ∈ Finset.range m, (a k + b k) ^ 2 := by
      simpa using hCS
    _ ≤ (m : ℝ) *
        ∑ k ∈ Finset.range m, (2 * (a k) ^ 2 + 2 * (b k) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro k hk
        nlinarith [sq_nonneg (a k - b k)]
      · positivity
    _ = (m : ℝ) *
        ∑ k ∈ Finset.range m,
          (2 *
              (C.independentPairHybridTargetTrajectoryFixedLeftOverlapTransportBCF
                backgroundAt target O m k x) ^ 2 +
            2 *
              (C.independentPairHybridTargetTrajectoryAdjacentBackgroundChangeBCF
                backgroundAt target O m k x) ^ 2) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
