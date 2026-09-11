import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryPairResidualCorePoincare
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace FiniteHybridPath

/-- Replace coordinates of `A` by those of `B` in the order prescribed by
`order`. At time `k`, precisely the coordinates whose ranks are strictly below
`k` have been replaced. -/
def configuration
    {ι X : Type*}
    [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (A B : ι → X)
    (k : ℕ) : ι → X :=
  fun i => if (order i).val < k then B i else A i

@[simp]
theorem configuration_zero
    {ι X : Type*}
    [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (A B : ι → X) :
    configuration order A B 0 = A := by
  funext i
  simp [configuration]

@[simp]
theorem configuration_card
    {ι X : Type*}
    [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (A B : ι → X) :
    configuration order A B (Fintype.card ι) = B := by
  funext i
  simp [configuration, (order i).isLt]

/-- A finite path controls its endpoint difference by the number of steps times
its squared increment energy. -/
theorem endpoint_sub_sq_le_card_mul_sum_increment_sq
    {ι X : Type*}
    [Fintype ι]
    (order : ι ≃ Fin (Fintype.card ι))
    (observable : (ι → X) → ℝ)
    (A B : ι → X) :
    (observable A - observable B) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        ∑ k : Fin (Fintype.card ι),
          (observable (configuration order A B (k.val + 1)) -
            observable (configuration order A B k.val)) ^ 2 := by
  let path : ℕ → ℝ := fun k => observable (configuration order A B k)
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.range (Fintype.card ι))
    (fun k => path (k + 1) - path k)
    (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow] at hCS
  have hTel :
      ∑ k ∈ Finset.range (Fintype.card ι),
          (path (k + 1) - path k) =
        path (Fintype.card ι) - path 0 := by
    simpa using (Finset.sum_range_sub path (Fintype.card ι))
  rw [hTel] at hCS
  have hPath :
      (path (Fintype.card ι) - path 0) ^ 2 ≤
        (Fintype.card ι : ℝ) *
          ∑ k ∈ Finset.range (Fintype.card ι),
            (path (k + 1) - path k) ^ 2 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hCS
  dsimp [path] at hPath
  rw [configuration_zero, configuration_card] at hPath
  calc
    (observable A - observable B) ^ 2 =
        (observable B - observable A) ^ 2 := by ring
    _ ≤ (Fintype.card ι : ℝ) *
        ∑ k ∈ Finset.range (Fintype.card ι),
          (observable (configuration order A B (k + 1)) -
            observable (configuration order A B k)) ^ 2 := hPath
    _ = (Fintype.card ι : ℝ) *
        ∑ k : Fin (Fintype.card ι),
          (observable (configuration order A B (k.val + 1)) -
            observable (configuration order A B k.val)) ^ 2 := by
      congr 1
      symm
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      simp [Finset.mem_range.mp hk]

end FiniteHybridPath

/-- Canonical finite ranking of the physical links of a compact oriented Wilson
system. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.canonicalEdgeOrder
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.base.geometry.Edge ≃ Fin (Fintype.card C.base.geometry.Edge) :=
  Fintype.equivFin C.base.geometry.Edge

/-- Hybrid configuration of an independent Gibbs pair, obtained by replacing
physical links one at a time in the canonical finite order. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridConfiguration
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (k : ℕ) : C.base.Configuration :=
  FiniteHybridPath.configuration C.canonicalEdgeOrder A B k

@[simp]
theorem continuous_compact_oriented_independentPairHybridConfiguration_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration) :
    C.independentPairHybridConfiguration A B 0 = A := by
  exact FiniteHybridPath.configuration_zero C.canonicalEdgeOrder A B

@[simp]
theorem continuous_compact_oriented_independentPairHybridConfiguration_card
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration) :
    C.independentPairHybridConfiguration A B
        (Fintype.card C.base.geometry.Edge) = B := by
  exact FiniteHybridPath.configuration_card C.canonicalEdgeOrder A B

/-- Observable increment at one canonical hybrid-path step. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridIncrementBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) : ℝ :=
  let k := (C.canonicalEdgeOrder target).val
  O (C.independentPairHybridConfiguration z.1 z.2 (k + 1)) -
    O (C.independentPairHybridConfiguration z.1 z.2 k)

/-- Every independent Gibbs-pair observable difference is controlled pointwise
by the finite sum of squared canonical hybrid increments. -/
theorem continuous_compact_oriented_independentPairDifference_sq_le_card_mul_sum_hybridIncrement_sq
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration) :
    (O A - O B) ^ 2 ≤
      (Fintype.card C.base.geometry.Edge : ℝ) *
        ∑ target : C.base.geometry.Edge,
          (C.independentPairHybridIncrementBCF target O (A, B)) ^ 2 := by
  have h := FiniteHybridPath.endpoint_sub_sq_le_card_mul_sum_increment_sq
    C.canonicalEdgeOrder O A B
  have hReindex :
      (∑ target : C.base.geometry.Edge,
          (C.independentPairHybridIncrementBCF target O (A, B)) ^ 2) =
        ∑ k : Fin (Fintype.card C.base.geometry.Edge),
          (O (C.independentPairHybridConfiguration A B (k.val + 1)) -
            O (C.independentPairHybridConfiguration A B k.val)) ^ 2 := by
    rw [← C.canonicalEdgeOrder.sum_comp]
    rfl
  rw [hReindex]
  exact h

end

end MathlibAnalytic
end MGAP4D
