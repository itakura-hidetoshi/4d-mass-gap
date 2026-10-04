import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovSummableAdjacentDefect
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PhysicalDirectedClosureTransferContraction
import Mathlib.Tactic

/-!
# Adjacent common-marginal SU(2) transfer compressions

For two consecutive lattice scales n and n+1, both finite Krylov vectors can be
transported isometrically into the union marginal

  I_n = R.marginalIndex n ∪ R.marginalIndex (n+1).

This file places the two actual normalized physical pair transfers on that same
finite Hilbert space.

For each side we compose

  pair Haar
    -> selected finite marginal
    -> union finite marginal,

obtaining an isometric embedding.  We then apply the existing
physical-carrier-projected compression construction to get two bounded
endomorphisms A_n^L and A_n^R of the *same* union-marginal L2 space.

Both operators have norm at most one and act exactly as the corresponding
finite normalized pair transfer on embedded physical pair vectors.  Natural
powers therefore intertwine exactly.

Consequently the #5096 adjacent finite Krylov defect is exactly

  || (A_n^L)^m v_{n,k}^L - (A_n^R)^m v_{n,k}^R ||,

where both initial vectors have norm one.

This is the finite common carrier needed for the subsequent perturbation
estimate.  No cross-scale operator compatibility is assumed here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped ENNReal InnerProductSpace InnerProduct Topology

noncomputable section

local instance su2AdjacentCommonTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance su2AdjacentCommonCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance su2AdjacentCommonSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance su2AdjacentCommonMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance su2AdjacentCommonBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance su2AdjacentCommonSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance su2AdjacentCommonSpatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

local instance su2AdjacentCommonNontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

section AdjacentCommonTransfer

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 specialUnitaryTwoWilsonRankPositive beta hbeta)
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    (R : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMarginalProjectiveReadout Q F)

/-- Union marginal for the adjacent scales n and n+1. -/
def physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
    (n : ℕ) :
    Finset EuclideanFourSpace :=
  R.marginalIndex n ∪ R.marginalIndex (n + 1)

/-- Isometric embedding of the coarse pair-Haar carrier into the adjacent
union marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonLeftPairEmbedding
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2 →ₗᵢ[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
      (F := F)
      (show R.marginalIndex n ⊆
          physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n by
        exact Finset.subset_union_left)).comp
    (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R n)

/-- Isometric embedding of the fine pair-Haar carrier into the same adjacent
union marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonRightPairEmbedding
    (n : ℕ) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2 →ₗᵢ[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  (EuclideanYangMillsProjectiveLimitMeasure.finiteMarginalL2Transition
      (F := F)
      (show R.marginalIndex (n + 1) ⊆
          physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n by
        exact Finset.subset_union_right)).comp
    (physicalYangMillsSU2PairHaarProjectiveFiniteEmbedding Q R (n + 1))

local instance su2AdjacentCommonPhysicalPairCarrierComplete (n : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2) := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
  infer_instance

/-- Coarse normalized physical pair transfer compressed to the common adjacent
union marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonLeftTransfer
    (n : ℕ) :
    Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) →L[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  realLinearIsometrySubspaceProjectedCompression
    (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent n) 2)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n))

/-- Fine normalized physical pair transfer compressed to the same common
adjacent union marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonRightTransfer
    (n : ℕ) :
    Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) →L[ℝ]
      Lp ℝ 2
        (F.finiteMarginal
          (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
            (Q := Q) R n)) :=
  realLinearIsometrySubspaceProjectedCompression
    (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n)
    (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
      (halfExtent (n + 1)) 2)
    (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1)))

@[simp]
theorem physicalYangMillsSU2AdjacentCommonLeftTransfer_apply_embedding
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2)
    (hx :
      x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
          (halfExtent n) 2) :
    physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n
        (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n x) =
      physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) x) := by
  unfold physicalYangMillsSU2AdjacentCommonLeftTransfer
  exact
    realLinearIsometrySubspaceProjectedCompression_apply_map_mem
      (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n))
      x hx

@[simp]
theorem physicalYangMillsSU2AdjacentCommonRightTransfer_apply_embedding
    (n : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2)
    (hx :
      x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
          (halfExtent (n + 1)) 2) :
    physicalYangMillsSU2AdjacentCommonRightTransfer Q R n
        (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n x) =
      physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta (n + 1)) (hbeta (n + 1)) x) := by
  unfold physicalYangMillsSU2AdjacentCommonRightTransfer
  exact
    realLinearIsometrySubspaceProjectedCompression_apply_map_mem
      (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent (n + 1)) 2)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta (n + 1)) (hbeta (n + 1)))
      x hx

theorem physicalYangMillsSU2AdjacentCommonLeftTransfer_opNorm_le_one
    (n : ℕ) :
    ‖physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n‖ ≤ 1 := by
  unfold physicalYangMillsSU2AdjacentCommonLeftTransfer
  apply
    realLinearIsometrySubspaceProjectedCompression_opNorm_le
      (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent n) 2)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n))
      1 zero_le_one
  intro x hx
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_norm_le_one
      (halfExtent n) (beta n) (hbeta n) x hx

theorem physicalYangMillsSU2AdjacentCommonRightTransfer_opNorm_le_one
    (n : ℕ) :
    ‖physicalYangMillsSU2AdjacentCommonRightTransfer Q R n‖ ≤ 1 := by
  unfold physicalYangMillsSU2AdjacentCommonRightTransfer
  apply
    realLinearIsometrySubspaceProjectedCompression_opNorm_le
      (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n)
      (periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
        (halfExtent (n + 1)) 2)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta (n + 1)) (hbeta (n + 1)))
      1 zero_le_one
  intro x hx
  simpa using
    periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_norm_le_one
      (halfExtent (n + 1)) (beta (n + 1)) (hbeta (n + 1)) x hx

/-- First-three finite mode belongs to the physical pair carrier. -/
theorem periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode_mem_physicalPairCarrier
    (H : ℕ) (k : Fin 3) :
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        H k ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier H 2 := by
  unfold periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
  exact
    periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairHaarL2_mem_physicalPairCarrier
      H k.1

/-- Exact natural-power intertwining for the coarse common-marginal transfer. -/
theorem physicalYangMillsSU2AdjacentCommonLeftTransfer_pow_apply_embedding
    (n m : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent n) 2)
    (hx :
      x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
          (halfExtent n) 2) :
    (physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n ^ m)
        (physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n x) =
      physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) ^ m) x) := by
  let A := physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
  let J := physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n
  change (A ^ m) (J x) = J ((T ^ m) x)
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      have hxT :
          T x ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
              (halfExtent n) 2 := by
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant
            (halfExtent n) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) hx
      change (A ^ m) (A (J x)) = J ((T ^ m) (T x))
      have hstep : A (J x) = J (T x) := by
        simpa [A, T, J] using
          physicalYangMillsSU2AdjacentCommonLeftTransfer_apply_embedding
            Q R n x hx
      rw [hstep]
      exact ih (T x) hxT

/-- Exact natural-power intertwining for the fine common-marginal transfer. -/
theorem physicalYangMillsSU2AdjacentCommonRightTransfer_pow_apply_embedding
    (n m : ℕ)
    (x :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
        (halfExtent (n + 1)) 2)
    (hx :
      x ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
          (halfExtent (n + 1)) 2) :
    (physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ m)
        (physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n x) =
      physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
        ((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta (n + 1)) (hbeta (n + 1)) ^ m) x) := by
  let A := physicalYangMillsSU2AdjacentCommonRightTransfer Q R n
  let T :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1))
  let J := physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
  change (A ^ m) (J x) = J ((T ^ m) x)
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      have hxT :
          T x ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier
              (halfExtent (n + 1)) 2 := by
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalPairCarrier_normalizedTransfer_invariant
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta (n + 1)) (hbeta (n + 1)) hx
      change (A ^ m) (A (J x)) = J ((T ^ m) (T x))
      have hstep : A (J x) = J (T x) := by
        simpa [A, T, J] using
          physicalYangMillsSU2AdjacentCommonRightTransfer_apply_embedding
            Q R n x hx
      rw [hstep]
      exact ih (T x) hxT

/-- Coarse initial Krylov vector in the common adjacent marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode
    (n : ℕ) (k : Fin 3) :
    Lp ℝ 2
      (F.finiteMarginal
        (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
          (Q := Q) R n)) :=
  physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
      (halfExtent n) k)

/-- Fine initial Krylov vector in the same common adjacent marginal. -/
noncomputable def physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode
    (n : ℕ) (k : Fin 3) :
    Lp ℝ 2
      (F.finiteMarginal
        (physicalYangMillsSU2ThreeModeAdjacentCommonMarginalIndex
          (Q := Q) R n)) :=
  physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
      (halfExtent (n + 1)) k)

@[simp]
theorem physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode_norm
    (n : ℕ) (k : Fin 3) :
    ‖physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode Q R n k‖ = 1 := by
  unfold physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode
  rw [(physicalYangMillsSU2AdjacentCommonLeftPairEmbedding Q R n).norm_map]
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode_orthonormal
      (halfExtent n)).norm_eq_one k

@[simp]
theorem physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode_norm
    (n : ℕ) (k : Fin 3) :
    ‖physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k‖ = 1 := by
  unfold physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode
  rw [(physicalYangMillsSU2AdjacentCommonRightPairEmbedding Q R n).norm_map]
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode_orthonormal
      (halfExtent (n + 1))).norm_eq_one k

/-- Exact finite common-carrier representation of the adjacent Krylov defect as
the distance between the two compressed transfer power orbits. -/
theorem physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect_eq_commonTransferPowerDifference
    (n m : ℕ) (k : Fin 3) :
    physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
        (Q := Q) (R := R) n m k =
      ‖(physicalYangMillsSU2AdjacentCommonLeftTransfer Q R n ^ m)
          (physicalYangMillsSU2AdjacentCommonLeftInitialKrylovMode Q R n k) -
        (physicalYangMillsSU2AdjacentCommonRightTransfer Q R n ^ m)
          (physicalYangMillsSU2AdjacentCommonRightInitialKrylovMode Q R n k)‖ := by
  rw [
    physicalYangMillsSU2AdjacentCommonLeftTransfer_pow_apply_embedding
      Q R n m
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent n) k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode_mem_physicalPairCarrier
        (halfExtent n) k),
    physicalYangMillsSU2AdjacentCommonRightTransfer_pow_apply_embedding
      Q R n m
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode
        (halfExtent (n + 1)) k)
      (periodicHypercubicEvenPrimarySpatialPlaquetteWilsonEnergyGramSchmidtPairFinThreeMode_mem_physicalPairCarrier
        (halfExtent (n + 1)) k)]
  unfold physicalYangMillsSU2ThreeModeFiniteAdjacentKrylovDefect
  unfold physicalYangMillsSU2ThreeModeFiniteCommonMarginalKrylovDefect
  unfold physicalYangMillsSU2ThreeModeEvolvedFiniteMarginalKrylovMode
  unfold physicalYangMillsSU2AdjacentCommonLeftPairEmbedding
  unfold physicalYangMillsSU2AdjacentCommonRightPairEmbedding
  rfl

end AdjacentCommonTransfer

end

end MathlibAnalytic
end MGAP4D
