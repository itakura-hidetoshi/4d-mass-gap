import MGAP4D.MathlibAnalytic.InfiniteProductProbabilityCoordinateL2Orthogonality
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCanonicalBoundaryVacuumAdjoint
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2PhysicalVacuumSector
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryDecay
import Mathlib.Tactic

/-!
# Top-mode / OS-boundary-vacuum compatibility and the independent-product obstruction

PR #4989 proves that centered vectors placed in fresh coordinates of an
independent infinite product cannot converge strongly to a nonzero vector.

The remaining Wilson-specific question is whether the #4984 one-sided
top-orthogonal boundary image is centered for the *actual interacting boundary
marginal*.  The exact missing compatibility is isolated here:

the actual finite OS boundary vacuum, after the canonical boundary-to-pair
Haar-L2 coordinate isometry, must equal the physically selected pair top mode
`Omega_top tensor Omega_top`.

Under precisely that compatibility, every #4984 finite excitation image is
centered in its interacting marginal coordinate, hence any strong limit of
fresh-scale coordinate images in the independent product is forced to be zero.

This file does not assert the compatibility.  It proves its exact consequence,
so the next model-facing task is no longer ambiguous.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Topology
open scoped InnerProductSpace

noncomputable section

local instance topBoundaryVacuumCenteringObstructionNeZero
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance topBoundaryVacuumCenteringObstructionTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance topBoundaryVacuumCenteringObstructionCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance topBoundaryVacuumCenteringObstructionSecondCountable
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance topBoundaryVacuumCenteringObstructionMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance topBoundaryVacuumCenteringObstructionBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Exact finite-volume compatibility required to identify the canonical OS
boundary vacuum with the physically selected pair top mode.

No one-dimensionality of the full top eigenspace is asserted. -/
def PeriodicHypercubicEvenSpecialUnitaryTopBoundaryVacuumCompatibility
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop :=
  periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
      (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta) =
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
      H N hN beta hbeta

/-- Under exact top/boundary-vacuum compatibility, every represented one-sided
physical top-orthogonal excitation is orthogonal to the actual finite OS
boundary vacuum in shared-boundary Haar L2. -/
theorem
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundary_inner_boundaryVacuum_eq_zero
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcompat :
      PeriodicHypercubicEvenSpecialUnitaryTopBoundaryVacuumCompatibility
        H N hN beta hbeta)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :
    inner ℝ
      (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
        H N hN beta hbeta x) = 0 := by
  let A :=
    periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePairLinearIsometry H N
  let B :=
    periodicHypercubicEvenSpatialSlicePairHaarL2ToBoundaryLinearIsometry H N
  let e :=
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationPairLinearIsometry
      H N hN beta hbeta x
  have hback :
      A
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
          H N hN beta hbeta x) = e := by
    change A (B e) = e
    exact periodicHypercubicEvenBoundaryHaarL2ToSpatialSlicePair_rightInverse
      H N e
  calc
    inner ℝ
        (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
          H N hN beta hbeta x) =
      inner ℝ
        (A (periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta))
        (A
          (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
            H N hN beta hbeta x)) := by
      symm
      exact A.inner_map_map _ _
    _ =
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2
          H N hN beta hbeta)
        e := by
      rw [hcompat, hback]
    _ = 0 := by
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairTopModeL2_inner_oneSidedExcitation_eq_zero
          H N hN beta hbeta x

/-- Reciprocal-vacuum transport then makes the same finite excitation centered
against the constant-one vector of the interacting boundary marginal. -/
theorem
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationMarginal_centered
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcompat :
      PeriodicHypercubicEvenSpecialUnitaryTopBoundaryVacuumCompatibility
        H N hN beta hbeta)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta) :
    inner ℝ
      (Lp.const 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          H N hN beta hbeta) (1 : ℝ))
      (periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
          H N hN beta hbeta x)) = 0 := by
  let M :=
    periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
      H N hN beta hbeta
  let vac :=
    periodicHypercubicEvenBoundaryVacuumL2 H N hN beta hbeta
  let exc :=
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
      H N hN beta hbeta x
  have hvac :
      M vac =
        Lp.const 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H N hN beta hbeta) (1 : ℝ) := by
    exact periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry_vacuum
      H N hN beta hbeta
  have horth : inner ℝ vac exc = 0 := by
    exact
      periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundary_inner_boundaryVacuum_eq_zero
        H N hN beta hbeta hcompat x
  calc
    inner ℝ
        (Lp.const 2
          (periodicHypercubicEvenBoundaryMarginalMeasure
            H N hN beta hbeta) (1 : ℝ))
        (M exc) =
      inner ℝ (M vac) (M exc) := by rw [hvac]
    _ = inner ℝ vac exc := M.inner_map_map vac exc
    _ = 0 := horth

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- Under scale-wise top/boundary-vacuum compatibility, the finite marginal
vector used inside the #4984 common-product embedding is centered at every
scale. -/
theorem
    periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleMarginal_centered
    (hcompat : ∀ n,
      PeriodicHypercubicEvenSpecialUnitaryTopBoundaryVacuumCompatibility
        (halfExtent n) N hN (beta n) (hbeta n))
    (x : (n : ℕ) →
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n))
    (n : ℕ) :
    inner ℝ
      (Lp.const 2
        (physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
          halfExtent N hN beta hbeta n)
        (1 : ℝ))
      ((periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
          (halfExtent n) N hN (beta n) (hbeta n)).comp
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
          (halfExtent n) N hN (beta n) (hbeta n))
        (x n)) = 0 := by
  change
    inner ℝ
      (Lp.const 2
        (periodicHypercubicEvenBoundaryMarginalMeasure
          (halfExtent n) N hN (beta n) (hbeta n))
        (1 : ℝ))
      (periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
        (halfExtent n) N hN (beta n) (hbeta n)
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
          (halfExtent n) N hN (beta n) (hbeta n) (x n))) = 0
  exact
    periodicHypercubicEvenSpecialUnitaryOneSidedExcitationMarginal_centered
      (halfExtent n) N hN (beta n) (hbeta n) (hcompat n) (x n)

/-- Consequently, if the actual OS boundary vacuum equals the selected pair top
mode at every scale, the #4984 independent-product embeddings of a moving
finite top-orthogonal excitation sequence can have a strong limit only at zero.

This is the Wilson-specific specialization of the #4988/#4989 obstruction. -/
theorem
    periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundary_tendsto_zero_of_topBoundaryVacuumCompatibility
    (hcompat : ∀ n,
      PeriodicHypercubicEvenSpecialUnitaryTopBoundaryVacuumCompatibility
        (halfExtent n) N hN (beta n) (hbeta n))
    (x : (n : ℕ) →
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n))
    (y :
      PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryL2
        halfExtent N hN beta hbeta)
    (hlim :
      Tendsto
        (fun n =>
          periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
            halfExtent N hN beta hbeta n (x n))
        atTop (𝓝 y)) :
    y = 0 := by
  let μ := fun n =>
    physicalYangMillsEvenPeriodicWilsonBoundaryScaleMarginalMeasure
      halfExtent N hN beta hbeta n
  let f := fun n =>
    (periodicHypercubicEvenBoundaryHaarToMarginalL2Isometry
      (halfExtent n) N hN (beta n) (hbeta n)).comp
        (periodicHypercubicEvenSpecialUnitaryOneSidedExcitationBoundaryLinearIsometry
          (halfExtent n) N hN (beta n) (hbeta n))
        (x n)
  have hcenter :
      ∀ n, inner ℝ (Lp.const 2 (μ n) (1 : ℝ)) (f n) = 0 := by
    intro n
    exact
      periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleMarginal_centered
        halfExtent N hN beta hbeta hcompat x n
  have hlim' :
      Tendsto
        (fun n =>
          infiniteProductProbabilityCoordinateL2Pullback μ n (f n))
        atTop (𝓝 y) := by
    simpa [μ, f,
      infiniteProductProbabilityCoordinateL2Pullback,
      physicalYangMillsEvenPeriodicWilsonBoundaryMarginalL2ToScaleCommon,
      periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry]
      using hlim
  exact
    infiniteProductProbabilityCoordinateL2Pullback_tendsto_zero_of_centered
      μ f hcenter y hlim'

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D
