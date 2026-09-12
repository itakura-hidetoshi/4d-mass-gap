import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSBoundarySpatialHalfWeightFactorization
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCoordinateTransferBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The spatial part of the complete unfixed positive-half-cylinder path action,
kept in the symmetric one-slab normal form.  Every slab contributes one half of
each of its two spatial boundary actions.  Consequently the two fixed endpoint
slices occur with coefficient `1/2`, while every strict interior slice occurs
once after adjacent slab contributions are combined. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) : ℝ :=
  ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
    ((1 / 2 : ℝ) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
          (path i.castSucc) +
      (1 / 2 : ℝ) *
        periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
          (path i.succ))

/-- The temporal part of the complete unfixed positive-half-cylinder path
action.  It contains exactly one unfixed temporal crossing action for each of
the `H+1` physical slabs. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) : ℝ :=
  ∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
    periodicHypercubicEvenSpecialUnitaryUnfixedTemporalCrossingAction H N
      (path i.castSucc) (U i) (path i.succ)

/-- The complete unfixed positive-half-cylinder action is exactly the sum of
its symmetric spatial half-action sector and its temporal crossing sector.
This is purely the finite-slab algebraic normal form; no OS/path geometric
identification is assumed here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction_eq_spatialHalf_add_temporal
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction H N path U =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
          H N path +
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
          H N path U := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold periodicHypercubicEvenSpecialUnitaryUnfixedOneSlabAction
  ring

/-- The symmetric spatial half-action can equivalently be written as the sum
of all lower-slab half-actions plus all upper-slab half-actions.  This form is
useful when the two reflection-fixed endpoint weights are extracted from the
actual OS boundary sector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction_eq_left_add_right
    (H N : ℕ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
        H N path =
      (∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path i.castSucc)) +
      (∑ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
        (1 / 2 : ℝ) *
          periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H N
            (path i.succ)) := by
  classical
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
  rw [Finset.sum_add_distrib]

/-- Boltzmann form of the complete unfixed positive-half-cylinder path kernel.
It is obtained from the already-proved pathwise temporal-gauge reduction and
therefore introduces no new gauge-fixing assumption. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_boltzmann
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta path U =
      Real.exp
        (-beta *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction
            H N path U) := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_temporalGauge]
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_boltzmann]
  rw [← periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction_eq_temporalGauge]

/-- Boltzmann weight of the symmetric spatial half-action sector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathWeight
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N) : ℝ :=
  Real.exp
    (-beta *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
        H N path)

/-- Boltzmann weight of the unfixed temporal crossing sector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathWeight
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) : ℝ :=
  Real.exp
    (-beta *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
        H N path U)

/-- Exact spatial/temporal factorization of the complete unfixed path kernel.
The next OS-coordinate theorem only has to identify the actual positive-half
plaquette sectors with these two explicit factors. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_spatialHalf_mul_temporal
    (H N : ℕ)
    (beta : ℝ)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath H N)
    (U : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalLinkField H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta path U =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathWeight
          H N beta path *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathWeight
          H N beta path U := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel_eq_boltzmann]
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathAction_eq_spatialHalf_add_temporal]
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathWeight
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathWeight
  rw [show
    -beta *
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
            H N path +
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
            H N path U) =
      (-beta *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedSpatialHalfPathAction
          H N path) +
      (-beta *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedTemporalPathAction
          H N path U) by ring]
  rw [Real.exp_add]

end

end MathlibAnalytic
end MGAP4D
