import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonalSmoothedCarrierCore
import Mathlib.Tactic

/-!
# Literal cylinder means and the same-root vacuum coefficient

The preceding same-root packages now reduce the exact excitation carrier to a dense core of
positive-time translates of literal bounded-continuous fixed-slot cylinders, and identify their
OS self-correlations with weak limits of actual finite Wilson reflection forms.

To use a model-derived *centered* Wilson estimate, the probabilistic centering coefficient must be
identified with the Hilbert-space vacuum coefficient on this same carrier.  This file makes that
identification exact.

For every finite nonnegative slot set `J`, the constant-one cylinder in the `J` sector represents
exactly the same algebraic-direct-limit vector as the canonical empty-slot vacuum.  Therefore the
inner product of the vacuum with a literal cylinder state is simply the continuum expectation of
that cylinder.  Weak convergence of the actual finite Wilson scalar path laws shows that the finite
expectations converge to this same coefficient.  Finally, positive rational-time smoothing leaves
the coefficient unchanged because the same-root OS semigroup is symmetric and fixes the vacuum.

Thus probabilistic centering of literal cylinders and Hilbert centering against `Ω` use the same
continuum scalar.  No non-collapse estimate, variance floor, decay constant, positive mass, or
old-carrier identification is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory UniformSpace
open scoped InnerProductSpace

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The constant-one wrapped cylinder in an arbitrary fixed-slot OS sector. -/
noncomputable def fixedSlotCarrierOne
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.FixedSlotCarrier :=
  ⟨1⟩

@[simp]
theorem fixedSlotCarrierOne_observable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotCarrierOne.observable = 1 :=
  rfl

/-- The empty vacuum slot index is below every finite nonnegative slot index. -/
theorem fixedSlotHilbertDirectLimitVacuumIndex_le
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    fixedSlotHilbertDirectLimitVacuumIndex ≤ J := by
  change (∅ : Finset ℚ) ⊆ J.1
  exact Finset.empty_subset J.1

/-- Including the empty-slot vacuum cylinder into any fixed-slot sector gives the literal
constant-one cylinder there. -/
theorem fixedSlotHilbertDirectLimitVacuumCarrier_inclusion_eq_one
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    (P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).fixedSlotCarrierInclusion
        (P.fixedSlotDataOfIndex J)
        (fixedSlotHilbertDirectLimitVacuumIndex_le J)
        P.fixedSlotHilbertDirectLimitVacuumCarrier =
      (P.fixedSlotDataOfIndex J).fixedSlotCarrierOne := by
  apply FixedSlotCarrier.observable_injective (P.fixedSlotDataOfIndex J)
  ext v
  rfl

/-- The constant-one cylinder in any finite slot sector represents exactly the canonical completed
direct-limit vacuum. -/
@[simp]
theorem fixedSlotHilbertDirectLimitCarrierState_one_eq_vacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    P.fixedSlotHilbertDirectLimitCarrierState J
        (P.fixedSlotDataOfIndex J).fixedSlotCarrierOne =
      P.fixedSlotHilbertDirectLimitVacuum := by
  unfold fixedSlotHilbertDirectLimitCarrierState fixedSlotHilbertDirectLimitVacuum
  apply congrArg
    (fun z : P.fixedSlotHilbertAlgebraicDirectLimit =>
      (z : P.fixedSlotHilbertDirectLimitCompletion))
  rw [P.fixedSlotHilbertAlgebraicLinearIsometry_apply]
  unfold fixedSlotHilbertDirectLimitVacuumAlgebraic
  let h0J := fixedSlotHilbertDirectLimitVacuumIndex_le J
  calc
    P.fixedSlotHilbertAlgebraicOf J
        ((P.fixedSlotDataOfIndex J).hilbertState
          (P.fixedSlotDataOfIndex J).fixedSlotCarrierOne) =
      P.fixedSlotHilbertAlgebraicOf J
        (P.fixedSlotIndexedHilbertMap
          fixedSlotHilbertDirectLimitVacuumIndex J h0J
          ((P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).hilbertState
            P.fixedSlotHilbertDirectLimitVacuumCarrier)) := by
      congr 1
      change
        (P.fixedSlotDataOfIndex J).hilbertState
            (P.fixedSlotDataOfIndex J).fixedSlotCarrierOne =
          (P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).fixedSlotHilbertInclusion
            (P.fixedSlotDataOfIndex J) h0J
            ((P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).hilbertState
              P.fixedSlotHilbertDirectLimitVacuumCarrier)
      rw [(P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).fixedSlotHilbertInclusion_hilbertState]
      rw [P.fixedSlotHilbertDirectLimitVacuumCarrier_inclusion_eq_one J]
    _ = P.fixedSlotHilbertAlgebraicOf fixedSlotHilbertDirectLimitVacuumIndex
        ((P.fixedSlotDataOfIndex fixedSlotHilbertDirectLimitVacuumIndex).hilbertState
          P.fixedSlotHilbertDirectLimitVacuumCarrier) :=
      P.fixedSlotHilbertAlgebraicOf_map
        fixedSlotHilbertDirectLimitVacuumIndex J h0J _

/-- Continuum probabilistic mean of one literal fixed-slot cylinder. -/
noncomputable def fixedSlotCarrierContinuumMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F : P.FixedSlotCarrier) : ℝ :=
  periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
    L.continuumMeasure
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
      P.slots F.observable)

/-- Pairing the constant-one cylinder with a literal cylinder is exactly its continuum mean. -/
theorem fixedSlotCarrierOne_inner_eq_continuumMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F : P.FixedSlotCarrier) :
    inner ℝ P.fixedSlotCarrierOne F =
      P.fixedSlotCarrierContinuumMean F := by
  rw [P.inner_eq_fixedSlotOSBilinForm]
  rw [L.fixedSlotOSBilinForm_apply]
  simp [fixedSlotCarrierOne, fixedSlotCarrierContinuumMean,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarReflectionPullback_apply,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_apply]

/-- The completed same-root vacuum coefficient of a literal cylinder state is exactly its
continuum probabilistic mean. -/
theorem fixedSlotHilbertDirectLimitVacuum_inner_carrierState_eq_continuumMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitCarrierState J F) =
      (P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F := by
  rw [← P.fixedSlotHilbertDirectLimitCarrierState_one_eq_vacuum J]
  unfold fixedSlotHilbertDirectLimitCarrierState
  rw [Completion.inner_coe]
  rw [P.fixedSlotHilbertAlgebraicLinearIsometry_inner]
  rw [(P.fixedSlotDataOfIndex J).inner_hilbertState_hilbertState]
  exact (P.fixedSlotDataOfIndex J).fixedSlotCarrierOne_inner_eq_continuumMean F

/-- Along the selected Prokhorov subsequence, actual finite Wilson expectations of a literal
cylinder converge to the same continuum scalar that appears as its Hilbert vacuum coefficient. -/
theorem fixedSlotCarrier_finiteExpectation_tendsto_continuumMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    Tendsto
      (fun n =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
            (H (L.subsequence n)) N hN
            (beta (L.subsequence n)) (hbeta (L.subsequence n))
            (fun k =>
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence k))
            n)
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
            J.1 F.observable))
      atTop
      (nhds ((P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F)) := by
  have hweak :=
    L.weakConvergence_reindexed H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
  have hint :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        J.1 F.observable)
  simpa [fixedSlotCarrierContinuumMean,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply] using hint

/-- A positive-time translate of a literal cylinder, canonically regarded as a regular vector. -/
noncomputable def fixedSlotHilbertDirectLimitCarrierPositiveTimeRegular
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat) (hs : 0 < s)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitRegularSubspace :=
  ⟨P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
      (P.fixedSlotHilbertDirectLimitCarrierState J F),
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_mem_regularSubspace_of_pos
      s hs (P.fixedSlotHilbertDirectLimitCarrierState J F)⟩

/-- Positive-time smoothing preserves the literal cylinder's vacuum coefficient, so the regular
Hilbert coefficient is still exactly the same continuum probabilistic mean. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumCoefficient_carrierPositiveTimeRegular_eq_continuumMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat) (hs : 0 < s)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitRegularVacuumCoefficient
        (P.fixedSlotHilbertDirectLimitCarrierPositiveTimeRegular s hs J F) =
      (P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumCoefficient
  change
    inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          (P.fixedSlotHilbertDirectLimitCarrierState J F)) = _
  have hsym :=
    P.fixedSlotHilbertDirectLimitTimeTranslate_inner_symmetric
      (s : ℚ) s.2 P.fixedSlotHilbertDirectLimitVacuum
      (P.fixedSlotHilbertDirectLimitCarrierState J F)
  calc
    inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          (P.fixedSlotHilbertDirectLimitCarrierState J F)) =
      inner ℝ
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          P.fixedSlotHilbertDirectLimitVacuum)
        (P.fixedSlotHilbertDirectLimitCarrierState J F) := by
          simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM] using hsym.symm
    _ = inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitCarrierState J F) := by
          rw [P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_vacuum]
    _ = (P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F :=
      P.fixedSlotHilbertDirectLimitVacuum_inner_carrierState_eq_continuumMean J F

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
