import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitPositiveTimeRegularization
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Dense positive-time smoothed algebraic core of the same-root regular OS sector

The completed factorial OS direct-limit carrier contains a canonical dense algebraic direct-limit
subspace.  The preceding layer proves that every strictly positive rational-time translate of an
arbitrary completed vector belongs to the zero-time regular sector.

This file combines those two facts without adding any continuity hypothesis on the whole completed
carrier.

For a fixed positive rational time `s`, density of the canonical completion embedding and
contractivity imply that every vector `T_s x` can be approximated arbitrarily well by vectors
`T_s z` with `z` algebraic.  We collect all such positive-time smoothed algebraic vectors in one
set and prove that every one of them is regular.

For a regular vector `x`, the explicit positive sequence

`1 / (n + 1) : NNRat`

tends to zero.  Hence regularity gives `T_(1/(n+1)) x → x`.  Each term belongs to the closure of
the smoothed algebraic set by the fixed-time approximation theorem.  Closedness of the closure
therefore yields that every regular vector belongs to that same closure.

Thus the same-root regular sector has a dense core made from the actual algebraic fixed-slot
carrier followed by strictly positive OS time smoothing.  No stochastic-continuity assumption,
spectral functional calculus, mass-gap input, or old-carrier identification is used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

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

/-- Positive-time smoothed vectors coming from the canonical algebraic fixed-slot direct limit. -/
def fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Set P.fixedSlotHilbertDirectLimitCompletion :=
  {y | ∃ s : NNRat, 0 < s ∧
    ∃ z : P.fixedSlotHilbertAlgebraicDirectLimit,
      y = P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
        (z : P.fixedSlotHilbertDirectLimitCompletion)}

/-- Every positive-time smoothed algebraic vector lies in the canonical regular sector. -/
theorem fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet_subset_regularSubspace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet ⊆
      P.fixedSlotHilbertDirectLimitRegularSubspace := by
  rintro y ⟨s, hs, z, rfl⟩
  exact
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_mem_regularSubspace_of_pos
      s hs (z : P.fixedSlotHilbertDirectLimitCompletion)

/-- At a fixed strictly positive rational time, algebraic input vectors approximate the translate
of every completed input vector. -/
theorem fixedSlotHilbertDirectLimit_positiveTime_algebraic_approximation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat) (hs : 0 < s)
    (x : P.fixedSlotHilbertDirectLimitCompletion)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ z : P.fixedSlotHilbertAlgebraicDirectLimit,
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          (z : P.fixedSlotHilbertDirectLimitCompletion) ∈
        P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet ∧
      dist
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x)
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (z : P.fixedSlotHilbertDirectLimitCompletion)) < ε := by
  obtain ⟨z, hz⟩ :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt x hε
  refine ⟨z, ?_, ?_⟩
  · exact ⟨s, hs, z, rfl⟩
  · calc
      dist
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x)
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
            (z : P.fixedSlotHilbertDirectLimitCompletion)) =
        ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
          (x - (z : P.fixedSlotHilbertDirectLimitCompletion))‖ := by
            rw [dist_eq_norm, map_sub]
      _ ≤ ‖x - (z : P.fixedSlotHilbertDirectLimitCompletion)‖ :=
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_le s _
      _ = dist x (z : P.fixedSlotHilbertDirectLimitCompletion) := by
        rw [dist_eq_norm]
      _ < ε := hz

/-- Every strictly positive rational-time translate belongs to the closure of the positive-time
smoothed algebraic set. -/
theorem fixedSlotHilbertDirectLimit_positiveTime_mem_closure_smoothedAlgebraic
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (s : NNRat) (hs : 0 < s)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s x ∈
      closure P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet := by
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨z, hzmem, hzdist⟩ :=
    P.fixedSlotHilbertDirectLimit_positiveTime_algebraic_approximation
      s hs x ε hε
  exact
    ⟨P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM s
        (z : P.fixedSlotHilbertDirectLimitCompletion), hzmem, hzdist⟩

/-- The explicit strictly positive rational time mesh `1/(n+1)` tends to zero. -/
theorem fixedSlotHilbertDirectLimit_positiveReciprocalTime_tendsto_zero :
    Tendsto (fun n : ℕ => (1 / ((n : NNRat) + 1) : NNRat)) atTop (𝓝 0) := by
  simpa using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := NNRat))

/-- A regular vector is the limit of its strictly positive rational-time regularizations along the
explicit reciprocal mesh. -/
theorem fixedSlotHilbertDirectLimitRegularSubspace_tendsto_positiveReciprocalTime
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
          (1 / ((n : NNRat) + 1))
          (x : P.fixedSlotHilbertDirectLimitCompletion))
      atTop
      (𝓝 (x : P.fixedSlotHilbertDirectLimitCompletion)) := by
  exact x.2.comp fixedSlotHilbertDirectLimit_positiveReciprocalTime_tendsto_zero

/-- Every vector in the canonical regular sector lies in the closure of the positive-time smoothed
algebraic set.  This is the same-root dense regular-core statement. -/
theorem fixedSlotHilbertDirectLimitRegularSubspace_subset_closure_smoothedAlgebraic
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    (P.fixedSlotHilbertDirectLimitRegularSubspace :
      Set P.fixedSlotHilbertDirectLimitCompletion) ⊆
      closure P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet := by
  intro x hx
  let xr : P.fixedSlotHilbertDirectLimitRegularSubspace := ⟨x, hx⟩
  have hlim :
      Tendsto
        (fun n : ℕ =>
          P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
            (1 / ((n : NNRat) + 1)) x)
        atTop (𝓝 x) := by
    simpa [xr] using
      P.fixedSlotHilbertDirectLimitRegularSubspace_tendsto_positiveReciprocalTime xr
  have hmem : ∀ n : ℕ,
      P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM
          (1 / ((n : NNRat) + 1)) x ∈
        closure P.fixedSlotHilbertDirectLimitPositiveTimeSmoothedAlgebraicSet := by
    intro n
    apply P.fixedSlotHilbertDirectLimit_positiveTime_mem_closure_smoothedAlgebraic
    positivity
  exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall hmem)

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
