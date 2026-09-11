import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitLiteralCylinderVacuumMeanBridge
import Mathlib.Tactic

/-!
# Mean-subtracted finite Wilson reflection forms and centered same-root OS correlations

The preceding same-root packages identify, for every literal fixed-slot bounded-continuous cylinder,

* its completed direct-limit OS correlation with the weak limit of the actual finite Wilson
  reflection forms; and
* its Hilbert vacuum coefficient with its continuum probabilistic mean, itself the weak limit of
  the actual finite Wilson means.

This file combines those two exact bridges.  A literal cylinder state is centered in the completed
same-root Hilbert carrier by subtracting its continuum mean times the canonical vacuum.  The
resulting vector is exactly vacuum-orthogonal.  Because rational OS time translation is symmetric
and fixes the same canonical vacuum, its double-time centered correlation is the uncentered
correlation minus the square of that continuum mean.

On the finite side we deliberately use the conservative name *mean-subtracted reflection form*:

`Q_n(τ_h F) - (E_n F)^2`.

No finite temporal stationarity statement is assumed here, so this expression is not relabelled as
an abstract covariance.  Weak convergence of both terms proves that these actual finite Wilson
mean-subtracted reflection forms converge exactly to the centered same-root Hilbert correlation.

This creates the precise insertion point for a future model-derived, scale-uniform quantitative
bound on centered literal Wilson cylinders.  No non-collapse, variance floor, decay constant,
positive mass, spectral gap, or old-carrier identification is introduced.
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

/-- The rational completed direct-limit OS contraction fixes the canonical same-root vacuum at
all nonnegative rational times. -/
@[simp]
theorem fixedSlotHilbertDirectLimitTimeTranslateCLM_vacuum
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht
        P.fixedSlotHilbertDirectLimitVacuum =
      P.fixedSlotHilbertDirectLimitVacuum := by
  let q : NNRat := ⟨t, ht⟩
  have hq := P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM_vacuum q
  simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM, q] using hq

/-- A literal fixed-slot cylinder centered by the exact continuum mean that #1907 identifies with
its same-root Hilbert vacuum coefficient. -/
noncomputable def fixedSlotHilbertDirectLimitCenteredCarrierState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.fixedSlotHilbertDirectLimitCompletion :=
  P.fixedSlotHilbertDirectLimitCarrierState J F -
    (P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F •
      P.fixedSlotHilbertDirectLimitVacuum

/-- Probabilistic centering of a literal cylinder is exactly Hilbert vacuum centering on the
same-root completed carrier. -/
@[simp]
theorem fixedSlotHilbertDirectLimitVacuum_inner_centeredCarrierState
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F) = 0 := by
  unfold fixedSlotHilbertDirectLimitCenteredCarrierState
  rw [inner_sub_right, inner_smul_right]
  rw [P.fixedSlotHilbertDirectLimitVacuum_inner_carrierState_eq_continuumMean J F]
  rw [real_inner_self_eq_norm_sq, P.fixedSlotHilbertDirectLimitVacuum_norm]
  simp

/-- The canonical vacuum coefficient of a rationally translated literal cylinder remains its
original continuum mean. -/
theorem fixedSlotHilbertDirectLimitVacuum_inner_timeTranslate_carrierState_eq_continuumMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (t : ℚ) (ht : 0 ≤ t)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht
          (P.fixedSlotHilbertDirectLimitCarrierState J F)) =
      (P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F := by
  have hsym :=
    P.fixedSlotHilbertDirectLimitTimeTranslate_inner_symmetric
      t ht P.fixedSlotHilbertDirectLimitVacuum
      (P.fixedSlotHilbertDirectLimitCarrierState J F)
  calc
    inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht
          (P.fixedSlotHilbertDirectLimitCarrierState J F)) =
      inner ℝ
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht
          P.fixedSlotHilbertDirectLimitVacuum)
        (P.fixedSlotHilbertDirectLimitCarrierState J F) := by
          simpa using hsym.symm
    _ = inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        (P.fixedSlotHilbertDirectLimitCarrierState J F) := by
          rw [P.fixedSlotHilbertDirectLimitTimeTranslateCLM_vacuum]
    _ = (P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F :=
      P.fixedSlotHilbertDirectLimitVacuum_inner_carrierState_eq_continuumMean J F

/-- Exact centering identity for the double-time OS correlation of a literal cylinder state.
The only subtracted term is the square of the continuum mean / Hilbert vacuum coefficient. -/
theorem fixedSlotHilbertDirectLimitCenteredCarrierState_correlation_double_eq_sub_mean_sq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    inner ℝ
        (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
          (h + h) (add_nonneg hh hh)
          (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)) =
      inner ℝ
          (P.fixedSlotHilbertDirectLimitCarrierState J F)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (h + h) (add_nonneg hh hh)
            (P.fixedSlotHilbertDirectLimitCarrierState J F)) -
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F) ^ 2 := by
  let x := P.fixedSlotHilbertDirectLimitCarrierState J F
  let μ := (P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F
  have hVacuumX :
      inner ℝ P.fixedSlotHilbertDirectLimitVacuum x = μ := by
    simpa [x, μ] using
      P.fixedSlotHilbertDirectLimitVacuum_inner_carrierState_eq_continuumMean J F
  have hXVacuum :
      inner ℝ x P.fixedSlotHilbertDirectLimitVacuum = μ := by
    calc
      inner ℝ x P.fixedSlotHilbertDirectLimitVacuum =
          inner ℝ P.fixedSlotHilbertDirectLimitVacuum x := real_inner_comm _ _
      _ = μ := hVacuumX
  have hVacuumTx :
      inner ℝ P.fixedSlotHilbertDirectLimitVacuum
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (h + h) (add_nonneg hh hh) x) = μ := by
    simpa [x, μ] using
      P.fixedSlotHilbertDirectLimitVacuum_inner_timeTranslate_carrierState_eq_continuumMean
        J (h + h) (add_nonneg hh hh) F
  have hVacuumSelf :
      inner ℝ P.fixedSlotHilbertDirectLimitVacuum
        P.fixedSlotHilbertDirectLimitVacuum = 1 := by
    rw [real_inner_self_eq_norm_sq, P.fixedSlotHilbertDirectLimitVacuum_norm]
    norm_num
  change
    inner ℝ
        (x - μ • P.fixedSlotHilbertDirectLimitVacuum)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
          (h + h) (add_nonneg hh hh)
          (x - μ • P.fixedSlotHilbertDirectLimitVacuum)) =
      inner ℝ x
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (h + h) (add_nonneg hh hh) x) - μ ^ 2
  rw [map_sub, map_smul, P.fixedSlotHilbertDirectLimitTimeTranslateCLM_vacuum]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  rw [hVacuumTx, hXVacuum, hVacuumSelf]
  ring

/-- The centered double-time Hilbert correlation is the continuum translated reflection form
minus the squared continuum mean. -/
theorem fixedSlotHilbertDirectLimitCenteredCarrierState_correlation_double_eq_meanSubtractedReflectionForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    inner ℝ
        (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)
        (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
          (h + h) (add_nonneg hh hh)
          (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)) =
      ((P.fixedSlotDataOfIndex
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)).fixedSlotCarrierPositiveCylinder
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F)).realReflectionForm
          (L.continuumMeasure : Measure (ℚ → ℝ)) -
        ((P.fixedSlotDataOfIndex J).fixedSlotCarrierContinuumMean F) ^ 2 := by
  rw [P.fixedSlotHilbertDirectLimitCenteredCarrierState_correlation_double_eq_sub_mean_sq J h hh F]
  rw [P.fixedSlotHilbertDirectLimitCarrierState_correlation_double_eq_realReflectionForm J h hh F]

/-- Actual finite Wilson mean of a literal fixed-slot cylinder along the selected Prokhorov
subsequence. -/
noncomputable def fixedSlotCarrierFiniteMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F : P.FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
      (H (L.subsequence n)) N hN
      (beta (L.subsequence n)) (hbeta (L.subsequence n))
      (fun k =>
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence k))
      n)
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
      P.slots F.observable)

/-- The finite mean wrapper converges to the already-canonical continuum mean. -/
theorem fixedSlotCarrierFiniteMean_tendsto_continuumMean
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (F : P.FixedSlotCarrier) :
    Tendsto (fun n => P.fixedSlotCarrierFiniteMean F n) atTop
      (nhds (P.fixedSlotCarrierContinuumMean F)) := by
  have hweak :=
    L.weakConvergence_reindexed H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
  have hint :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable
        P.slots F.observable)
  simpa [fixedSlotCarrierFiniteMean, fixedSlotCarrierContinuumMean,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPathExpectation_apply] using hint

/-- The actual finite Wilson translated reflection form with the square of the actual finite
Wilson mean subtracted.  No temporal stationarity assumption is built into this definition. -/
noncomputable def fixedSlotCarrierFiniteMeanSubtractedReflectionForm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (n : ℕ) : ℝ :=
  ((P.fixedSlotDataOfIndex
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate h hh J)).fixedSlotCarrierPositiveCylinder
    ((P.fixedSlotDataOfIndex J).fixedSlotCarrierTimeTranslate h hh F)).realReflectionForm
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProbabilityMeasure
        (H (L.subsequence n)) N hN
        (beta (L.subsequence n)) (hbeta (L.subsequence n))
        (fun k =>
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (L.subsequence k))
        n : Measure (ℚ → ℝ)) -
    ((P.fixedSlotDataOfIndex J).fixedSlotCarrierFiniteMean F n) ^ 2

/-- Along the actual selected Wilson subsequence, the finite mean-subtracted reflection forms
converge exactly to the centered same-root double-time Hilbert correlation. -/
theorem fixedSlotCarrierFiniteMeanSubtractedReflectionForm_tendsto_centeredCorrelation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    Tendsto
      (fun n => P.fixedSlotCarrierFiniteMeanSubtractedReflectionForm J h hh F n)
      atTop
      (nhds
        (inner ℝ
          (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (h + h) (add_nonneg hh hh)
            (P.fixedSlotHilbertDirectLimitCenteredCarrierState J F)))) := by
  have hQ :=
    P.fixedSlotHilbertDirectLimitCarrierState_translatedReflectionForm_tendsto_correlation_double
      J h hh F
  have hM :=
    (P.fixedSlotDataOfIndex J).fixedSlotCarrierFiniteMean_tendsto_continuumMean F
  have hsub := hQ.sub (hM.mul hM)
  rw [P.fixedSlotHilbertDirectLimitCenteredCarrierState_correlation_double_eq_sub_mean_sq J h hh F]
  simpa [fixedSlotCarrierFiniteMeanSubtractedReflectionForm, pow_two] using hsub

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
