import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularSector
import Mathlib.Tactic

/-!
# Scalar-correlation criterion for the canonical factorial OS regular sector

The canonical same-root factorial OS construction defines the regular sector as those completed
OS vectors whose nonnegative-rational contraction orbit is strongly continuous at time zero.
For the next finite-Wilson-to-continuum step it is useful to replace this vector-valued condition
by a scalar one.

For every completed direct-limit vector `x` and every nonnegative rational time `t`, contractivity
gives the quantitative estimate

`‖T_t x - x‖² ≤ 2 (‖x‖² - ⟪x, T_t x⟫)`.

Consequently `x` is regular if and only if its self-correlation tends to its zero-time value:

`⟪x, T_t x⟫ → ⟪x,x⟫` as `t → 0` in `NNRat`.

This reduces the construction of concrete regular cylinder excitations to a real-valued correlation
limit that can later be attacked directly by finite Wilson estimates and weak convergence.  No
stochastic continuity, density claim, positive mass, spectral gap, or new physical assumption is
introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology

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

/-- The rational OS self-correlation is bounded above by its zero-time norm square. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslate_inner_le_norm_sq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNRat)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    inner ℝ x (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x) ≤ ‖x‖ ^ 2 := by
  calc
    inner ℝ x (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x) ≤
        ‖x‖ * ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_le t x)
        (norm_nonneg x)
    _ = ‖x‖ ^ 2 := by ring

/-- Quantitative conversion from scalar correlation defect to strong-orbit defect.

This estimate uses only the contraction property of the already-constructed rational OS
semigroup. -/
theorem fixedSlotHilbertDirectLimitNNRatTimeTranslate_sub_norm_sq_le_twice_correlation_defect
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNRat)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x - x‖ ^ 2 ≤
      2 *
        (‖x‖ ^ 2 -
          inner ℝ x (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x)) := by
  have hnorm := P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_norm_le t x
  have hprod :
      0 ≤
        (‖x‖ - ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x‖) *
          (‖x‖ + ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x‖) :=
    mul_nonneg
      (sub_nonneg.mpr hnorm)
      (add_nonneg (norm_nonneg x)
        (norm_nonneg (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x)))
  have hsqnorm :
      ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith
  rw [norm_sub_sq_real]
  rw [real_inner_comm
    (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x) x]
  nlinarith

/-- Strong zero-time regularity implies convergence of the scalar OS self-correlation. -/
theorem fixedSlotHilbertDirectLimitNNRatCorrelation_tendsto_zero_of_mem_regularSubspace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitCompletion)
    (hx : x ∈ P.fixedSlotHilbertDirectLimitRegularSubspace) :
    Tendsto
      (fun t : NNRat =>
        inner ℝ x (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x))
      (𝓝 0)
      (𝓝 (inner ℝ x x)) := by
  have hx' :=
    (P.mem_fixedSlotHilbertDirectLimitRegularSubspace_iff x).mp hx
  have hconst :
      Tendsto
        (fun _ : NNRat => x)
        (𝓝 0)
        (𝓝 x) :=
    tendsto_const_nhds
  exact Filter.Tendsto.inner (𝕜 := ℝ) hconst hx'

/-- Convergence of the scalar OS self-correlation to its zero-time value forces strong
zero-time regularity of the orbit. -/
theorem mem_fixedSlotHilbertDirectLimitRegularSubspace_of_NNRatCorrelation_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitCompletion)
    (hcorr :
      Tendsto
        (fun t : NNRat =>
          inner ℝ x (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x))
        (𝓝 0)
        (𝓝 (inner ℝ x x))) :
    x ∈ P.fixedSlotHilbertDirectLimitRegularSubspace := by
  rw [P.mem_fixedSlotHilbertDirectLimitRegularSubspace_iff]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hεsq : 0 < ε ^ 2 := by positivity
  have hδ : 0 < ε ^ 2 / 4 := by positivity
  have hevent := (Metric.tendsto_nhds.mp hcorr) (ε ^ 2 / 4) hδ
  filter_upwards [hevent] with t ht
  have habs :
      |inner ℝ x (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x) -
          inner ℝ x x| < ε ^ 2 / 4 := by
    simpa [Real.dist_eq] using ht
  have hgap :
      inner ℝ x x -
          inner ℝ x (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x) <
        ε ^ 2 / 4 := by
    have hleft := (abs_lt.mp habs).1
    nlinarith
  rw [real_inner_self_eq_norm_sq] at hgap
  have hdefect :=
    P.fixedSlotHilbertDirectLimitNNRatTimeTranslate_sub_norm_sq_le_twice_correlation_defect
      t x
  have hsquare :
      ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x - x‖ ^ 2 < ε ^ 2 := by
    nlinarith
  have habsnorm :
      |‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x - x‖| < ε :=
    abs_lt_of_sq_lt_sq hsquare (le_of_lt hε)
  have hnorm :
      ‖P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x - x‖ < ε := by
    simpa [abs_of_nonneg (norm_nonneg _)] using habsnorm
  simpa [dist_eq_norm] using hnorm

/-- Exact scalar characterization of the canonical same-root regular sector. -/
theorem mem_fixedSlotHilbertDirectLimitRegularSubspace_iff_NNRatCorrelation_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    x ∈ P.fixedSlotHilbertDirectLimitRegularSubspace ↔
      Tendsto
        (fun t : NNRat =>
          inner ℝ x (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x))
        (𝓝 0)
        (𝓝 (inner ℝ x x)) := by
  constructor
  · exact P.fixedSlotHilbertDirectLimitNNRatCorrelation_tendsto_zero_of_mem_regularSubspace x
  · exact P.mem_fixedSlotHilbertDirectLimitRegularSubspace_of_NNRatCorrelation_tendsto_zero x

/-- Norm-square form of the scalar regularity criterion. -/
theorem mem_fixedSlotHilbertDirectLimitRegularSubspace_iff_NNRatCorrelation_tendsto_norm_sq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    x ∈ P.fixedSlotHilbertDirectLimitRegularSubspace ↔
      Tendsto
        (fun t : NNRat =>
          inner ℝ x (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t x))
        (𝓝 0)
        (𝓝 (‖x‖ ^ 2)) := by
  simpa [real_inner_self_eq_norm_sq] using
    P.mem_fixedSlotHilbertDirectLimitRegularSubspace_iff_NNRatCorrelation_tendsto_zero x

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
