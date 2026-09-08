import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumFullSpatialOneLinkDoobBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumUniformDoobFactorSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The real Harnack endpoint ratio is exactly `exp (-16 * beta)`.

The vacuum amplitude cancels completely.  This is the quantitative reason the
continuous-vacuum one-link comparison is independent of the lattice volume and
of the base configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_harnackEndpointRatio_eq_exp_neg_sixteen
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    let omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
    let R : ℝ := Real.exp (8 * beta)
    (omega A / R) / (R * omega A) = Real.exp (-16 * beta) := by
  dsimp only
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let R : ℝ := Real.exp (8 * beta)
  have homegaPos : 0 < omega A := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta A
  have hRPos : 0 < R := by
    simpa [R] using Real.exp_pos (8 * beta)
  have homegaNe : omega A ≠ 0 := ne_of_gt homegaPos
  have hRNe : R ≠ 0 := ne_of_gt hRPos
  calc
    (omega A / R) / (R * omega A) = 1 / (R * R) := by
      field_simp [hRNe, homegaNe]
    _ = R⁻¹ * R⁻¹ := by
      field_simp [hRNe]
    _ = Real.exp (-(8 * beta)) * Real.exp (-(8 * beta)) := by
      rw [Real.exp_neg, Real.exp_neg]
      rfl
    _ = Real.exp (-(8 * beta) + -(8 * beta)) := by
      rw [← Real.exp_add]
    _ = Real.exp (-16 * beta) := by ring_nf

/-- ENNReal form of the same cancellation.  This is the exact coefficient that
appears in the normalized Doob-variance comparison. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_harnackENNRealRatio_eq_exp_neg_sixteen
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    let omega :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta
    let R : ℝ := Real.exp (8 * beta)
    ENNReal.ofReal (omega A / R) / ENNReal.ofReal (R * omega A) =
      ENNReal.ofReal (Real.exp (-16 * beta)) := by
  dsimp only
  let omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let R : ℝ := Real.exp (8 * beta)
  have homegaPos : 0 < omega A := by
    simpa [omega] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
        H N hN beta hbeta A
  have hRPos : 0 < R := by
    simpa [R] using Real.exp_pos (8 * beta)
  have hnumNonneg : 0 ≤ omega A / R := le_of_lt (div_pos homegaPos hRPos)
  have hdenPos : 0 < R * omega A := mul_pos hRPos homegaPos
  rw [← ENNReal.ofReal_div_of_pos hdenPos]
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_harnackEndpointRatio_eq_exp_neg_sixteen
    H N hN beta hbeta A]

/-- Literal full four-dimensional Wilson one-link variance comparison with the
vacuum amplitude removed from the statement.  The loss is the explicit local
factor `exp (-16 * beta)`, independent of `H` and of the configuration. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoob_evariance_exp_neg_sixteen_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      ((periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
          A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target))) :
    ENNReal.ofReal (Real.exp (-16 * beta)) *
        evariance X
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).singleLinkConditionalMeasure
              A (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)) ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoobMeasure
          H N hN beta hbeta A target) := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumFullSpatialLinkDoob_evariance_lower_bound
      H N hN beta hbeta A target X hX
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_harnackENNRealRatio_eq_exp_neg_sixteen
    H N hN beta hbeta (periodicHypercubicEvenSpatialSliceRestriction A)] at h
  exact h

end

end MathlibAnalytic
end MGAP4D
