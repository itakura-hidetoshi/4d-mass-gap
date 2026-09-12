import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonActualExcitationOneStepSymmetry
import MGAP4D.MathlibAnalytic.PositiveOperatorRayleighLogRate
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

noncomputable section

open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace ContinuousLinearMap

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The square of a bounded symmetric real-Hilbert operator is positive.

This is obtained without assuming positivity of the original operator: symmetry
identifies the adjoint with the operator itself, so the square is the canonical
positive operator `T† T`. -/
theorem comp_self_isPositive_of_isSymmetric
    (T : H →L[ℝ] H) (hT : T.IsSymmetric) :
    (T ∘L T).IsPositive := by
  have hpos := ContinuousLinearMap.isPositive_adjoint_comp_self T
  simpa only [hT.clm_adjoint_eq] using hpos

/-- The C-star norm identity for a symmetric operator square. -/
theorem norm_comp_self_eq_sq_of_isSymmetric
    (T : H →L[ℝ] H) (hT : T.IsSymmetric) :
    ‖T ∘L T‖ = ‖T‖ * ‖T‖ := by
  simpa only [hT.clm_adjoint_eq] using
    ContinuousLinearMap.norm_adjoint_comp_self T

/-- Exact logarithmic-rate Rayleigh recovery from a merely symmetric one-step
operator, by passing to the positive two-step operator.

For positive spacing `a`, positive one-step norm, and `eps > 0`, there is a
unit vector whose two-step discrete energy over physical time `2a` is strictly
below the **same** one-step logarithmic rate plus `eps`:

`(1 - <T^2 x,x>) / (2a) < -log ||T|| / a + eps`.

The factor two cancels exactly because `||T^2|| = ||T||^2`; hence no rate
coefficient is lost and no one-step positivity hypothesis is introduced. -/
theorem exists_unit_twoStepDiscreteEnergy_lt_logRate_add_of_isSymmetric
    (T : H →L[ℝ] H) (hT : T.IsSymmetric)
    {a eps : ℝ} (ha : 0 < a) (hTnorm : 0 < ‖T‖) (heps : 0 < eps) :
    ∃ x : H, ‖x‖ = 1 ∧
      (1 - inner ℝ ((T ∘L T) x) x) / (2 * a) <
        -Real.log ‖T‖ / a + eps := by
  let T2 : H →L[ℝ] H := T ∘L T
  have hT2pos : T2.IsPositive := by
    dsimp [T2]
    exact comp_self_isPositive_of_isSymmetric T hT
  have hT2norm : ‖T2‖ = ‖T‖ * ‖T‖ := by
    dsimp [T2]
    exact norm_comp_self_eq_sq_of_isSymmetric T hT
  have hT2norm_pos : 0 < ‖T2‖ := by
    rw [hT2norm]
    positivity
  have h2a : 0 < 2 * a := by positivity
  rcases ContinuousLinearMap.IsPositive.exists_unit_discreteEnergy_lt_logRate_add
      (T := T2) hT2pos h2a hT2norm_pos heps with
    ⟨x, hxnorm, hxenergy⟩
  have hlog : Real.log ‖T2‖ = 2 * Real.log ‖T‖ := by
    rw [hT2norm, Real.log_mul hTnorm.ne' hTnorm.ne']
    ring
  refine ⟨x, hxnorm, ?_⟩
  calc
    (1 - inner ℝ ((T ∘L T) x) x) / (2 * a) =
        (1 - inner ℝ (T2 x) x) / (2 * a) := by rfl
    _ < -Real.log ‖T2‖ / (2 * a) + eps := hxenergy
    _ = -Real.log ‖T‖ / a + eps := by
      rw [hlog]
      field_simp [ha.ne']
      <;> ring

end ContinuousLinearMap

local instance actualTwoStepRateSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualTwoStepRateSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance actualTwoStepRateSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance actualTwoStepRateSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance actualTwoStepRateSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance actualTwoStepRateSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- The square of the actual completed finite Wilson excitation one-step
operator is positive.  This is theorem-generated from the actual OS symmetry
proved in the previous layer; no positivity field is stored. -/
theorem physicalExcitationTwoStepOperator_isPositive
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    ((A.physicalExcitationOneStepOperator n) ∘L
      (A.physicalExcitationOneStepOperator n)).IsPositive :=
  ContinuousLinearMap.comp_self_isPositive_of_isSymmetric
    (A.physicalExcitationOneStepOperator n)
    (A.physicalExcitationOneStepOperator_isSymmetric n)

/-- The actual positive two-step operator has norm equal to the square of the
exact centered transfer factor. -/
@[simp] theorem physicalExcitationTwoStepOperator_opNorm_eq_centeredTransferFactor_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ) :
    ‖(A.physicalExcitationOneStepOperator n) ∘L
        (A.physicalExcitationOneStepOperator n)‖ =
      A.centeredTransferFactor n * A.centeredTransferFactor n := by
  rw [ContinuousLinearMap.norm_comp_self_eq_sq_of_isSymmetric
      (A.physicalExcitationOneStepOperator n)
      (A.physicalExcitationOneStepOperator_isSymmetric n),
    A.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]

/-- At every finite scale with positive centered transfer factor, the **actual
completed finite Wilson excitation Hilbert space** contains a unit vector whose
positive two-step quadratic energy recovers the exact intrinsic one-step
logarithmic rate up to arbitrary positive additive error.

No finite-dimensional spectral theorem, eigenvector, norm attainment,
one-step positivity assumption, continuum mass, or target exact value enters. -/
theorem exists_physicalExcitationUnitTwoStepEnergy_lt_centeredLogRate_add
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (hfactor : 0 < A.centeredTransferFactor n)
    {eps : ℝ} (heps : 0 < eps) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert,
      ‖psi‖ = 1 ∧
      (1 - inner ℝ
          (((A.physicalExcitationOneStepOperator n) ∘L
            (A.physicalExcitationOneStepOperator n)) psi) psi) /
          (2 * S.latticeSpacing n) <
        -Real.log (A.centeredTransferFactor n) / S.latticeSpacing n + eps := by
  dsimp only
  let Tn := A.physicalExcitationOneStepOperator n
  have hTnorm : 0 < ‖Tn‖ := by
    dsimp [Tn]
    rw [A.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]
    exact hfactor
  rcases ContinuousLinearMap.exists_unit_twoStepDiscreteEnergy_lt_logRate_add_of_isSymmetric
      Tn (A.physicalExcitationOneStepOperator_isSymmetric n)
      (S.latticeSpacing_pos n) hTnorm heps with
    ⟨psi, hpsi, henergy⟩
  have hopnorm : ‖Tn‖ = A.centeredTransferFactor n := by
    dsimp [Tn]
    exact A.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor n
  refine ⟨psi, hpsi, ?_⟩
  change
    (1 - inner ℝ ((Tn ∘L Tn) psi) psi) / (2 * S.latticeSpacing n) <
      -Real.log (A.centeredTransferFactor n) / S.latticeSpacing n + eps
  rw [← hopnorm]
  exact henergy

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

end MathlibAnalytic
end MGAP4D

end