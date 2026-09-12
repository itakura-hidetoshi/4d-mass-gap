import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSCarrierContraction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# Factorial OS contraction on separated fixed-slot sectors

The preceding layer proves the genuine same-root contraction on the wrapped OS seminormed carrier,
while #1842 already provides the algebraic time-translation map on the separated quotient.  This
file combines those two canonical results.

Using `SeparationQuotient.norm_mk`, the carrier contraction descends exactly to

`‖T_t x‖ ≤ ‖x‖`

for every separated fixed-slot vector.  The existing algebraic quotient map can therefore be
packaged by Mathlib `LinearMap.mkContinuous` with bound `1`, yielding a continuous linear
contraction between the separated sectors for `J` and `J+t`.

No Hilbert-completion extension, direct-limit operator, semigroup, Hamiltonian, spectral statement,
or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

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

/-- The algebraic separated time-translation map from #1842 is a contraction after #1845. -/
theorem fixedSlotSeparatedTimeTranslate_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x : P.Separated) :
    ‖P.fixedSlotSeparatedTimeTranslate t ht x‖ ≤ ‖x‖ := by
  obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
  change
    ‖P.fixedSlotSeparatedTimeTranslate t ht (P.osClass F)‖ ≤ ‖P.osClass F‖
  rw [P.fixedSlotSeparatedTimeTranslate_osClass]
  change
    ‖SeparationQuotient.mk (P.fixedSlotCarrierTimeTranslate t ht F)‖ ≤
      ‖SeparationQuotient.mk F‖
  simpa only [SeparationQuotient.norm_mk] using
    P.fixedSlotCarrierTimeTranslate_norm_le t ht F

/-- Continuous linear rational-time translation on the separated fixed-slot OS sector, with the
sharp contraction bound built into its construction. -/
noncomputable def fixedSlotSeparatedTimeTranslateCLM
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    P.Separated →L[ℝ] (P.fixedSlotTimeTranslateData t ht).Separated :=
  (P.fixedSlotSeparatedTimeTranslate t ht).mkContinuous 1 fun x => by
    simpa using P.fixedSlotSeparatedTimeTranslate_norm_le t ht x

@[simp]
theorem fixedSlotSeparatedTimeTranslateCLM_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x : P.Separated) :
    P.fixedSlotSeparatedTimeTranslateCLM t ht x =
      P.fixedSlotSeparatedTimeTranslate t ht x :=
  rfl

/-- The separated continuous-linear time translation has operator norm at most one. -/
theorem fixedSlotSeparatedTimeTranslateCLM_norm_le_one
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    ‖P.fixedSlotSeparatedTimeTranslateCLM t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using P.fixedSlotSeparatedTimeTranslate_norm_le t ht x

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
