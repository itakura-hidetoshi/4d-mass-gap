import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSTimeTranslateNullPreservation
import Mathlib.Analysis.Normed.Group.SeparationQuotient
import Mathlib.Tactic

/-!
# Factorial OS time translation on separated fixed-slot sectors

The preceding layer proves that nonnegative rational time translation preserves the OS null
submodule on the canonical primary-scalar factorial root.  This file uses precisely that result to
descend the algebraic time-translation map from the wrapped seminormed carrier to its
`SeparationQuotient`.

Crucially, no continuity or norm bound for time translation is assumed here.  In particular we do
not use `SeparationQuotient.map`, whose uniform-space API would require continuity information not
yet established.  Instead we prove directly that translation respects the inseparability relation:
if `x-y` has OS seminorm zero, then its translated difference has OS seminorm zero by the null-space
theorem.  `Quotient.map'` then gives the desired algebraic quotient map, which is packaged as a
linear map using the existing linearity of fixed-slot observable translation.

No contraction, continuous extension to Hilbert completion, semigroup, Hamiltonian, spectral
statement, or mass-gap transfer is introduced here.
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

/-- Fixed-slot carrier time translation preserves the inseparability relation.  The proof is purely
seminorm algebra: inseparability is `‖F-G‖ = 0`, and #1840 sends the null difference to a null
translated difference. -/
theorem fixedSlotCarrierTimeTranslate_inseparable
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    {F G : P.FixedSlotCarrier}
    (hFG : Inseparable F G) :
    Inseparable
      (P.fixedSlotCarrierTimeTranslate t ht F)
      (P.fixedSlotCarrierTimeTranslate t ht G) := by
  have hdiff : ‖F - G‖ = 0 := by
    simpa [dist_eq_norm] using (Metric.inseparable_iff.mp hFG)
  have hnull : F - G ∈ P.nullSubmodule :=
    (P.mem_nullSubmodule (F - G)).2 hdiff
  have htranslatedNull :=
    P.fixedSlotCarrierTimeTranslate_mem_nullSubmodule t ht (F - G) hnull
  have htranslatedNorm :
      ‖P.fixedSlotCarrierTimeTranslate t ht (F - G)‖ = 0 :=
    ((P.fixedSlotTimeTranslateData t ht).mem_nullSubmodule
      (P.fixedSlotCarrierTimeTranslate t ht (F - G))).1 htranslatedNull
  apply Metric.inseparable_iff.mpr
  rw [dist_eq_norm, ← map_sub]
  exact htranslatedNorm

/-- Algebraic rational-time translation on the separated fixed-slot OS sector.

This is intentionally only a `LinearMap`: no boundedness or continuity is claimed before an OS
contraction estimate is proved. -/
noncomputable def fixedSlotSeparatedTimeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    P.Separated →ₗ[ℝ] (P.fixedSlotTimeTranslateData t ht).Separated where
  toFun :=
    Quotient.map'
      (P.fixedSlotCarrierTimeTranslate t ht)
      (fun _ _ h => P.fixedSlotCarrierTimeTranslate_inseparable t ht h)
  map_add' := by
    intro x y
    obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨y, rfl⟩ := SeparationQuotient.surjective_mk y
    change
      SeparationQuotient.mk
          (P.fixedSlotCarrierTimeTranslate t ht (x + y)) =
        SeparationQuotient.mk (P.fixedSlotCarrierTimeTranslate t ht x) +
          SeparationQuotient.mk (P.fixedSlotCarrierTimeTranslate t ht y)
    rw [map_add, SeparationQuotient.mk_add]
  map_smul' := by
    intro r x
    obtain ⟨x, rfl⟩ := SeparationQuotient.surjective_mk x
    change
      SeparationQuotient.mk
          (P.fixedSlotCarrierTimeTranslate t ht (r • x)) =
        r • SeparationQuotient.mk (P.fixedSlotCarrierTimeTranslate t ht x)
    rw [map_smul, SeparationQuotient.mk_smul]

/-- The separated translation is exactly the quotient class of the translated wrapped carrier. -/
@[simp]
theorem fixedSlotSeparatedTimeTranslate_osClass
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotSeparatedTimeTranslate t ht (P.osClass F) =
      (P.fixedSlotTimeTranslateData t ht).osClass
        (P.fixedSlotCarrierTimeTranslate t ht F) :=
  rfl

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
