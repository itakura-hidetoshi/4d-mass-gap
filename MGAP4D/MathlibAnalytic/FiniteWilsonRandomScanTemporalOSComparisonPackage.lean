import MGAP4D.MathlibAnalytic.RealHilbertDiscreteSemigroupComparisonDefect
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertShiftSemigroup
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertPositiveSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The already constructed random-scan temporal OS semigroup is exactly the
natural powers of its completed one-step positive-time path shift. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_eq_pow
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n =
      L.randomScanTwoSidedIntegerPathOSHilbertShift ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_succ,
        ih, pow_succ']
      rfl

/-- Defect between the random-scan temporal OS transfer and an independently
specified one-step operator on the same reconstructed random-scan OS Hilbert
carrier.  In particular, supplying a geometric Wilson transfer here is a
mathematical hypothesis, not a consequence of the name `temporal`. -/
noncomputable def
    FiniteLatticeWilsonSystem.randomScanTemporalOSStepComparisonDefect
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert) :
    L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
      L.RandomScanTwoSidedIntegerPathOSHilbert :=
  L.randomScanTwoSidedIntegerPathOSHilbertShift - candidate

@[simp] theorem
    FiniteLatticeWilsonSystem.randomScanTemporalOSStepComparisonDefect_apply
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    L.randomScanTemporalOSStepComparisonDefect candidate x =
      L.randomScanTwoSidedIntegerPathOSHilbertShift x - candidate x :=
  rfl

/-- Zero one-step defect is exactly equality with the completed random-scan OS
shift. -/
theorem
    FiniteLatticeWilsonSystem.randomScanTemporalOSStepComparisonDefect_eq_zero_iff
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert) :
    L.randomScanTemporalOSStepComparisonDefect candidate = 0 ↔
      L.randomScanTwoSidedIntegerPathOSHilbertShift = candidate := by
  unfold FiniteLatticeWilsonSystem.randomScanTemporalOSStepComparisonDefect
  exact sub_eq_zero

/-- Natural-time discrepancy between the reconstructed random-scan OS semigroup
and powers of an independently supplied same-carrier transfer. -/
noncomputable def
    FiniteLatticeWilsonSystem.randomScanTemporalOSSemigroupComparisonDefect
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert)
    (n : ℕ) :
    L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
      L.RandomScanTwoSidedIntegerPathOSHilbert :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n - candidate ^ n

/-- The random-scan semigroup defect is the generic discrete comparison defect
of the one-step random-scan OS shift and the candidate. -/
theorem
    FiniteLatticeWilsonSystem.randomScanTemporalOSSemigroupComparisonDefect_eq_generic
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert)
    (n : ℕ) :
    L.randomScanTemporalOSSemigroupComparisonDefect candidate n =
      realHilbertDiscreteSemigroupComparisonDefect
        L.randomScanTwoSidedIntegerPathOSHilbertShift candidate n := by
  rw [FiniteLatticeWilsonSystem.randomScanTemporalOSSemigroupComparisonDefect,
    realHilbertDiscreteSemigroupComparisonDefect,
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_eq_pow]

@[simp] theorem
    FiniteLatticeWilsonSystem.randomScanTemporalOSSemigroupComparisonDefect_zero
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert) :
    L.randomScanTemporalOSSemigroupComparisonDefect candidate 0 = 0 := by
  rw [L.randomScanTemporalOSSemigroupComparisonDefect_eq_generic]
  exact realHilbertDiscreteSemigroupComparisonDefect_zero _ _

@[simp] theorem
    FiniteLatticeWilsonSystem.randomScanTemporalOSSemigroupComparisonDefect_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert) :
    L.randomScanTemporalOSSemigroupComparisonDefect candidate 1 =
      L.randomScanTemporalOSStepComparisonDefect candidate := by
  rw [L.randomScanTemporalOSSemigroupComparisonDefect_eq_generic,
    realHilbertDiscreteSemigroupComparisonDefect_one]
  rfl

/-- Equality of the candidate with the random-scan OS transfer at one step is
equivalent to equality of the complete natural-time families. -/
theorem
    FiniteLatticeWilsonSystem.randomScanTemporalOSSemigroupComparisonDefect_all_eq_zero_iff
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert) :
    (∀ n : ℕ,
      L.randomScanTemporalOSSemigroupComparisonDefect candidate n = 0) ↔
      L.randomScanTwoSidedIntegerPathOSHilbertShift = candidate := by
  simp_rw [L.randomScanTemporalOSSemigroupComparisonDefect_eq_generic]
  exact realHilbertDiscreteSemigroupComparisonDefect_all_eq_zero_iff
    L.randomScanTwoSidedIntegerPathOSHilbertShift candidate

/-- A nonzero one-step discrepancy provides an exact natural-time no-go theorem
for identifying the candidate with the random-scan OS transfer family. -/
theorem
    FiniteLatticeWilsonSystem.randomScanTemporalOSSemigroupComparison_no_go
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert)
    (hCandidate :
      L.randomScanTwoSidedIntegerPathOSHilbertShift ≠ candidate) :
    ∃ n : ℕ,
      L.randomScanTemporalOSSemigroupComparisonDefect candidate n ≠ 0 := by
  rcases
      realHilbertDiscreteSemigroupComparisonDefect_exists_ne_zero_of_step_ne
        L.randomScanTwoSidedIntegerPathOSHilbertShift candidate hCandidate with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [L.randomScanTemporalOSSemigroupComparisonDefect_eq_generic]
  exact hn

/-- On completed observable classes, equality with a candidate transfer is
fully testable at the one-step path-translation level. -/
theorem
    FiniteLatticeWilsonSystem.randomScanTemporalOSStepComparisonDefect_class
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (candidate :
      L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert)
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTemporalOSStepComparisonDefect candidate
        (L.randomScanTwoSidedIntegerPathOSHilbertClass F) =
      L.randomScanTwoSidedIntegerPathOSHilbertClass
          (linearMarkovPositiveTimeShiftAlgHom F) -
        candidate (L.randomScanTwoSidedIntegerPathOSHilbertClass F) := by
  rw [L.randomScanTemporalOSStepComparisonDefect_apply,
    L.randomScanTwoSidedIntegerPathOSHilbertShift_class]

/-- The random-scan OS transfer remains a positive self-adjoint contraction;
this receipt characterizes the operator being compared without promoting it to
a geometric Wilson Euclidean-time transfer. -/
theorem
    FiniteLatticeWilsonSystem.randomScanTemporalOSTransfer_operator_receipt
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    (∀ x y : L.RandomScanTwoSidedIntegerPathOSHilbert,
      inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShift x) y =
        inner ℝ x (L.randomScanTwoSidedIntegerPathOSHilbertShift y)) ∧
    (∀ x : L.RandomScanTwoSidedIntegerPathOSHilbert,
      0 ≤ inner ℝ (L.randomScanTwoSidedIntegerPathOSHilbertShift x) x) ∧
    (∀ x : L.RandomScanTwoSidedIntegerPathOSHilbert,
      ‖L.randomScanTwoSidedIntegerPathOSHilbertShift x‖ ≤ ‖x‖) := by
  exact ⟨
    L.inner_randomScanTwoSidedIntegerPathOSHilbertShift_left_eq_right,
    L.inner_randomScanTwoSidedIntegerPathOSHilbertShift_self_nonneg,
    L.norm_randomScanTwoSidedIntegerPathOSHilbertShift_le⟩

end

end MathlibAnalytic
end MGAP4D
