import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSPreHilbert
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertCompletion

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The complete temporal OS Hilbert space of the actual finite Wilson
Gibbs-stationary random-scan two-sided path law. -/
abbrev FiniteLatticeWilsonSystem.RandomScanTwoSidedIntegerPathOSHilbert
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.Hilbert

/-- The canonical dense embedding of the actual finite Wilson separated OS
pre-Hilbert space into its Hilbert completion. -/
def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSPreHilbertToHilbert
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSPreHilbert) :
    L.RandomScanTwoSidedIntegerPathOSHilbert :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.completedClass x

/-- The completed actual finite Wilson OS vector represented by a positive-time
cylinder observable. -/
def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertClass
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.RandomScanTwoSidedIntegerPathOSHilbert :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.completedObservableClass F

/-- The actual finite Wilson separated OS pre-Hilbert space is dense in its
Hilbert completion. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSPreHilbert_dense
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    DenseRange L.randomScanTwoSidedIntegerPathOSPreHilbertToHilbert := by
  exact
    L.randomScanTwoSidedIntegerPathOSPreHilbertData.separated_dense_in_hilbert

/-- The Hilbert inner product of completed actual Wilson OS classes is exactly the
full random-scan two-sided path-space OS form. -/
@[simp] theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSHilbertClass
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertClass F)
        (L.randomScanTwoSidedIntegerPathOSHilbertClass G) =
      L.randomScanTwoSidedIntegerPathOSForm F G := by
  change
    linearMarkovTwoSidedIntegerPathOSForm
        L.gibbsPMF L.randomScanTransitionPMF
          (finite_lattice_randomScanDetailedBalanceReal L) F G =
      L.randomScanTwoSidedIntegerPathOSForm F G
  rfl

/-- The actual finite Wilson temporal OS Hilbert space is positive definite. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbert_inner_self_eq_zero_iff
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ x x = 0 ↔ x = 0 :=
  LinearMarkovTwoSidedIntegerPathOSPreHilbertData.hilbert_inner_self_eq_zero_iff
    L.randomScanTwoSidedIntegerPathOSPreHilbertData x

/-- The actual finite Wilson temporal OS Hilbert space is complete. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbert_complete
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    CompleteSpace L.RandomScanTwoSidedIntegerPathOSHilbert := by
  infer_instance

end

end MathlibAnalytic
end MGAP4D
