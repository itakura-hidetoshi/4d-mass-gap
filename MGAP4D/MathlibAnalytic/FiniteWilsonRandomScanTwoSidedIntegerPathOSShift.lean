import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSPreHilbert
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSShiftQuotient

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The one-step positive-time shift on the actual finite Wilson separated temporal
OS pre-Hilbert space. -/
noncomputable def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSShiftLinearMap
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.RandomScanTwoSidedIntegerPathOSPreHilbert →ₗ[ℝ]
      L.RandomScanTwoSidedIntegerPathOSPreHilbert :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.separatedShiftLinearMap

/-- The actual Wilson shift sends an observable class to the class of its
positive-time translate. -/
@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSShiftLinearMap_class
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSShiftLinearMap
        (L.randomScanTwoSidedIntegerPathOSClass F) =
      L.randomScanTwoSidedIntegerPathOSClass
        (linearMarkovPositiveTimeShiftAlgHom F) := by
  exact
    LinearMarkovTwoSidedIntegerPathOSPreHilbertData.separatedShiftLinearMap_observableClass
      L.randomScanTwoSidedIntegerPathOSPreHilbertData F

/-- The actual finite Wilson positive-time shift preserves the temporal OS null
submodule. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSNull_shift
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration))
    (hF : F ∈ L.randomScanTwoSidedIntegerPathOSNull) :
    linearMarkovPositiveTimeShiftAlgHom F ∈
      L.randomScanTwoSidedIntegerPathOSNull := by
  exact linearMarkovPositiveTimeShift_mem_twoSidedIntegerPathOSNull
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) F hF

/-- The descended actual finite Wilson positive-time shift is symmetric for the
separated temporal OS inner product. -/
theorem FiniteLatticeWilsonSystem.inner_randomScanTwoSidedIntegerPathOSShift_left_eq_right
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (x y : L.RandomScanTwoSidedIntegerPathOSPreHilbert) :
    inner ℝ (L.randomScanTwoSidedIntegerPathOSShiftLinearMap x) y =
      inner ℝ x (L.randomScanTwoSidedIntegerPathOSShiftLinearMap y) := by
  exact
    LinearMarkovTwoSidedIntegerPathOSPreHilbertData.inner_separatedShiftLinearMap_left_eq_right
      L.randomScanTwoSidedIntegerPathOSPreHilbertData x y

end

end MathlibAnalytic
end MGAP4D
