import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertSpectralRadius
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSHilbertAlgebraicComplexification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Algebraic complexification of the actual finite Wilson random-scan
temporal OS Hilbert space. -/
abbrev FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.HilbertAlgebraicComplexification

/-- Algebraically complexified one-step actual finite Wilson random-scan
temporal OS shift. -/
def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →ₗ[ℂ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftAlgebraicComplexification

/-- Algebraically complexified actual finite Wilson random-scan temporal OS
semigroup. -/
def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification →ₗ[ℂ]
      L.randomScanTwoSidedIntegerPathOSHilbertAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupAlgebraicComplexification n

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_tmul
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (z : ℂ)
    (x : L.randomScanTwoSidedIntegerPathOSPreHilbertData.Hilbert) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n
        (z ⊗ₜ[ℝ] x) =
      z ⊗ₜ[ℝ]
        L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x :=
  rfl

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_zero
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification 0 = 1 :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupAlgebraicComplexification_zero

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_one
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification 1 =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupAlgebraicComplexification_one

@[simp] theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_succ
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification (n + 1) =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification.comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupAlgebraicComplexification_succ n

/-- The actual finite Wilson complexified operators retain the additive
semigroup law. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_add
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (m n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification (m + n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupAlgebraicComplexification_add m n

/-- Any two actual finite Wilson algebraically complexified temporal OS
operators commute. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_comp_comm
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (m n : ℕ) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification m).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n) =
      (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n).comp
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification m) :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupAlgebraicComplexification_comp_comm m n

/-- The actual finite Wilson algebraically complexified temporal OS semigroup
is generated by its complexified one-step shift. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification_eq_pow
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroupAlgebraicComplexification n =
      L.randomScanTwoSidedIntegerPathOSHilbertShiftAlgebraicComplexification ^ n :=
  L.randomScanTwoSidedIntegerPathOSPreHilbertData.hilbertShiftSemigroupAlgebraicComplexification_eq_pow n

end

end MathlibAnalytic
end MGAP4D
