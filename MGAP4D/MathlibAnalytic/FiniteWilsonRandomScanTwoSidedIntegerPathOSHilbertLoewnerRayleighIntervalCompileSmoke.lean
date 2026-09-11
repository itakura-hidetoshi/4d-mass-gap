import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPathOSHilbertLoewnerRayleighInterval

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    inner ℝ
        (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n x) x ≤
      inner ℝ x x :=
  L.inner_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_self_le n x

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    ((1 : L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
        L.RandomScanTwoSidedIntegerPathOSHilbert) -
      L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).IsPositive :=
  L.one_sub_randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_isPositive n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n ∈
      Set.Icc
        (0 : L.RandomScanTwoSidedIntegerPathOSHilbert →L[ℝ]
          L.RandomScanTwoSidedIntegerPathOSHilbert)
        1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_mem_Icc n

example
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (x : L.RandomScanTwoSidedIntegerPathOSHilbert) :
    (L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup n).rayleighQuotient x ∈
      Set.Icc (0 : ℝ) 1 :=
  L.randomScanTwoSidedIntegerPathOSHilbertShiftSemigroup_rayleighQuotient_mem_Icc n x

end

end MathlibAnalytic
end MGAP4D
