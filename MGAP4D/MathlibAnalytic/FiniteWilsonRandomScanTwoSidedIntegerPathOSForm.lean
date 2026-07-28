import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanTwoSidedIntegerPositiveTimeOS
import MGAP4D.MathlibAnalytic.LinearMarkovTwoSidedIntegerPathOSNull

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The full temporal Osterwalder--Schrader bilinear form for the actual finite
Wilson Gibbs-stationary random-scan two-sided path law. -/
def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSForm
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) : ℝ :=
  linearMarkovTwoSidedIntegerPathOSForm
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) F G

/-- The actual Wilson OS form is the reflected product integral on the full
countably additive two-sided path measure. -/
theorem FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSForm_eq_integral
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSForm F G =
      ∫ path,
        ((F : (ℕ → L.Configuration) → ℝ)
          (linearMarkovIntegerPathNonnegativeRestriction
            (linearMarkovIntegerPathReflection path))) *
        ((G : (ℕ → L.Configuration) → ℝ)
          (linearMarkovIntegerPathNonnegativeRestriction path))
        ∂L.randomScanTwoSidedIntegerPathMeasure := by
  unfold FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSForm
    linearMarkovTwoSidedIntegerPathOSForm
    FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathMeasure
  rfl

/-- Symmetry of the actual finite Wilson full path-space OS form. -/
theorem finite_lattice_randomScanTwoSidedIntegerPathOSForm_symmetric
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    L.randomScanTwoSidedIntegerPathOSForm F G =
      L.randomScanTwoSidedIntegerPathOSForm G F := by
  exact linearMarkovTwoSidedIntegerPathOSForm_symmetric
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) F G

/-- Diagonal reflection positivity of the actual finite Wilson OS form. -/
theorem finite_lattice_randomScanTwoSidedIntegerPathOSForm_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    0 ≤ L.randomScanTwoSidedIntegerPathOSForm F F := by
  exact linearMarkovTwoSidedIntegerPathOSForm_nonneg
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) F

/-- Cauchy--Schwarz inequality for the actual finite Wilson OS form. -/
theorem finite_lattice_randomScanTwoSidedIntegerPathOSForm_cauchy_schwarz
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F G : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    (L.randomScanTwoSidedIntegerPathOSForm F G) ^ 2 ≤
      L.randomScanTwoSidedIntegerPathOSForm F F *
        L.randomScanTwoSidedIntegerPathOSForm G G := by
  exact linearMarkovTwoSidedIntegerPathOSForm_cauchy_schwarz
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) F G

/-- The OS null submodule for the actual finite Wilson random-scan path law. -/
def FiniteLatticeWilsonSystem.randomScanTwoSidedIntegerPathOSNull
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge] :
    Submodule ℝ
      (linearMarkovPositiveTimeCylinderSubalgebra
        (Ω := L.Configuration)) :=
  linearMarkovTwoSidedIntegerPathOSNull
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L)

@[simp] theorem FiniteLatticeWilsonSystem.mem_randomScanTwoSidedIntegerPathOSNull_iff
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    F ∈ L.randomScanTwoSidedIntegerPathOSNull ↔
      L.randomScanTwoSidedIntegerPathOSForm F F = 0 :=
  Iff.rfl

/-- Wilson OS-null observables are exactly those orthogonal to every generated
positive-time cylinder observable. -/
theorem FiniteLatticeWilsonSystem.mem_randomScanTwoSidedIntegerPathOSNull_iff_forall_orthogonal
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (F : linearMarkovPositiveTimeCylinderSubalgebra
      (Ω := L.Configuration)) :
    F ∈ L.randomScanTwoSidedIntegerPathOSNull ↔
      ∀ G : linearMarkovPositiveTimeCylinderSubalgebra
          (Ω := L.Configuration),
        L.randomScanTwoSidedIntegerPathOSForm F G = 0 := by
  exact mem_linearMarkovTwoSidedIntegerPathOSNull_iff_forall_orthogonal
    L.gibbsPMF L.randomScanTransitionPMF
      (finite_lattice_randomScanDetailedBalanceReal L) F

end

end MathlibAnalytic
end MGAP4D
