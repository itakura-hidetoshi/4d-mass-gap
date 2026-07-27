import MGAP4D.MathlibAnalytic.LinearMarkovCenteredTimeReflectionPMF
import MGAP4D.MathlibAnalytic.FiniteWilsonRandomScanPositiveTimeOSGram
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual finite Wilson path centered at time zero with a reflected and a
positive finite random-scan future. -/
abbrev FiniteLatticeWilsonSystem.RandomScanCenteredFinitePath
    (L : FiniteLatticeWilsonSystem)
    (n : ℕ) :=
  LinearMarkovCenteredFinitePath L.Configuration n

/-- The actual Gibbs-centered finite reflected random-scan path PMF. -/
abbrev FiniteLatticeWilsonSystem.randomScanCenteredFinitePathPMF
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    PMF (L.RandomScanCenteredFinitePath n) :=
  linearMarkovCenteredFinitePathPMF
    L.gibbsPMF L.randomScanTransitionPMF n

/-- Actual finite Wilson centered time reflection. -/
abbrev FiniteLatticeWilsonSystem.randomScanCenteredFinitePathReflection
    (L : FiniteLatticeWilsonSystem)
    {n : ℕ} :
    L.RandomScanCenteredFinitePath n →
      L.RandomScanCenteredFinitePath n :=
  linearMarkovCenteredFinitePathReflection

/-- The actual finite Wilson centered path law is reflection invariant. -/
theorem finite_lattice_randomScanCenteredFinitePathPMF_map_reflection
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ) :
    (L.randomScanCenteredFinitePathPMF n).map
        L.randomScanCenteredFinitePathReflection =
      L.randomScanCenteredFinitePathPMF n :=
  linearMarkovCenteredFinitePathPMF_map_reflection
    L.gibbsPMF L.randomScanTransitionPMF n

/-- Reflection invariance of the actual centered Wilson path law in expectation
form. -/
theorem finite_lattice_randomScanCenteredFinitePathPMF_expectation_reflection
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (H : L.RandomScanCenteredFinitePath n → ℝ) :
    finitePMFExpectationReal
        (L.randomScanCenteredFinitePathPMF n)
        (H ∘ L.randomScanCenteredFinitePathReflection) =
      finitePMFExpectationReal
        (L.randomScanCenteredFinitePathPMF n) H :=
  linearMarkovCenteredFinitePathPMF_expectation_reflection
    L.gibbsPMF L.randomScanTransitionPMF n H

/-- The concrete finite Wilson temporal OS bilinear form is exactly the
reflected-product expectation under the actual centered finite path PMF. -/
theorem finite_lattice_randomScanCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (F G : LinearMarkovPositiveTimeFuturePath L.Configuration n → ℝ) :
    finitePMFExpectationReal
        (L.randomScanCenteredFinitePathPMF n)
        (fun path =>
          linearMarkovCenteredFinitePathPositiveLift F
              (L.randomScanCenteredFinitePathReflection path) *
            linearMarkovCenteredFinitePathPositiveLift G path) =
      L.randomScanPositiveTimeOSForm n F G :=
  linearMarkovCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm
    L.gibbsPMF L.randomScanTransitionPMF n F G

/-- The temporal OS quadratic form of every actual finite Wilson future
observable is therefore an honest reflected expectation under a
reflection-invariant PMF. -/
theorem finite_lattice_randomScanCenteredFinitePathPMF_reflectedSquare_expectation_nonneg
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (F : LinearMarkovPositiveTimeFuturePath L.Configuration n → ℝ) :
    0 ≤ finitePMFExpectationReal
        (L.randomScanCenteredFinitePathPMF n)
        (fun path =>
          linearMarkovCenteredFinitePathPositiveLift F
              (L.randomScanCenteredFinitePathReflection path) *
            linearMarkovCenteredFinitePathPositiveLift F path) := by
  rw [finite_lattice_randomScanCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm]
  exact finite_lattice_randomScanPositiveTimeOSForm_nonneg L n F

/-- For a positive-time product cylinder, the centered reflected expectation is
the Gibbs expectation of the square of the already constructed conditional
boundary cylinder amplitude. -/
theorem finite_lattice_randomScanCenteredFinitePathPMF_product_reflectedSquare_eq_gibbs_boundary_sq
    (L : FiniteLatticeWilsonSystem)
    [Nonempty L.Edge]
    (n : ℕ)
    (fs : Fin (n + 1) → L.Configuration → ℝ) :
    finitePMFExpectationReal
        (L.randomScanCenteredFinitePathPMF n)
        (fun path =>
          linearMarkovCenteredFinitePathPositiveLift
              (linearMarkovFinitePathProduct fs)
              (L.randomScanCenteredFinitePathReflection path) *
            linearMarkovCenteredFinitePathPositiveLift
              (linearMarkovFinitePathProduct fs) path) =
      L.gibbsExpectationReal
        (fun boundary =>
          (L.randomScanPositiveTimeBoundaryCylinderAmplitude
            n fs boundary) ^ 2) := by
  rw [finite_lattice_randomScanCenteredFinitePathPMF_reflectedProduct_expectation_eq_OSForm]
  exact finite_lattice_randomScanPositiveTimeOSForm_product_eq_gibbs_boundary_sq
    L n fs

end

end MathlibAnalytic
end MGAP4D
