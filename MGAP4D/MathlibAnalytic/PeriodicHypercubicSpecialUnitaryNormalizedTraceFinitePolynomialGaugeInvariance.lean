import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryNormalizedTracePowerGaugeInvariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite real polynomial in normalized real traces of powers of one
special-unitary element.

The finite support is kept explicit as a `Finset ℕ`; this is exactly the form
needed by the finite Wilson/cylinder algebra and avoids introducing any
additional analytic or physical assumption. -/
def normalizedSpecialUnitaryRealTraceFinitePolynomial
    {N : ℕ}
    (s : Finset ℕ)
    (c : ℕ → ℝ)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  s.sum (fun j => c j * normalizedSpecialUnitaryRealTrace N (g ^ j))

/-- Every finite real polynomial in normalized trace powers is a class
function on `SU(N)`.

This is only finite-sum linearity applied to
`normalizedSpecialUnitaryRealTrace_pow_conjInvariant`; no new gauge or physics
hypothesis is used. -/
theorem normalizedSpecialUnitaryRealTraceFinitePolynomial_conjInvariant
    {N : ℕ}
    (s : Finset ℕ)
    (c : ℕ → ℝ)
    (h g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    normalizedSpecialUnitaryRealTraceFinitePolynomial s c (h * g * h⁻¹) =
      normalizedSpecialUnitaryRealTraceFinitePolynomial s c g := by
  unfold normalizedSpecialUnitaryRealTraceFinitePolynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [normalizedSpecialUnitaryRealTrace_pow_conjInvariant]

/-- The actual signed periodic `SU(N)` plaquette normalized-trace polynomial.
It is the finite linear span of the already-constructed normalized trace-power
observables. -/
def periodicHypercubicSpecialUnitary_plaquetteNormalizedTraceFinitePolynomial
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (s : Finset ℕ)
    (c : ℕ → ℝ)
    (A : PeriodicHypercubicEdge n →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicPlaquette n) : ℝ :=
  normalizedSpecialUnitaryRealTraceFinitePolynomial s c
    ((periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).base.plaquetteHolonomy A p)

/-- Every finite normalized-trace polynomial of an actual plaquette holonomy is
gauge invariant.

Actual plaquette covariance supplies conjugation at the base vertex, while the
finite class-function theorem above removes it term-by-term. -/
theorem periodicHypercubicSpecialUnitary_plaquetteNormalizedTraceFinitePolynomial_gaugeInvariant
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (gamma :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.GaugeTransformation)
    (s : Finset ℕ)
    (c : ℕ → ℝ)
    (A : PeriodicHypercubicEdge n →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicSpecialUnitary_plaquetteNormalizedTraceFinitePolynomial
        n N hN beta beta_nonneg s c
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).base.gaugeTransform gamma A) p =
      periodicHypercubicSpecialUnitary_plaquetteNormalizedTraceFinitePolynomial
        n N hN beta beta_nonneg s c A p := by
  unfold periodicHypercubicSpecialUnitary_plaquetteNormalizedTraceFinitePolynomial
  rw [compact_oriented_plaquetteHolonomy_gaugeTransform]
  exact normalizedSpecialUnitaryRealTraceFinitePolynomial_conjInvariant s c _ _

end

end MathlibAnalytic
end MGAP4D
