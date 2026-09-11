import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergyConjugation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The normalized real trace of a special-unitary power is a class function.

The only matrix input is the already-proved Wilson-energy conjugation theorem,
whose proof is the cyclicity identity `Matrix.trace_mul_cycle`.  The extra
power is transported through conjugation inside the group, so no gauge
invariance hypothesis is introduced. -/
theorem normalizedSpecialUnitaryRealTrace_pow_conjInvariant
    {N : ℕ}
    (h g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (j : ℕ) :
    normalizedSpecialUnitaryRealTrace N ((h * g * h⁻¹) ^ j) =
      normalizedSpecialUnitaryRealTrace N (g ^ j) := by
  have hpow : (h * g * h⁻¹) ^ j = h * g ^ j * h⁻¹ := by
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, pow_succ, ih]
        group
  rw [hpow]
  have hEnergy := specialUnitaryWilsonPlaquetteEnergy_conjInvariant h (g ^ j)
  rw [specialUnitaryWilsonPlaquetteEnergy_eq,
    specialUnitaryWilsonPlaquetteEnergy_eq] at hEnergy
  linarith

/-- For the actual signed periodic `SU(N)` Wilson system, every normalized
trace power of a plaquette holonomy is gauge invariant.

The proof is entirely constructive: compact oriented holonomy covariance gives
conjugation at the plaquette base vertex, and the preceding class-function
lemma removes that conjugation after taking the power and normalized trace. -/
theorem periodicHypercubicSpecialUnitary_plaquetteNormalizedTracePower_gaugeInvariant
    (n N : ℕ)
    [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (gamma :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).base.GaugeTransformation)
    (A : PeriodicHypercubicEdge n →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (p : PeriodicHypercubicPlaquette n)
    (j : ℕ) :
    normalizedSpecialUnitaryRealTrace N
        (((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).base.plaquetteHolonomy
            ((periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta beta_nonneg).base.gaugeTransform gamma A) p) ^ j) =
      normalizedSpecialUnitaryRealTrace N
        (((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).base.plaquetteHolonomy A p) ^ j) := by
  rw [compact_oriented_plaquetteHolonomy_gaugeTransform]
  exact normalizedSpecialUnitaryRealTrace_pow_conjInvariant _ _ j

end

end MathlibAnalytic
end MGAP4D
