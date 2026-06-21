import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionSectorReflection
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Positive-open-half Wilson Boltzmann amplitude. -/
noncomputable def periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta * periodicHypercubicEvenPositiveWilsonAction H N A)

/-- Negative-open-half Wilson Boltzmann amplitude. -/
noncomputable def periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta * periodicHypercubicEvenNegativeWilsonAction H N A)

/-- Crossing-sector Wilson Boltzmann weight. -/
noncomputable def periodicHypercubicEvenCrossingWilsonBoltzmannWeight
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  Real.exp (-beta * periodicHypercubicEvenCrossingWilsonAction H N A)

/-- The logarithmic Wilson Gibbs weight is exactly the sum of its positive,
negative, and crossing logarithmic sector weights. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_gibbsExponent_exact_sector_decomposition
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.gibbsExponent A =
      (-beta * periodicHypercubicEvenPositiveWilsonAction H N A) +
      (-beta * periodicHypercubicEvenNegativeWilsonAction H N A) +
      (-beta * periodicHypercubicEvenCrossingWilsonAction H N A) := by
  unfold CompactOrientedGaugeWilsonSystem.gibbsExponent
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_exact_sector_decomposition]
  change
    -beta *
        (periodicHypercubicEvenPositiveWilsonAction H N A +
          periodicHypercubicEvenNegativeWilsonAction H N A +
          periodicHypercubicEvenCrossingWilsonAction H N A) =
      (-beta * periodicHypercubicEvenPositiveWilsonAction H N A) +
      (-beta * periodicHypercubicEvenNegativeWilsonAction H N A) +
      (-beta * periodicHypercubicEvenCrossingWilsonAction H N A)
  ring

/-- Exponentiating the exact action-sector decomposition factors the genuine
finite-volume Wilson Gibbs weight into two open-half amplitudes and one crossing
weight.  No independence of the two halves is asserted: the crossing interaction
remains explicit in the final factor. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_exp_gibbsExponent_eq_sector_product
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.gibbsExponent A) =
      periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta A *
      periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude H N beta A *
      periodicHypercubicEvenCrossingWilsonBoltzmannWeight H N beta A := by
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_gibbsExponent_exact_sector_decomposition]
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenCrossingWilsonBoltzmannWeight
  rw [Real.exp_add, Real.exp_add]

/-- Reflection exchanges the positive Wilson Boltzmann amplitude with the
negative Wilson Boltzmann amplitude. -/
theorem periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude H N beta A := by
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude
  rw [periodicHypercubicEvenPositiveWilsonAction_configurationReflection]

/-- Reflection exchanges the negative Wilson Boltzmann amplitude with the
positive Wilson Boltzmann amplitude. -/
theorem periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude_configurationReflection
    (H N : ℕ)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude H N beta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude H N beta A := by
  unfold periodicHypercubicEvenNegativeWilsonBoltzmannAmplitude
  unfold periodicHypercubicEvenPositiveWilsonBoltzmannAmplitude
  rw [periodicHypercubicEvenNegativeWilsonAction_configurationReflection]

/-- Reflection preserves the crossing-sector Wilson Boltzmann weight. -/
theorem periodicHypercubicEvenCrossingWilsonBoltzmannWeight_configurationReflection
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenCrossingWilsonBoltzmannWeight H N beta
        (periodicHypercubicEvenConfigurationReflection H A) =
      periodicHypercubicEvenCrossingWilsonBoltzmannWeight H N beta A := by
  unfold periodicHypercubicEvenCrossingWilsonBoltzmannWeight
  rw [periodicHypercubicEvenCrossingWilsonAction_configurationReflection H N hN]

end

end MathlibAnalytic
end MGAP4D
