import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumLogStepRate
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/-!
# Vacuum-gap slope below the infrared physical OS mass

For a nonzero physical state orthogonal to the vacuum, the preceding layer shows
that every positive one-step vacuum-gap slope

`t⁻¹ * (1 - decayFactor t)`

is below the normalized physical OS logarithmic decay at every positive discrete
even time `2 n t`.

This file uses Archimedean cofinality of the discrete times and the already
constructed antitone zero-based effective-mass tail to show that the same slope
is below the infrared effective mass.  Passing to `t -> 0+` through the existing
`VacuumSemigroupGapSlope.slope_tendsto` theorem then gives

`mass ≤ m_IR`.

No spectral theorem, PVM, exponential-decay hypothesis, self-adjointness
assumption, or new physical axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Every positive one-step vacuum-gap slope is below the infrared physical OS
effective mass of a nonzero vacuum-orthogonal state. -/
theorem VacuumSemigroupGapSlope.slope_le_infraredEffectiveMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (t : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0)
    (ht : 0 < t) :
    (t : ℝ)⁻¹ * (1 - G.decayFactor t) ≤
      T.physicalCorrelationRealClampInfraredEffectiveMass psi := by
  unfold physicalCorrelationRealClampInfraredEffectiveMass
  refine le_ciInf (fun u => ?_)
  have htReal : 0 < (t : ℝ) := by
    exact_mod_cast ht
  have hden : 0 < 2 * (t : ℝ) := by positivity
  have hx :
      0 < (((u + 1 : NNReal) : ℝ) / (2 * (t : ℝ))) := by
    positivity
  obtain ⟨n, hn⟩ :=
    exists_nat_gt (((u + 1 : NNReal) : ℝ) / (2 * (t : ℝ)))
  have hnReal : 0 < (n : ℝ) := hx.trans hn
  have hnPos : 0 < n := by
    exact_mod_cast hnReal
  have hmul :
      (((u + 1 : NNReal) : ℝ)) <
        (n : ℝ) * (2 * (t : ℝ)) :=
    (div_lt_iff₀ hden).mp hn
  have htime :
      (((u + 1 : NNReal) : ℝ)) ≤
        (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) := by
    norm_num at hmul ⊢
    nlinarith
  have hslope :=
    G.slope_le_normalizedLogDecayFromZero_nat_mul_add_self
      T hSymmetric t n hpsi hpsi_ne ht hnPos
  rw [T.physicalCorrelationRealClampNormalizedLogDecayFromZero_eq_effectiveMass]
    at hslope
  have hanti :
      T.physicalCorrelationRealClampEffectiveMass psi 0
          (((((n : NNReal) * t) + ((n : NNReal) * t) : NNReal) : ℝ)) ≤
        T.physicalCorrelationRealClampEffectiveMass psi 0
          (((u + 1 : NNReal) : ℝ)) := by
    apply T.physicalCorrelationRealClampEffectiveMass_zero_antitone
      hSymmetric hpsi
    · positivity
    · exact htime
  exact hslope.trans hanti

/-- The vacuum-sector mass carried by `VacuumSemigroupGapSlope` is bounded below
by the actual infrared logarithmic decay exponent of every nonzero
vacuum-orthogonal physical state. -/
theorem VacuumSemigroupGapSlope.mass_le_infraredEffectiveMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    G.mass ≤ T.physicalCorrelationRealClampInfraredEffectiveMass psi := by
  apply le_of_tendsto G.slope_tendsto
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact
    G.slope_le_infraredEffectiveMass
      T hSymmetric t hpsi hpsi_ne ht

/-- Finite-volume transfer wrapper for the infrared mass lower bound. -/
theorem FiniteVolumeVacuumGapTransfer.mass_le_infraredEffectiveMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0) :
    G.mass ≤ T.physicalCorrelationRealClampInfraredEffectiveMass psi := by
  exact
    G.toVacuumSemigroupGapSlope.mass_le_infraredEffectiveMass
      T hSymmetric hpsi hpsi_ne

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
