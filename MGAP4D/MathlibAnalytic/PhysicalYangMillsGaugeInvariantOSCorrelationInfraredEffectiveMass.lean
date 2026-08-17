import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCorrelationEffectiveMassRayleighUpper
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
# Infrared limit of the physical OS effective mass

The zero-based unregularized physical OS effective mass is antitone for positive
Euclidean time and nonnegative.  Therefore its long-time tail has a canonical
finite infrared limit.  We construct that limit directly as the conditional
infimum of the continuous tail `t = u + 1`, `u : NNReal`, and use Mathlib's
`tendsto_atTop_ciInf` monotone-convergence theorem to prove convergence.

For every nonzero state in the canonical right-generator domain this gives

`0 <= m_IR <= m_eff(0,t) <= <H_right psi, psi> / ||psi||^2`

for every positive finite Euclidean time `t`.

No spectral theorem, PVM, self-adjointness hypothesis, exponential-decay
assumption, or new physical axiom is used.
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

/-- The infrared effective mass is the conditional infimum of the positive
zero-based effective-mass tail.  The shift by one avoids the degenerate secant
at `t = 0` while remaining cofinal at long Euclidean time. -/
def physicalCorrelationRealClampInfraredEffectiveMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) : ℝ :=
  ⨅ u : NNReal,
    T.physicalCorrelationRealClampEffectiveMass
      psi 0 (((u + 1 : NNReal) : ℝ))

/-- The shifted positive-time effective-mass tail is antitone. -/
theorem physicalCorrelationRealClampEffectiveMass_shift_antitone
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    Antitone
      (fun u : NNReal =>
        T.physicalCorrelationRealClampEffectiveMass
          psi 0 (((u + 1 : NNReal) : ℝ))) := by
  intro u v huv
  apply T.physicalCorrelationRealClampEffectiveMass_zero_antitone
    hSymmetric hpsi
  · have hu : (0 : NNReal) < u + 1 := by positivity
    exact_mod_cast hu
  · have huv' : u + 1 ≤ v + 1 := add_le_add_right huv 1
    exact_mod_cast huv'

/-- The shifted effective-mass tail is bounded below by zero. -/
theorem physicalCorrelationRealClampEffectiveMass_shift_bddBelow
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    BddBelow
      (Set.range
        (fun u : NNReal =>
          T.physicalCorrelationRealClampEffectiveMass
            psi 0 (((u + 1 : NNReal) : ℝ)))) := by
  refine ⟨0, ?_⟩
  rintro y ⟨u, rfl⟩
  apply T.physicalCorrelationRealClampEffectiveMass_nonneg
    hSymmetric hpsi
  positivity

/-- The physical OS effective mass has a finite long-time infrared limit,
constructed rather than assumed. -/
theorem physicalCorrelationRealClampEffectiveMass_shift_tendsto_infrared
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    Tendsto
      (fun u : NNReal =>
        T.physicalCorrelationRealClampEffectiveMass
          psi 0 (((u + 1 : NNReal) : ℝ)))
      atTop
      (nhds (T.physicalCorrelationRealClampInfraredEffectiveMass psi)) := by
  unfold physicalCorrelationRealClampInfraredEffectiveMass
  exact tendsto_atTop_ciInf
    (T.physicalCorrelationRealClampEffectiveMass_shift_antitone
      hSymmetric hpsi)
    (T.physicalCorrelationRealClampEffectiveMass_shift_bddBelow
      hSymmetric hpsi)

/-- The infrared effective mass is nonnegative. -/
theorem physicalCorrelationRealClampInfraredEffectiveMass_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0) :
    0 ≤ T.physicalCorrelationRealClampInfraredEffectiveMass psi := by
  have hlim :=
    T.physicalCorrelationRealClampEffectiveMass_shift_tendsto_infrared
      hSymmetric hpsi
  apply ge_of_tendsto hlim
  filter_upwards with u
  apply T.physicalCorrelationRealClampEffectiveMass_nonneg
    hSymmetric hpsi
  positivity

/-- The infrared limit is a lower bound for every positive finite-time
zero-based effective mass, including times below the chosen tail shift. -/
theorem physicalCorrelationRealClampInfraredEffectiveMass_le_effectiveMass_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert} (hpsi : psi ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    T.physicalCorrelationRealClampInfraredEffectiveMass psi ≤
      T.physicalCorrelationRealClampEffectiveMass psi 0 (t : ℝ) := by
  have hlim :=
    T.physicalCorrelationRealClampEffectiveMass_shift_tendsto_infrared
      hSymmetric hpsi
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop t] with u hu
  apply T.physicalCorrelationRealClampEffectiveMass_zero_antitone
    hSymmetric hpsi
  · exact_mod_cast ht
  · have hut : t ≤ u + 1 := le_trans hu (le_add_right (le_refl u))
    exact_mod_cast hut

/-- The constructed infrared effective mass is bounded above by the canonical
right-Hamiltonian Rayleigh quotient. -/
theorem physicalCorrelationRealClampInfraredEffectiveMass_le_rightHamiltonian_rayleigh
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0) :
    T.physicalCorrelationRealClampInfraredEffectiveMass
        (psi : P.PhysicalHilbert) ≤
      ⟪T.rightHamiltonian psi,
          (psi : P.PhysicalHilbert)⟫_ℝ /
        ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
  have hlim :=
    T.physicalCorrelationRealClampEffectiveMass_shift_tendsto_infrared
      hSymmetric hpsi
  apply le_of_tendsto hlim
  filter_upwards with u
  have hu : (0 : NNReal) < u + 1 := by positivity
  exact
    T.physicalCorrelationRealClampEffectiveMass_zero_le_rightHamiltonian_rayleigh
      hSymmetric psi hpsi (u + 1) hu

/-- Complete UV-to-IR effective-mass sandwich along the physical OS
correlation. -/
theorem physicalCorrelationRealClampEffectiveMass_uv_ir_sandwich
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (psi : T.rightGeneratorDomain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    0 ≤ T.physicalCorrelationRealClampInfraredEffectiveMass
          (psi : P.PhysicalHilbert) ∧
      T.physicalCorrelationRealClampInfraredEffectiveMass
          (psi : P.PhysicalHilbert) ≤
        T.physicalCorrelationRealClampEffectiveMass
          (psi : P.PhysicalHilbert) 0 (t : ℝ) ∧
      T.physicalCorrelationRealClampEffectiveMass
          (psi : P.PhysicalHilbert) 0 (t : ℝ) ≤
        ⟪T.rightHamiltonian psi,
            (psi : P.PhysicalHilbert)⟫_ℝ /
          ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
  constructor
  · exact T.physicalCorrelationRealClampInfraredEffectiveMass_nonneg
      hSymmetric hpsi
  constructor
  · exact
      T.physicalCorrelationRealClampInfraredEffectiveMass_le_effectiveMass_zero
        hSymmetric hpsi t ht
  · exact
      T.physicalCorrelationRealClampEffectiveMass_zero_le_rightHamiltonian_rayleigh
        hSymmetric psi hpsi t ht

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
