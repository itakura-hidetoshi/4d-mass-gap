import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassGeneratorDomainNormDecay
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverageGeneratorDomain
import Mathlib.Tactic

/-!
# Full vacuum-orthogonal norm decay from the derived physical Yang--Mills mass

The preceding layer proves

`‖T_t ψ‖ ≤ ‖ψ‖ * exp (-physicalYangMillsMass * t)`

for vacuum-orthogonal vectors in the canonical right-generator domain.

This file removes the generator-domain restriction without adding a new physical
assumption.  For an arbitrary vacuum-orthogonal physical Hilbert vector `ψ`, we
use the already constructed time averages and subtract their vacuum component:

`A_h ψ - ⟪A_h ψ, Ω⟫_ℝ Ω`.

Because the right-generator domain is a linear subspace containing the vacuum,
these centered averages remain in the generator domain.  Vacuum normalization
makes them exactly vacuum-orthogonal, and strong continuity of the time averages
makes them converge back to `ψ` as `h → 0+`.

For fixed `t`, the desired norm inequality defines a closed subset of the
physical Hilbert space.  The generator-domain estimate therefore extends across
the closure to the complete vacuum-orthogonal sector.

No spectral theorem, functional-calculus identity `T_t = exp (-t H)`, exact
numerical mass value, PVM atom, or additional physical hypothesis is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Real
open scoped InnerProductSpace Topology NNReal

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Time-average approximation with its scalar vacuum component removed. -/
def vacuumCenteredTimeAverage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) : P.PhysicalHilbert :=
  T.timeAverage h psi -
    inner ℝ (T.timeAverage h psi) P.vacuum • P.vacuum

/-- Every vacuum-centered time average remains in the canonical right-generator
 domain.  This uses only linearity of the domain and the fact that the vacuum is
 itself a generator-domain vector. -/
theorem vacuumCenteredTimeAverage_mem_rightGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.vacuumCenteredTimeAverage h psi ∈ T.rightGeneratorDomain := by
  apply T.rightGeneratorDomain.sub_mem
  · exact T.timeAverage_mem_rightGeneratorDomain h psi
  · exact T.rightGeneratorDomain.smul_mem
      (inner ℝ (T.timeAverage h psi) P.vacuum)
      T.vacuum_mem_rightGeneratorDomain

/-- Vacuum normalization makes the centered time average exactly orthogonal to
 the vacuum. -/
theorem vacuumCenteredTimeAverage_inner_vacuum_eq_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    inner ℝ (T.vacuumCenteredTimeAverage h psi) P.vacuum = 0 := by
  simp [vacuumCenteredTimeAverage, inner_sub_left, inner_smul_left,
    P.norm_vacuum hP]

/-- On an already vacuum-orthogonal state, centered time averages converge back
 to the original state as positive averaging width tends to zero. -/
theorem vacuumCenteredTimeAverage_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert)
    (horthogonal : inner ℝ psi P.vacuum = 0) :
    Tendsto (fun h : NNReal => T.vacuumCenteredTimeAverage h psi)
      (nhdsWithin 0 (Ioi 0)) (nhds psi) := by
  have htime := T.timeAverage_tendsto_zero psi
  have hinner := htime.inner (𝕜 := ℝ)
    (tendsto_const_nhds :
      Tendsto (fun _ : NNReal => P.vacuum)
        (nhdsWithin 0 (Ioi 0)) (nhds P.vacuum))
  have hsmul := hinner.smul
    (tendsto_const_nhds :
      Tendsto (fun _ : NNReal => P.vacuum)
        (nhdsWithin 0 (Ioi 0)) (nhds P.vacuum))
  have hsub := htime.sub hsmul
  simpa [vacuumCenteredTimeAverage, horthogonal] using hsub

/-- Vacuum-orthogonal generator-domain vectors are dense at every
 vacuum-orthogonal physical Hilbert vector. -/
theorem mem_closure_rightGeneratorDomain_inner_vacuum_eq_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (psi : P.PhysicalHilbert)
    (horthogonal : inner ℝ psi P.vacuum = 0) :
    psi ∈ closure
      {phi : P.PhysicalHilbert |
        phi ∈ T.rightGeneratorDomain ∧ inner ℝ phi P.vacuum = 0} := by
  apply mem_closure_of_tendsto
    (T.vacuumCenteredTimeAverage_tendsto_zero psi horthogonal)
  filter_upwards [self_mem_nhdsWithin] with h _hh
  exact ⟨T.vacuumCenteredTimeAverage_mem_rightGeneratorDomain h psi,
    T.vacuumCenteredTimeAverage_inner_vacuum_eq_zero hP h psi⟩

/-- The derived physical Yang--Mills mass controls the physical semigroup norm
 exponentially on the entire vacuum-orthogonal physical Hilbert sector.

This is the continuous extension of the generator-domain estimate. -/
theorem physicalOperator_norm_le_exp_neg_physicalYangMillsMass_of_inner_vacuum_eq_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (t : NNReal) (psi : P.PhysicalHilbert)
    (horthogonal : inner ℝ psi P.vacuum = 0) :
    ‖T.toPhysicalSemigroup.operator t psi‖ ≤
      ‖psi‖ * Real.exp ((-T.physicalYangMillsMass) * (t : ℝ)) := by
  let core : Set P.PhysicalHilbert :=
    {phi | phi ∈ T.rightGeneratorDomain ∧ inner ℝ phi P.vacuum = 0}
  let decaySet : Set P.PhysicalHilbert :=
    {phi |
      ‖T.toPhysicalSemigroup.operator t phi‖ ≤
        ‖phi‖ * Real.exp ((-T.physicalYangMillsMass) * (t : ℝ))}
  have hpsi : psi ∈ closure core := by
    simpa [core] using
      T.mem_closure_rightGeneratorDomain_inner_vacuum_eq_zero
        hP psi horthogonal
  have hclosed : IsClosed decaySet := by
    dsimp [decaySet]
    exact isClosed_le (by fun_prop) (by fun_prop)
  have hcore : core ⊆ decaySet := by
    intro phi hphi
    change
      ‖T.toPhysicalSemigroup.operator t phi‖ ≤
        ‖phi‖ * Real.exp ((-T.physicalYangMillsMass) * (t : ℝ))
    exact T.physicalOperator_norm_le_exp_neg_physicalYangMillsMass
      hP t ⟨phi, hphi.1⟩ hphi.2
  exact (closure_minimal hcore hclosed) hpsi

/-- Submodule-facing form of full excitation-sector exponential decay. -/
theorem physicalOperator_norm_le_exp_neg_physicalYangMillsMass_of_mem_vacuumOrthogonal
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (t : NNReal) (psi : P.PhysicalHilbert)
    (hpsi : psi ∈ P.vacuumOrthogonal) :
    ‖T.toPhysicalSemigroup.operator t psi‖ ≤
      ‖psi‖ * Real.exp ((-T.physicalYangMillsMass) * (t : ℝ)) := by
  have horthogonal : inner ℝ psi P.vacuum = 0 := by
    have h := (P.mem_vacuumOrthogonal_iff psi).mp hpsi
    simpa [real_inner_comm] using h
  exact T.physicalOperator_norm_le_exp_neg_physicalYangMillsMass_of_inner_vacuum_eq_zero
    hP t psi horthogonal

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
