import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassRealRightSlope
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
# Gronwall decay from the derived physical Yang--Mills mass

The preceding layers identify the real right slope of the squared physical
semigroup orbit and bound it by the variational physical mass:

`D₊ ‖T_t ψ‖² ≤ -2 m_phys ‖T_t ψ‖²`.

This file applies Mathlib's scalar Gronwall theorem directly to that inequality.
No spectral theorem, functional calculus, exact mass value, PVM atom, or new
physical assumption is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The variational physical Yang--Mills mass gives an exponential upper bound
for the squared norm of every vacuum-orthogonal generator-domain orbit. -/
theorem physicalOrbitNormSqReal_le_exp_neg_two_mul_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (t : ℝ) (ht : 0 ≤ t) (psi : T.rightGeneratorDomain)
    (horthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) t ≤
      ‖(psi : P.PhysicalHilbert)‖ ^ 2 *
        Real.exp ((-2 * T.physicalYangMillsMass) * t) := by
  let f : ℝ → ℝ :=
    T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert)
  let f' : ℝ → ℝ := fun x =>
    -2 * inner ℝ
      (T.rightHamiltonian
        ⟨T.toPhysicalSemigroup.operator x.toNNReal
            (psi : P.PhysicalHilbert),
          T.physicalOperator_mem_rightGeneratorDomain
            x.toNNReal psi.property⟩)
      (T.toPhysicalSemigroup.operator x.toNNReal
        (psi : P.PhysicalHilbert))
  have hf : ContinuousOn f (Icc (0 : ℝ) t) := by
    exact (T.physicalOrbitNormSqReal_continuous
      (psi : P.PhysicalHilbert)).continuousOn
  have hf' :
      ∀ x ∈ Ico (0 : ℝ) t, ∀ r, f' x < r →
        ∃ᶠ z in 𝓝[>] x,
          (z - x)⁻¹ * (f z - f x) < r := by
    intro x hx r hr
    have hslope :=
      T.physicalOrbitNormSqReal_rightSlope_tendsto_mass_decay_upper
        hP x hx.1 psi horthogonal
    have heventually :
        ∀ᶠ z in 𝓝[>] x,
          (z - x)⁻¹ * (f z - f x) < r := by
      apply hslope.1.eventually
      simpa [f'] using (eventually_lt_nhds hr)
    exact heventually.frequently
  have hbound :
      ∀ x ∈ Ico (0 : ℝ) t,
        f' x ≤ (-2 * T.physicalYangMillsMass) * f x + 0 := by
    intro x hx
    have hslope :=
      T.physicalOrbitNormSqReal_rightSlope_tendsto_mass_decay_upper
        hP x hx.1 psi horthogonal
    simpa [f, f'] using hslope.2
  have hG :=
    le_gronwallBound_of_liminf_deriv_right_le
      (f := f) (f' := f')
      (δ := f 0) (K := -2 * T.physicalYangMillsMass)
      (ε := 0) (a := 0) (b := t)
      hf hf' (le_rfl) hbound t ⟨ht, le_rfl⟩
  simpa [f, physicalOrbitNormSqReal, gronwallBound_ε0,
    T.toPhysicalSemigroup.operator_zero] using hG

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
