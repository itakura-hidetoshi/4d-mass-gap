import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassRealRightSlope
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic

/-!
# Gronwall decay from the derived physical Yang--Mills mass

The preceding layer supplies, on the canonical right-generator domain and in the
vacuum-orthogonal sector, a real right-neighborhood slope whose limit is bounded
above by

`-2 * physicalYangMillsMass * ‖T_t psi‖²`.

This file applies Mathlib's scalar
`le_gronwallBound_of_liminf_deriv_right_le` directly.  The coefficient
`K = -2 * physicalYangMillsMass` is allowed to have either sign by the scalar
Mathlib theorem, so no extra positivity hypothesis is inserted here.

The resulting estimate is the squared-norm semigroup decay

`‖T_t psi‖² ≤ ‖psi‖² * exp (-2 * physicalYangMillsMass * t)`

for vacuum-orthogonal states in the canonical right-generator domain.

No spectral theorem, functional-calculus identity `T_t = exp (-t H)`, exact
numerical mass value, PVM atom, or new physical assumption is introduced.
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

/-- The Hamiltonian right-slope rate used in the scalar Gronwall argument. -/
def physicalOrbitNormSqRealHamiltonianRate
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) (x : ℝ) : ℝ :=
  -2 * inner ℝ
    (T.rightHamiltonian
      ⟨T.toPhysicalSemigroup.operator x.toNNReal
          (psi : P.PhysicalHilbert),
        T.physicalOperator_mem_rightGeneratorDomain x.toNNReal psi.property⟩)
    (T.toPhysicalSemigroup.operator x.toNNReal
      (psi : P.PhysicalHilbert))

/-- The real right slope converges to the Hamiltonian rate. -/
theorem physicalOrbitNormSqReal_rightSlope_tendsto_hamiltonianRate
    (T : P.StronglyContinuousPhysicalSemigroup)
    (x : ℝ) (hx : 0 ≤ x) (psi : T.rightGeneratorDomain) :
    Tendsto
      (fun z : ℝ =>
        (z - x)⁻¹ *
          (T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) z -
            T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) x))
      (nhdsWithin x (Ioi x))
      (nhds (T.physicalOrbitNormSqRealHamiltonianRate psi x)) := by
  simpa [physicalOrbitNormSqRealHamiltonianRate] using
    T.physicalOrbitNormSqReal_rightSlope_tendsto_rightHamiltonian x hx psi

/-- The Hamiltonian right-slope rate is bounded by the derived mass times the
current squared orbit norm. -/
theorem physicalOrbitNormSqRealHamiltonianRate_le_mass_decay
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (x : ℝ) (hx : 0 ≤ x) (psi : T.rightGeneratorDomain)
    (horthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    T.physicalOrbitNormSqRealHamiltonianRate psi x ≤
      (-2 * T.physicalYangMillsMass) *
        T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) x := by
  have h :=
    T.physicalOrbitNormSqReal_rightSlope_tendsto_mass_decay_upper
      hP x hx psi horthogonal
  simpa [physicalOrbitNormSqRealHamiltonianRate, mul_assoc] using h.2

/-- Mathlib Gronwall turns the derived-mass right-slope inequality into
exponential squared-norm decay on the canonical generator domain. -/
theorem physicalOperator_norm_sq_le_exp_neg_two_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (t : NNReal) (psi : T.rightGeneratorDomain)
    (horthogonal :
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    ‖T.toPhysicalSemigroup.operator t
        (psi : P.PhysicalHilbert)‖ ^ 2 ≤
      ‖(psi : P.PhysicalHilbert)‖ ^ 2 *
        Real.exp ((-2 * T.physicalYangMillsMass) * (t : ℝ)) := by
  let f : ℝ → ℝ :=
    T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert)
  let f' : ℝ → ℝ :=
    T.physicalOrbitNormSqRealHamiltonianRate psi
  have hf : ContinuousOn f (Icc (0 : ℝ) (t : ℝ)) := by
    exact (T.physicalOrbitNormSqReal_continuous
      (psi : P.PhysicalHilbert)).continuousOn
  have hf' :
      ∀ x ∈ Ico (0 : ℝ) (t : ℝ), ∀ r, f' x < r →
        ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r := by
    intro x hx r hr
    have hlim :=
      T.physicalOrbitNormSqReal_rightSlope_tendsto_hamiltonianRate
        x hx.1 psi
    have hev :
        ∀ᶠ z in 𝓝[>] x,
          (z - x)⁻¹ *
            (T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) z -
              T.physicalOrbitNormSqReal (psi : P.PhysicalHilbert) x) < r :=
      hlim.eventually (Iio_mem_nhds hr)
    have hfreq := hev.frequently
    simpa [f, f'] using hfreq
  have ha : f 0 ≤ ‖(psi : P.PhysicalHilbert)‖ ^ 2 := by
    simp [f, physicalOrbitNormSqReal,
      T.toPhysicalSemigroup.operator_zero]
  have hbound :
      ∀ x ∈ Ico (0 : ℝ) (t : ℝ),
        f' x ≤ (-2 * T.physicalYangMillsMass) * f x + 0 := by
    intro x hx
    have hmass :=
      T.physicalOrbitNormSqRealHamiltonianRate_le_mass_decay
        hP x hx.1 psi horthogonal
    simpa [f, f'] using hmass
  have hgronwall :=
    le_gronwallBound_of_liminf_deriv_right_le
      (f := f) (f' := f')
      (δ := ‖(psi : P.PhysicalHilbert)‖ ^ 2)
      (K := -2 * T.physicalYangMillsMass) (ε := 0)
      (a := 0) (b := (t : ℝ))
      hf hf' ha hbound
  have htmem : (t : ℝ) ∈ Icc (0 : ℝ) (t : ℝ) :=
    ⟨t.coe_nonneg, le_rfl⟩
  have ht := hgronwall (t : ℝ) htmem
  simpa [f, physicalOrbitNormSqReal, gronwallBound_ε0] using ht

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
