import MGAP4D.MathlibAnalytic.FiniteBoltzmannWeightedProjectiveFirstVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeOneSlabKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite one-slab action carries a syntactic beta argument, but the
crossing-action definition does not use it.  Hence the energy entering the
Boltzmann factor is exactly beta-independent. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_beta_independent
    (H : ℕ)
    (β γ energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H β energyIdentity energyNontrivial U A B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H γ energyIdentity energyNontrivial U A B := by
  rfl

/-- Proof-free analytic extension of the exact temporal-link averaged one-slab
kernel to every real beta.  The action is frozen at beta zero, which is exact
because the action itself is beta-independent. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (β : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteBoltzmannWeightedProfile
    ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹)
    (fun U : FiniteEvenFourTorusZ2TemporalLinkField H =>
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H 0 energyIdentity energyNontrivial U A B)
    (fun _ => 1)
    β

/-- On the physical nonnegative-beta lane, the analytic extension agrees
exactly with the existing proof-parameterized one-slab kernel. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_eq_kernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
        H energyIdentity energyNontrivial β A B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
    finiteBoltzmannWeightedProfile finiteBoltzmannWeightedSum
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro U _hU
  simp only [mul_one]
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_beta_independent
    H 0 β energyIdentity energyNontrivial U A B]
  congr 1
  ring

/-- Exact beta-zero first variation of the proof-free one-slab kernel: the
uniform temporal-link average of minus the one-slab action. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_hasDerivAt_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    HasDerivAt
      (fun β : ℝ =>
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
          H energyIdentity energyNontrivial β A B)
      ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          -finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
            H 0 energyIdentity energyNontrivial U A B)
      0 := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
  simpa using
    (finiteBoltzmannWeightedProfile_hasDerivAt_zero
      ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹)
      (fun U : FiniteEvenFourTorusZ2TemporalLinkField H =>
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
          H 0 energyIdentity energyNontrivial U A B)
      (fun _ => (1 : ℝ)))

@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
        H energyIdentity energyNontrivial 0 A B = 1 := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalytic
  rw [finiteBoltzmannWeightedProfile_zero]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard :
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) ≠ 0)
  field_simp

end

end MathlibAnalytic
end MGAP4D