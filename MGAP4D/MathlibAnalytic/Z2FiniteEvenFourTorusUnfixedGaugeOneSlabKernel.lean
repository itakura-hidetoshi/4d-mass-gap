import MGAP4D.MathlibAnalytic.FiniteGroupInvariantKernelRightAverage
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeTemporalLinks
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact normalized finite sum over all temporal-link fields in one slab. -/
def finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2SliceConfiguration H → ℝ :=
  fun A B =>
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        Real.exp (-β *
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
            H β energyIdentity energyNontrivial U A B)

@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B =
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          Real.exp (-β *
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
              H β energyIdentity energyNontrivial U A B) :=
  rfl

/-- Temporal-link summation is exactly right-boundary residual-gauge averaging
of the temporal-gauge one-slab kernel. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B =
      finiteGroupRightAveragedKernel
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
          H β energyIdentity energyNontrivial hβ hEnergy).kernel A B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
    finiteGroupRightAveragedKernel
  congr 1
  apply Finset.sum_congr rfl
  intro U _hU
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_temporalGauge_smul]
  exact
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann
      H β energyIdentity energyNontrivial hβ hEnergy A (U • B)).symm

/-- The temporal-link averaged kernel is separately gauge invariant on its
upper boundary. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_right_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A (g • B) =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage]
  exact finiteGroupRightAveragedKernel_right_invariant
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel g A B

/-- The exact unfixed-gauge one-slab kernel is symmetric. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_symmetric
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy B A := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage]
  exact finiteGroupRightAveragedKernel_symmetric
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
    (fun X Y => finite_os_reflection_kernel_symmetric
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        H β energyIdentity energyNontrivial hβ hEnergy).toCertificate X Y)
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy) A B

/-- Symmetry and right invariance imply separate gauge invariance on the lower
boundary as well. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_left_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy (g • A) B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B := by
  calc
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy (g • A) B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy B (g • A) :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_symmetric
        H β energyIdentity energyNontrivial hβ hEnergy _ _
    _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy B A :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_right_invariant
        H β energyIdentity energyNontrivial hβ hEnergy g B A
    _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B :=
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_symmetric
        H β energyIdentity energyNontrivial hβ hEnergy B A

/-- Every entry of the finite temporal-link averaged kernel is strictly
positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy A B := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
  have hcardNat :
      0 < Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hcardReal :
      0 < (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ) := by
    exact_mod_cast hcardNat
  apply mul_pos (inv_pos.mpr hcardReal)
  apply Finset.sum_pos
  · intro U _hU
    exact (Real.exp_pos _).le
  · refine ⟨(1 : FiniteEvenFourTorusZ2TemporalLinkField H),
      Finset.mem_univ _, ?_⟩
    exact Real.exp_pos _

/-- Exact proposition collected by the finite temporal-link summation kernel
package. -/
def finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelClaimBoundary
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  (∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B =
      finiteGroupRightAveragedKernel
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
          H β energyIdentity energyNontrivial hβ hEnergy).kernel A B) ∧
  (∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy B A) ∧
  (∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
    ∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy (g • A) B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B) ∧
  (∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
    ∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A (g • B) =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy A B) ∧
  (∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
    0 < finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy A B)

/-- Public exact-kernel receipt for finite temporal-link summation. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelClaimBoundary
      H β energyIdentity energyNontrivial hβ hEnergy := by
  exact ⟨
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_symmetric
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_left_invariant
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_right_invariant
      H β energyIdentity energyNontrivial hβ hEnergy,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
      H β energyIdentity energyNontrivial hβ hEnergy⟩

end

end MathlibAnalytic
end MGAP4D
