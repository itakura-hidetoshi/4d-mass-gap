import MGAP4D.MathlibAnalytic.FiniteContinuousKernelOperatorPerronEigenvalue
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeOneSlabTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The finite unfixed-gauge one-slab action uses the coupling only in the
outer Boltzmann multiplier, not in the finite energy value itself. -/
@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_zeroCoupling
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (U : FiniteEvenFourTorusZ2TemporalLinkField H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H β energyIdentity energyNontrivial U A B =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H 0 energyIdentity energyNontrivial U A B := by
  rfl

/-- Proof-independent coupling family underlying the actual one-slab kernel.
It is defined on all real couplings; the physical nonnegative-coupling kernel
is its exact restriction. -/
def finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ) :
    FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2SliceConfiguration H → ℝ :=
  fun A B =>
    (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        Real.exp (-β *
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
            H β energyIdentity energyNontrivial U A B)

/-- The proof-independent coupling family is definitionally the actual kernel
whenever the physical proof arguments are supplied. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily_eq_actual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
        H energyIdentity energyNontrivial β =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rfl

/-- Every matrix entry of the actual proof-independent one-slab kernel family
is continuous in the coupling. -/
theorem continuous_finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Continuous (fun β : ℝ =>
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
        H energyIdentity energyNontrivial β A B) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
  apply continuous_const.mul
  apply continuous_finset_sum
  intro U _hU
  have hLinear : Continuous (fun β : ℝ =>
      -β * finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction
        H 0 energyIdentity energyNontrivial U A B) :=
    continuous_id.neg.mul continuous_const
  simpa only [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_zeroCoupling] using
    Real.continuous_exp.comp hLinear

/-- The proof-independent kernel family remains strictly positive for every
real coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily_pos
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β A B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
  have hcardNat :
      0 < Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hcardReal :
      0 < (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ) := by
    exact_mod_cast hcardNat
  apply mul_pos (inv_pos.mpr hcardReal)
  apply Finset.sum_pos
  · intro U _hU
    exact Real.exp_pos _
  · exact ⟨1, Finset.mem_univ _⟩

/-- The raw transfer of the proof-independent kernel family is nonzero at
every real coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily_raw_ne_zero
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ) :
    finiteKernelOperator
      (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
        H energyIdentity energyNontrivial β) ≠ 0 := by
  let A : FiniteEvenFourTorusZ2SliceConfiguration H := fun _ => 1
  apply finiteKernelOperator_ne_zero_of_diagonal_ne_zero
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β) A
  exact ne_of_gt
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily_pos
      H energyIdentity energyNontrivial β A A)

/-- The actual raw Perron normalization scalar is continuous as a function of
coupling. -/
theorem continuous_finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawPerronValue
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    Continuous (fun β : ℝ =>
      ‖finiteKernelOperator
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
          H energyIdentity energyNontrivial β)‖) := by
  apply continuous_finiteKernelOperator_norm
  intro A B
  exact
    continuous_finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial A B

/-- The normalized actual one-slab transfer has a proof-independent continuous
extension to all real couplings. -/
theorem continuous_finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransferCouplingFamily
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ) :
    Continuous (fun β : ℝ =>
      finiteKernelNormalizedOperator
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
          H energyIdentity energyNontrivial β)) := by
  apply continuous_finiteKernelNormalizedOperator
  · intro A B
    exact
      continuous_finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
        H energyIdentity energyNontrivial A B
  · intro β
    exact
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily_raw_ne_zero
        H energyIdentity energyNontrivial β

/-- On the physical nonnegative domain, the continuous coupling-family
transfer is exactly the repository's actual normalized one-slab transfer. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransferCouplingFamily_eq_actual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteKernelNormalizedOperator
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
          H energyIdentity energyNontrivial β) =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rfl

end

end MathlibAnalytic
end MGAP4D
