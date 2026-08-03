import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalGaugeOneSlabTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

/-- A concrete one-link excitation of a spatial slice configuration. -/
def finiteEvenFourTorusZ2SingleLinkExcitation
    (H : ℕ)
    (e₀ : FiniteEvenFourTorusSpatialLink H) :
    FiniteEvenFourTorusZ2SliceConfiguration H :=
  fun e => if e = e₀ then z2GaugeNontrivial else 1

/-- The constant identity spatial slice. -/
def finiteEvenFourTorusZ2IdentitySlice
    (H : ℕ) : FiniteEvenFourTorusZ2SliceConfiguration H :=
  fun _ => 1

/-- At a distinguished link, the identity slice and the single-link excitation
have nontrivial relative temporal plaquette holonomy. -/
theorem finiteEvenFourTorusZ2SingleLinkExcitation_relative_nontrivial
    (H : ℕ)
    (e₀ : FiniteEvenFourTorusSpatialLink H) :
    ((finiteEvenFourTorusZ2IdentitySlice H e₀)⁻¹ *
      finiteEvenFourTorusZ2SingleLinkExcitation H e₀ e₀) =
        z2GaugeNontrivial := by
  simp [finiteEvenFourTorusZ2IdentitySlice,
    finiteEvenFourTorusZ2SingleLinkExcitation]

/-- The local temporal factor distinguishes an identity crossing from a
single-link nontrivial crossing whenever the two plaquette energies differ and
`β ≠ 0`. -/
theorem finiteEvenFourTorusZ2TemporalLinkWeight_ne_of_energy_ne
    (β energyIdentity energyNontrivial : ℝ)
    (_hβ : 0 ≤ β)
    (_hEnergy : energyIdentity ≤ energyNontrivial)
    (hβ0 : β ≠ 0)
    (hE : energyIdentity ≠ energyNontrivial) :
    Real.exp (-β * energyIdentity) ≠
      Real.exp (-β * energyNontrivial) := by
  intro h
  have hexp := Real.exp_injective h
  apply hE
  apply mul_left_cancel₀ hβ0
  linarith

/-- Distinct finite boundary point states are orthogonal. -/
theorem finiteEvenFourTorusZ2BoundaryPointVector_inner_eq_zero_of_ne
    (H : ℕ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAB : A ≠ B) :
    inner ℝ (finiteBoundaryPointVector A)
      (finiteBoundaryPointVector B) = 0 := by
  classical
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro X _hX
  rw [finiteBoundaryPointVector_apply, finiteBoundaryPointVector_apply]
  by_cases hXA : X = A
  · subst X
    simp [hAB]
  · simp [hXA]

/-- Exact point-state criterion showing that the raw one-slab transfer is not a
scalar multiple of the identity: every off-diagonal kernel entry is strictly
positive. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_not_scalar_identity
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAB : A ≠ B) :
    ∀ c : ℝ,
      finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy ≠
        c • (1 : FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
          FiniteEvenFourTorusZ2SliceHilbert H) := by
  intro c hscalar
  have horth :=
    finiteEvenFourTorusZ2BoundaryPointVector_inner_eq_zero_of_ne H A B hAB
  have hoff :
      0 < inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B) := by
    rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_point_matrixElement]
    exact Real.exp_pos _
  have hscalarMatrix :
      inner ℝ
          (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
            H β energyIdentity energyNontrivial hβ hEnergy
            (finiteBoundaryPointVector A))
          (finiteBoundaryPointVector B) =
        inner ℝ
          ((c • (1 : FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
            FiniteEvenFourTorusZ2SliceHilbert H))
            (finiteBoundaryPointVector A))
          (finiteBoundaryPointVector B) := by
    exact congrArg
      (fun T : FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
          FiniteEvenFourTorusZ2SliceHilbert H =>
        inner ℝ (T (finiteBoundaryPointVector A))
          (finiteBoundaryPointVector B)) hscalar
  have hscalarZero :
      inner ℝ
        ((c • (1 : FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
          FiniteEvenFourTorusZ2SliceHilbert H))
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B) = 0 := by
    change inner ℝ (c • finiteBoundaryPointVector A)
      (finiteBoundaryPointVector B) = 0
    rw [real_inner_smul_left, horth, mul_zero]
  have hrawZero :
      inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B) = 0 :=
    hscalarMatrix.trans hscalarZero
  rw [hrawZero] at hoff
  exact (lt_irrefl 0) hoff

/-- The normalized actual one-slab transfer is nonidentity whenever the spatial
slice carrier contains two distinct configurations. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer_ne_identity
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAB : A ≠ B) :
    finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 1 := by
  intro hId
  have horth :=
    finiteEvenFourTorusZ2BoundaryPointVector_inner_eq_zero_of_ne H A B hAB
  have hoff :
      0 < inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B) := by
    unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
      finiteKernelNormalizedOperator
    rw [ContinuousLinearMap.smul_apply, real_inner_smul_left]
    apply mul_pos
    · exact inv_pos.mpr
        (norm_pos_iff.mpr
          (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
            H β energyIdentity energyNontrivial hβ hEnergy))
    · rw [finiteKernelOperator_point_matrixElement,
        finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann]
      exact Real.exp_pos _
  have hIdMatrix :
      inner ℝ
          (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
            H β energyIdentity energyNontrivial hβ hEnergy
            (finiteBoundaryPointVector A))
          (finiteBoundaryPointVector B) =
        inner ℝ
          ((1 : FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
            FiniteEvenFourTorusZ2SliceHilbert H)
            (finiteBoundaryPointVector A))
          (finiteBoundaryPointVector B) := by
    exact congrArg
      (fun T : FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
          FiniteEvenFourTorusZ2SliceHilbert H =>
        inner ℝ (T (finiteBoundaryPointVector A))
          (finiteBoundaryPointVector B)) hId
  have hidentityZero :
      inner ℝ
        ((1 : FiniteEvenFourTorusZ2SliceHilbert H →L[ℝ]
          FiniteEvenFourTorusZ2SliceHilbert H)
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B) = 0 := by
    change inner ℝ (finiteBoundaryPointVector A)
      (finiteBoundaryPointVector B) = 0
    exact horth
  have hnormalizedZero :
      inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B) = 0 :=
    hIdMatrix.trans hidentityZero
  rw [hnormalizedZero] at hoff
  exact (lt_irrefl 0) hoff

end

end MathlibAnalytic
end MGAP4D
