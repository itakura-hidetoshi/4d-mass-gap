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
  have horth :
      inner ℝ (finiteBoundaryPointVector A)
        (finiteBoundaryPointVector B) = 0 := by
    classical
    rw [PiLp.inner_apply]
    simp [finiteBoundaryPointVector, hAB]
  have hoff :
      0 < inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B) := by
    rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_point_matrixElement]
    exact Real.exp_pos _
  have hscalarMatrix := congrArg
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
  rw [hscalarMatrix, hscalarZero] at hoff
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
  have horth :
      inner ℝ (finiteBoundaryPointVector A)
        (finiteBoundaryPointVector B) = 0 := by
    classical
    rw [PiLp.inner_apply]
    simp [finiteBoundaryPointVector, hAB]
  have hoff :
      0 < inner ℝ
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteBoundaryPointVector A))
        (finiteBoundaryPointVector B) := by
    unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabTransfer
    rw [finiteKernelNormalizedOperator_matrixElement]
    apply mul_pos
    · exact inv_pos.mpr
        (norm_pos_iff.mpr
          (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_ne_zero
            H β energyIdentity energyNontrivial hβ hEnergy))
    · rw [show (∑ x, ∑ y,
          finiteBoundaryPointVector A x *
            (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
              H β energyIdentity energyNontrivial hβ hEnergy).kernel x y *
            finiteBoundaryPointVector B y) =
          (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
            H β energyIdentity energyNontrivial hβ hEnergy).kernel A B by
          classical
          simp [finiteBoundaryPointVector]]
      exact finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_pos
        H β energyIdentity energyNontrivial hβ hEnergy A B
  have hIdMatrix := congrArg
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
  rw [hIdMatrix, hidentityZero] at hoff
  exact (lt_irrefl 0) hoff

end

end MathlibAnalytic
end MGAP4D
