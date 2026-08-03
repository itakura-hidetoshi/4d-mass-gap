import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusResidualSliceGaugeAction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusTemporalGaugeOneSlabKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The temporal-gauge relative link variable is invariant when the same
residual gauge transformation is applied to both boundary slices. -/
theorem finiteEvenFourTorusZ2TemporalRelativeLink_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    ((g • A) e)⁻¹ * (g • B) e = (A e)⁻¹ * B e := by
  simp [finiteEvenFourTorusZ2ResidualSliceGaugeTransform,
    mul_assoc, mul_comm, mul_left_comm]
  calc
    g e.1 * (B e * ((g e.1)⁻¹ * (A e)⁻¹)) =
        (g e.1 * (g e.1)⁻¹) * (B e * (A e)⁻¹) := by
      ac_rfl
    _ = B e * (A e)⁻¹ := by
      simp

/-- The complete temporal crossing action is simultaneously residual-gauge
invariant. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingAction_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction
        H β energyIdentity energyNontrivial (g • A) (g • B) =
      finiteEvenFourTorusZ2TemporalGaugeCrossingAction
        H β energyIdentity energyNontrivial A B := by
  unfold finiteEvenFourTorusZ2TemporalGaugeCrossingAction
  simp_rw [finiteEvenFourTorusZ2TemporalRelativeLink_smul]

/-- The symmetric full one-slab Wilson action is invariant under the diagonal
residual gauge action on its two boundaries. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabAction_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
        H β energyIdentity energyNontrivial (g • A) (g • B) =
      finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
        H β energyIdentity energyNontrivial A B := by
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
  rw [finiteEvenFourTorusZ2SpatialWilsonAction_smul,
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction_smul,
    finiteEvenFourTorusZ2SpatialWilsonAction_smul]

/-- The actual temporal-gauge one-slab Gram kernel descends to simultaneous
residual gauge orbits. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
        (g • A) (g • B) =
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        H β energyIdentity energyNontrivial hβ hEnergy).kernel A B := by
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann,
    finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann,
    finiteEvenFourTorusZ2TemporalGaugeOneSlabAction_smul]

/-- Public receipt for the residual gauge invariance of the actual one-slab
Wilson kernel. -/
theorem finiteEvenFourTorusZ2ResidualGaugeOneSlabKernelInvariantPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    (∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
      ∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial (g • A) =
        finiteEvenFourTorusZ2SpatialWilsonAction
          H energyIdentity energyNontrivial A) ∧
    (∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
      ∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2TemporalGaugeCrossingAction
          H β energyIdentity energyNontrivial (g • A) (g • B) =
        finiteEvenFourTorusZ2TemporalGaugeCrossingAction
          H β energyIdentity energyNontrivial A B) ∧
    (∀ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
      ∀ A B : FiniteEvenFourTorusZ2SliceConfiguration H,
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        H β energyIdentity energyNontrivial hβ hEnergy).kernel
          (g • A) (g • B) =
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
          H β energyIdentity energyNontrivial hβ hEnergy).kernel A B) := by
  exact ⟨
    fun g A _B =>
      finiteEvenFourTorusZ2SpatialWilsonAction_smul
        H energyIdentity energyNontrivial g A,
    finiteEvenFourTorusZ2TemporalGaugeCrossingAction_smul
      H β energyIdentity energyNontrivial,
    finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
      H β energyIdentity energyNontrivial hβ hEnergy⟩

end

end MathlibAnalytic
end MGAP4D
