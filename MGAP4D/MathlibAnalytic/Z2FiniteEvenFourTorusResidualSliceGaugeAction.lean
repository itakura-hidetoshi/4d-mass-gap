import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusSpatialSlice
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Residual time-independent vertex gauge group on the canonical spatial
slice. -/
abbrev FiniteEvenFourTorusZ2ResidualSliceGaugeGroup (H : ℕ) : Type :=
  FiniteEvenFourTorusSpatialVertex H → Z2Gauge

/-- Residual gauge transformation of a spatial-link boundary configuration. -/
def finiteEvenFourTorusZ2ResidualSliceGaugeTransform
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteEvenFourTorusZ2SliceConfiguration H :=
  fun e =>
    g e.1 * A e *
      (g (finiteEvenFourTorusSpatialVertexStep H e.1 e.2))⁻¹

@[simp] theorem finiteEvenFourTorusZ2ResidualSliceGaugeTransform_apply
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2ResidualSliceGaugeTransform H g A e =
      g e.1 * A e *
        (g (finiteEvenFourTorusSpatialVertexStep H e.1 e.2))⁻¹ :=
  rfl

/-- The residual gauge formula is a genuine multiplicative group action. -/
instance finiteEvenFourTorusZ2ResidualSliceMulAction (H : ℕ) :
    MulAction (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) where
  smul := finiteEvenFourTorusZ2ResidualSliceGaugeTransform H
  one_smul A := by
    funext e
    simp [finiteEvenFourTorusZ2ResidualSliceGaugeTransform]
  mul_smul g h A := by
    funext e
    simp [finiteEvenFourTorusZ2ResidualSliceGaugeTransform, mul_assoc]

@[simp] theorem finiteEvenFourTorusZ2ResidualSlice_smul_apply
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    (g • A) e =
      g e.1 * A e *
        (g (finiteEvenFourTorusSpatialVertexStep H e.1 e.2))⁻¹ :=
  rfl

/-- Spatial unit translations commute on the abelian torus. -/
theorem finiteEvenFourTorusSpatialVertexStep_commute
    (H : ℕ)
    (v : FiniteEvenFourTorusSpatialVertex H)
    (μ ν : FiniteEvenFourTorusSpatialDirection) :
    finiteEvenFourTorusSpatialVertexStep H
        (finiteEvenFourTorusSpatialVertexStep H v μ) ν =
      finiteEvenFourTorusSpatialVertexStep H
        (finiteEvenFourTorusSpatialVertexStep H v ν) μ := by
  apply Subtype.ext
  change
    (v.1 + finiteFourTorusUnitStep (2 * H + 1) μ.1) +
        finiteFourTorusUnitStep (2 * H + 1) ν.1 =
      (v.1 + finiteFourTorusUnitStep (2 * H + 1) ν.1) +
        finiteFourTorusUnitStep (2 * H + 1) μ.1
  abel

/-- Spatial plaquette holonomy is invariant under residual slice gauge
transformations. -/
theorem finiteEvenFourTorusZ2SpatialPlaquetteHolonomy_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (p : FiniteEvenFourTorusSpatialPlaquette H) :
    finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H (g • A) p =
      finiteEvenFourTorusZ2SpatialPlaquetteHolonomy H A p := by
  rcases p with ⟨v, ⟨⟨μ, ν⟩, hμν⟩⟩
  unfold finiteEvenFourTorusZ2SpatialPlaquetteHolonomy
  dsimp only
  rw [finiteEvenFourTorusSpatialVertexStep_commute H v μ ν]
  simp [finiteEvenFourTorusZ2ResidualSliceGaugeTransform,
    mul_assoc, mul_comm, mul_left_comm]

/-- The complete spatial Wilson action is residual-gauge invariant. -/
theorem finiteEvenFourTorusZ2SpatialWilsonAction_smul
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial (g • A) =
      finiteEvenFourTorusZ2SpatialWilsonAction
        H energyIdentity energyNontrivial A := by
  unfold finiteEvenFourTorusZ2SpatialWilsonAction
  apply Finset.sum_congr rfl
  intro p _hp
  rw [finiteEvenFourTorusZ2SpatialPlaquetteHolonomy_smul]

/-- Spatial half-Boltzmann amplitudes descend to residual gauge orbits. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeight_smul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial (g • A) =
      finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial A := by
  unfold finiteEvenFourTorusZ2SpatialHalfWeight
  rw [finiteEvenFourTorusZ2SpatialWilsonAction_smul]

/-- On the one-site spatial torus every residual gauge transformation acts
trivially on spatial links.  This supplies a completely explicit invariant
sector used later for a nontriviality witness. -/
theorem finiteEvenFourTorusZ2ResidualSlice_smul_zero
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup 0)
    (A : FiniteEvenFourTorusZ2SliceConfiguration 0) :
    g • A = A := by
  funext e
  rcases e with ⟨v, μ⟩
  have hstep : finiteEvenFourTorusSpatialVertexStep 0 v μ = v := by
    apply Subtype.ext
    funext i
    exact Subsingleton.elim _ _
  simp [finiteEvenFourTorusZ2ResidualSliceGaugeTransform, hstep,
    mul_assoc, mul_comm, mul_left_comm]

end

end MathlibAnalytic
end MGAP4D
