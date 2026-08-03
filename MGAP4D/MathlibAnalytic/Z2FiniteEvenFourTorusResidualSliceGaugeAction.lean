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
    change finiteEvenFourTorusZ2ResidualSliceGaugeTransform H 1 A = A
    funext e
    change (1 : Z2Gauge) * A e * (1 : Z2Gauge)⁻¹ = A e
    simp
  mul_smul g h A := by
    change
      finiteEvenFourTorusZ2ResidualSliceGaugeTransform H (g * h) A =
        finiteEvenFourTorusZ2ResidualSliceGaugeTransform H g
          (finiteEvenFourTorusZ2ResidualSliceGaugeTransform H h A)
    funext e
    change
      (g e.1 * h e.1) * A e *
          (g (finiteEvenFourTorusSpatialVertexStep H e.1 e.2) *
            h (finiteEvenFourTorusSpatialVertexStep H e.1 e.2))⁻¹ =
        g e.1 *
          (h e.1 * A e *
            (h (finiteEvenFourTorusSpatialVertexStep H e.1 e.2))⁻¹) *
          (g (finiteEvenFourTorusSpatialVertexStep H e.1 e.2))⁻¹
    simp [mul_assoc, mul_comm, mul_left_comm]

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

/-- Algebraic cancellation behind abelian plaquette gauge invariance. -/
theorem commGroupPlaquetteGaugeCancellation
    {G : Type} [CommGroup G]
    (g00 g10 g01 g11 a b c d : G) :
    (g00 * a * g10⁻¹) *
        (g10 * b * g11⁻¹) *
        (g01 * c * g11⁻¹)⁻¹ *
        (g00 * d * g01⁻¹)⁻¹ =
      a * b * c⁻¹ * d⁻¹ := by
  simp [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

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
  simp only [finiteEvenFourTorusZ2ResidualSlice_smul_apply]
  rw [finiteEvenFourTorusSpatialVertexStep_commute H v μ ν]
  exact commGroupPlaquetteGaugeCancellation
    (g v)
    (g (finiteEvenFourTorusSpatialVertexStep H v μ))
    (g (finiteEvenFourTorusSpatialVertexStep H v ν))
    (g (finiteEvenFourTorusSpatialVertexStep H
      (finiteEvenFourTorusSpatialVertexStep H v μ) ν))
    (A (v, μ))
    (A (finiteEvenFourTorusSpatialVertexStep H v μ, ν))
    (A (finiteEvenFourTorusSpatialVertexStep H v ν, μ))
    (A (v, ν))

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

end

end MathlibAnalytic
end MGAP4D
