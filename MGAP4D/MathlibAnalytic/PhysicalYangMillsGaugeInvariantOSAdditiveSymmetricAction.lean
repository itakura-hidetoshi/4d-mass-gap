import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositiveTimeContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

/-- An additive action on an OS carrier whose translations are symmetric for
its real OS inner product.  No boundedness or contraction hypothesis is built
into this structure.

This is the algebraic level needed for discrete geometric Euclidean time:
symmetry plus the additive law already turns the square norm at one step into
a two-step Rayleigh matrix coefficient. -/
structure AdditiveSymmetricAction
    (I : Type*) [AddMonoid I] (P : D.OSPreHilbertData) where
  translate : I → P.Carrier →ₗ[ℝ] P.Carrier
  translate_zero : ∀ F, translate 0 F = F
  translate_add : ∀ s t F,
    translate (s + t) F = translate s (translate t F)
  inner_symmetric : ∀ i F G,
    inner ℝ (translate i F) G = inner ℝ F (translate i G)

namespace AdditiveSymmetricAction

variable {I : Type*} [AddMonoid I]

/-- For a symmetric additive action, the squared norm after one index `i` is
exactly the two-step Rayleigh coefficient at `i+i`.

This is the discrete OS identity
`‖T_i F‖² = ⟪F, T_{2i} F⟫`, derived without assuming that `T_i` is bounded. -/
theorem norm_translate_sq_eq_inner_double
    (A : P.AdditiveSymmetricAction I) (i : I) (F : P.Carrier) :
    ‖A.translate i F‖ ^ 2 =
      inner ℝ F (A.translate (i + i) F) := by
  rw [← real_inner_self_eq_norm_sq]
  calc
    inner ℝ (A.translate i F) (A.translate i F) =
        inner ℝ F (A.translate i (A.translate i F)) :=
      A.inner_symmetric i F (A.translate i F)
    _ = inner ℝ F (A.translate (i + i) F) := by
      rw [A.translate_add]

/-- A norm contraction by a nonnegative factor `r` is equivalent to the
Poincaré/Dirichlet defect inequality for the doubled additive step.

The equivalence is purely Hilbertian:

`‖T_i F‖ ≤ r ‖F‖`

iff

`(1-r²) ‖F‖² ≤ ⟪F,F⟫ - ⟪F,T_{2i}F⟫`.

Thus a strict transfer estimate may be attacked as a Rayleigh lower bound for
the geometric defect `I - T_{2i}` rather than as a norm estimate. -/
theorem norm_translate_le_iff_dirichlet_defect
    (A : P.AdditiveSymmetricAction I)
    (i : I) (r : ℝ) (hr : 0 ≤ r) (F : P.Carrier) :
    ‖A.translate i F‖ ≤ r * ‖F‖ ↔
      (1 - r ^ 2) * ‖F‖ ^ 2 ≤
        inner ℝ F F - inner ℝ F (A.translate (i + i) F) := by
  have hdouble := A.norm_translate_sq_eq_inner_double i F
  have hself : inner ℝ F F = ‖F‖ ^ 2 :=
    real_inner_self_eq_norm_sq F
  constructor
  · intro h
    have hsq :
        ‖A.translate i F‖ ^ 2 ≤ (r * ‖F‖) ^ 2 := by
      nlinarith [norm_nonneg (A.translate i F),
        mul_nonneg hr (norm_nonneg F)]
    rw [hdouble] at hsq
    rw [hself]
    nlinarith
  · intro h
    rw [hself] at h
    rw [← hdouble] at h
    have hsq :
        ‖A.translate i F‖ ^ 2 ≤ (r * ‖F‖) ^ 2 := by
      nlinarith
    nlinarith [norm_nonneg (A.translate i F),
      mul_nonneg hr (norm_nonneg F)]

end AdditiveSymmetricAction
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D