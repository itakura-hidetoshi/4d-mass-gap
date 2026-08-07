import MGAP4D.MathlibAnalytic.FiniteLinearizedGroundLiftedDefectFirstVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Second-order algebraic data at a base point where the normalized transfer
is itself the ground projector.  The inherited first-order identities are those
of Package T.  The new identity is exactly the second derivative of `P² = P`,
written without factorial normalization. -/
structure FiniteSecondOrderLinearizedTransferGroundProjectorData
    (E : Type*) [AddCommGroup E] [Module ℝ E]
    extends FiniteLinearizedTransferGroundProjectorData E where
  transferSecondVariation : E →ₗ[ℝ] E
  groundProjectorSecondVariation : E →ₗ[ℝ] E
  groundProjectorIdempotentSecondVariation :
    ∀ x : E,
      groundProjectorSecondVariation (baseProjector x) +
          (groundProjectorVariation (groundProjectorVariation x) +
            groundProjectorVariation (groundProjectorVariation x)) +
          baseProjector (groundProjectorSecondVariation x) =
        groundProjectorSecondVariation x

namespace FiniteSecondOrderLinearizedTransferGroundProjectorData

variable
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (D : FiniteSecondOrderLinearizedTransferGroundProjectorData E)

/-- Second variation of `D_lift = I - T + P`. -/
def groundLiftedSecondVariation : E →ₗ[ℝ] E :=
  -D.transferSecondVariation + D.groundProjectorSecondVariation

@[simp] theorem groundLiftedSecondVariation_apply (x : E) :
    D.groundLiftedSecondVariation x =
      -D.transferSecondVariation x + D.groundProjectorSecondVariation x :=
  rfl

/-- On beta-zero ground input, the transfer first variation agrees with the
projector first variation. -/
theorem groundProjectorVariation_baseProjector_eq_transferVariation
    (x : E) :
    D.groundProjectorVariation (D.baseProjector x) =
      D.transferVariation (D.baseProjector x) := by
  exact
    (D.toFiniteLinearizedTransferGroundProjectorData
      |>.transferVariation_baseProjector_eq_groundProjectorVariation x).symm

/-- On beta-zero complemented input, the projector first variation is the
ground projection of the transfer first variation. -/
theorem groundProjectorVariation_baseComplement_eq_baseProjector_transferVariation
    (x : E) :
    D.groundProjectorVariation (D.baseComplement x) =
      D.baseProjector (D.transferVariation (D.baseComplement x)) := by
  have hQQ :=
    D.toFiniteLinearizedTransferGroundProjectorData
      |>.baseComplement_groundProjectorVariation_baseComplement_apply x
  rw [FiniteLinearizedTransferGroundProjectorData.baseComplement_apply] at hQQ
  have hP :=
    D.toFiniteLinearizedTransferGroundProjectorData
      |>.baseProjector_transferVariation_eq_groundProjectorVariation
        (D.baseComplement x)
  have hRange :
      D.groundProjectorVariation (D.baseComplement x) =
        D.baseProjector
          (D.groundProjectorVariation (D.baseComplement x)) := by
    exact sub_eq_zero.mp hQQ
  exact hRange.trans hP.symm

/-- A transfer first variation applied to beta-zero ground input lands entirely
in the complementary sector. -/
theorem baseProjector_transferVariation_baseProjector_apply_eq_zero
    (x : E) :
    D.baseProjector (D.transferVariation (D.baseProjector x)) = 0 := by
  rw [D.toFiniteLinearizedTransferGroundProjectorData
    |>.transferVariation_baseProjector_eq_groundProjectorVariation]
  have hP :=
    D.groundProjectorIdempotentFirstVariation (D.baseProjector x)
  rw [D.baseProjector_idempotent] at hP
  exact add_left_cancel (hP.trans (add_zero _).symm)

/-- Hence the complement acts identically on `T₁ P₀`. -/
theorem baseComplement_transferVariation_baseProjector_apply
    (x : E) :
    D.baseComplement (D.transferVariation (D.baseProjector x)) =
      D.transferVariation (D.baseProjector x) := by
  rw [FiniteLinearizedTransferGroundProjectorData.baseComplement_apply,
    D.baseProjector_transferVariation_baseProjector_apply_eq_zero, sub_zero]

/-- Exact second-order projector identity on the beta-zero complementary
sector:

`Q P₂ Q = 2 T₁ P₀ T₁ Q`.

The two equal summands are kept explicit so the statement needs only additive
algebra and no normalization convention for second derivatives. -/
theorem baseComplement_groundProjectorSecondVariation_baseComplement_apply
    (x : E) :
    D.baseComplement
        (D.groundProjectorSecondVariation (D.baseComplement x)) =
      D.transferVariation
          (D.baseProjector (D.transferVariation (D.baseComplement x))) +
        D.transferVariation
          (D.baseProjector (D.transferVariation (D.baseComplement x))) := by
  have hQ :=
    D.toFiniteLinearizedTransferGroundProjectorData
      |>.baseProjector_baseComplement_apply x
  have hSecond := D.groundProjectorIdempotentSecondVariation (D.baseComplement x)
  rw [hQ, map_zero, zero_add] at hSecond
  have hP1Q := D.groundProjectorVariation_baseComplement_eq_baseProjector_transferVariation x
  rw [hP1Q] at hSecond
  rw [D.groundProjectorVariation_baseProjector_eq_transferVariation] at hSecond
  rw [FiniteLinearizedTransferGroundProjectorData.baseComplement_apply]
  apply sub_eq_iff_eq_add.mpr
  exact hSecond.symm

/-- The disconnected first-order ground/excited mixing term appearing in the
second-order ground-lifted expansion. -/
def firstVariationGroundMixing : E →ₗ[ℝ] E :=
  D.transferVariation.comp
    (D.baseProjector.comp
      (D.transferVariation.comp D.baseComplement))

@[simp] theorem firstVariationGroundMixing_apply (x : E) :
    D.firstVariationGroundMixing x =
      D.transferVariation
        (D.baseProjector (D.transferVariation (D.baseComplement x))) :=
  rfl

/-- The first-order mixing term already lands in the beta-zero complementary
sector. -/
theorem baseComplement_firstVariationGroundMixing_apply (x : E) :
    D.baseComplement (D.firstVariationGroundMixing x) =
      D.firstVariationGroundMixing x := by
  rw [D.firstVariationGroundMixing_apply]
  exact D.baseComplement_transferVariation_baseProjector_apply
    (D.transferVariation (D.baseComplement x))

/-- Exact connected second-order reduction:

`Q D₂ Q = - Q T₂ Q + 2 T₁ P₀ T₁ Q`.

Package T showed `Q D₁ Q = -Q T₁ Q`; for the finite Z₂ model that first-order
block vanishes.  At second order, however, the projector correction contributes
the nontrivial disconnected mixing term displayed here. -/
theorem baseComplement_groundLiftedSecondVariation_baseComplement_apply
    (x : E) :
    D.baseComplement (D.groundLiftedSecondVariation (D.baseComplement x)) =
      -D.baseComplement
          (D.transferSecondVariation (D.baseComplement x)) +
        D.firstVariationGroundMixing x +
        D.firstVariationGroundMixing x := by
  rw [D.groundLiftedSecondVariation_apply, map_add, map_neg,
    D.baseComplement_groundProjectorSecondVariation_baseComplement_apply,
    D.firstVariationGroundMixing_apply]
  abel

/-- Operator-level form of the connected second-order reduction. -/
theorem baseComplement_comp_groundLiftedSecondVariation_comp_baseComplement :
    D.baseComplement.comp
        (D.groundLiftedSecondVariation.comp D.baseComplement) =
      -(D.baseComplement.comp
          (D.transferSecondVariation.comp D.baseComplement)) +
        D.firstVariationGroundMixing +
        D.firstVariationGroundMixing := by
  apply LinearMap.ext
  intro x
  change
    D.baseComplement (D.groundLiftedSecondVariation (D.baseComplement x)) =
      -D.baseComplement (D.transferSecondVariation (D.baseComplement x)) +
        D.firstVariationGroundMixing x + D.firstVariationGroundMixing x
  exact D.baseComplement_groundLiftedSecondVariation_baseComplement_apply x

/-- Connected transfer block whose negative is the complemented ground-lifted
second variation. -/
def connectedTransferSecondVariation : E →ₗ[ℝ] E :=
  D.baseComplement.comp
      (D.transferSecondVariation.comp D.baseComplement) -
    D.firstVariationGroundMixing -
    D.firstVariationGroundMixing

/-- `Q D₂ Q` is exactly minus the connected transfer second-variation block. -/
theorem baseComplement_comp_groundLiftedSecondVariation_comp_baseComplement_eq_neg_connected :
    D.baseComplement.comp
        (D.groundLiftedSecondVariation.comp D.baseComplement) =
      -D.connectedTransferSecondVariation := by
  rw [D.baseComplement_comp_groundLiftedSecondVariation_comp_baseComplement]
  unfold connectedTransferSecondVariation
  abel

/-- A nonzero connected second-order block certifies a nonzero complemented
ground-lifted second variation. -/
theorem complementedGroundLiftedSecondVariation_ne_zero_of_connectedTransferSecondVariation_ne_zero
    (h : D.connectedTransferSecondVariation ≠ 0) :
    D.baseComplement.comp
        (D.groundLiftedSecondVariation.comp D.baseComplement) ≠ 0 := by
  rw [D.baseComplement_comp_groundLiftedSecondVariation_comp_baseComplement_eq_neg_connected]
  exact neg_ne_zero.mpr h

/-- Audit-visible generic Package-U receipt. -/
structure FiniteLinearizedGroundLiftedSecondVariationPackage where
  projectorSecondOrder :
    ∀ x : E,
      D.baseComplement
          (D.groundProjectorSecondVariation (D.baseComplement x)) =
        D.firstVariationGroundMixing x + D.firstVariationGroundMixing x
  connectedReduction :
    D.baseComplement.comp
        (D.groundLiftedSecondVariation.comp D.baseComplement) =
      -D.connectedTransferSecondVariation

/-- Construct the generic Package-U second-order receipt. -/
noncomputable def finiteLinearizedGroundLiftedSecondVariationPackage :
    D.FiniteLinearizedGroundLiftedSecondVariationPackage where
  projectorSecondOrder := fun x => by
    rw [D.firstVariationGroundMixing_apply]
    exact D.baseComplement_groundProjectorSecondVariation_baseComplement_apply x
  connectedReduction :=
    D.baseComplement_comp_groundLiftedSecondVariation_comp_baseComplement_eq_neg_connected

end FiniteSecondOrderLinearizedTransferGroundProjectorData

end

end MathlibAnalytic
end MGAP4D
