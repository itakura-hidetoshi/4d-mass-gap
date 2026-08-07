import MGAP4D.MathlibAnalytic.FiniteDimensionalSymmetricPositiveContractionGroundLiftedDefectDecomposition
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Algebraic first-variation data at a base point where the normalized transfer
is itself the ground projector.

The three displayed first-order identities are exactly the linearizations of
`P² = P`, `T P = P`, and `P T = P` at a point with `T₀ = P₀ = P`.
Keeping them as algebraic data avoids differentiating a spectral projector or an
operator norm before those analytic facts have been established. -/
structure FiniteLinearizedTransferGroundProjectorData
    (E : Type*) [AddCommGroup E] [Module ℝ E] where
  baseProjector : E →ₗ[ℝ] E
  transferVariation : E →ₗ[ℝ] E
  groundProjectorVariation : E →ₗ[ℝ] E
  baseProjector_idempotent :
    ∀ x : E, baseProjector (baseProjector x) = baseProjector x
  groundProjectorIdempotentFirstVariation :
    ∀ x : E,
      groundProjectorVariation (baseProjector x) +
          baseProjector (groundProjectorVariation x) =
        groundProjectorVariation x
  transferGroundProjectorFirstVariation :
    ∀ x : E,
      transferVariation (baseProjector x) +
          baseProjector (groundProjectorVariation x) =
        groundProjectorVariation x
  groundProjectorTransferFirstVariation :
    ∀ x : E,
      groundProjectorVariation (baseProjector x) +
          baseProjector (transferVariation x) =
        groundProjectorVariation x

namespace FiniteLinearizedTransferGroundProjectorData

variable
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (D : FiniteLinearizedTransferGroundProjectorData E)

/-- Complement of the beta-zero ground projector. -/
def baseComplement : E →ₗ[ℝ] E :=
  (LinearMap.id : E →ₗ[ℝ] E) - D.baseProjector

@[simp] theorem baseComplement_apply (x : E) :
    D.baseComplement x = x - D.baseProjector x :=
  rfl

/-- Linearized ground-lifted defect `D_lift = I - T + P`.  Since the identity
has zero variation, its first variation is `-T₁ + P₁`. -/
def groundLiftedVariation : E →ₗ[ℝ] E :=
  -D.transferVariation + D.groundProjectorVariation

@[simp] theorem groundLiftedVariation_apply (x : E) :
    D.groundLiftedVariation x =
      -D.transferVariation x + D.groundProjectorVariation x :=
  rfl

/-- The base projector annihilates its complementary input. -/
theorem baseProjector_baseComplement_apply (x : E) :
    D.baseProjector (D.baseComplement x) = 0 := by
  rw [D.baseComplement_apply, map_sub, D.baseProjector_idempotent]
  exact sub_self _

/-- The complementary projector annihilates the base-projector image. -/
theorem baseComplement_baseProjector_apply (x : E) :
    D.baseComplement (D.baseProjector x) = 0 := by
  rw [D.baseComplement_apply, D.baseProjector_idempotent]
  exact sub_self _

/-- Comparing the linearized identities `T P = P` and `P² = P` shows that the
transfer and ground-projector variations agree on the beta-zero ground input. -/
theorem transferVariation_baseProjector_eq_groundProjectorVariation
    (x : E) :
    D.transferVariation (D.baseProjector x) =
      D.groundProjectorVariation (D.baseProjector x) := by
  have hT := D.transferGroundProjectorFirstVariation x
  have hP := D.groundProjectorIdempotentFirstVariation x
  exact add_right_cancel (hT.trans hP.symm)

/-- Comparing `P T = P` with `P² = P` gives equality after projecting the
variation output back to the beta-zero ground sector. -/
theorem baseProjector_transferVariation_eq_groundProjectorVariation
    (x : E) :
    D.baseProjector (D.transferVariation x) =
      D.baseProjector (D.groundProjectorVariation x) := by
  have hT := D.groundProjectorTransferFirstVariation x
  have hP := D.groundProjectorIdempotentFirstVariation x
  exact add_left_cancel (hT.trans hP.symm)

/-- The linearized ground-lifted defect vanishes on the beta-zero ground
sector. -/
theorem groundLiftedVariation_baseProjector_apply (x : E) :
    D.groundLiftedVariation (D.baseProjector x) = 0 := by
  rw [D.groundLiftedVariation_apply,
    D.transferVariation_baseProjector_eq_groundProjectorVariation]
  module

/-- The linearized ground-lifted defect has no beta-zero ground component in its
output. -/
theorem baseProjector_groundLiftedVariation_apply (x : E) :
    D.baseProjector (D.groundLiftedVariation x) = 0 := by
  rw [D.groundLiftedVariation_apply, map_add, map_neg,
    D.baseProjector_transferVariation_eq_groundProjectorVariation]
  module

/-- The ground-projector variation has no complement-to-complement block.  This
is the familiar off-diagonal first variation of an idempotent projector, proved
here only from the linearized projector identity. -/
theorem baseComplement_groundProjectorVariation_baseComplement_apply
    (x : E) :
    D.baseComplement
        (D.groundProjectorVariation (D.baseComplement x)) = 0 := by
  have hQ := D.baseProjector_baseComplement_apply x
  have hP := D.groundProjectorIdempotentFirstVariation (D.baseComplement x)
  rw [hQ, map_zero, zero_add] at hP
  rw [D.baseComplement_apply, hP]
  exact sub_self _

/-- Complementing the input does not change the ground-lifted first variation. -/
theorem groundLiftedVariation_baseComplement_apply (x : E) :
    D.groundLiftedVariation (D.baseComplement x) =
      D.groundLiftedVariation x := by
  rw [D.baseComplement_apply, map_sub,
    D.groundLiftedVariation_baseProjector_apply, sub_zero]

/-- Complementing the output does not change the ground-lifted first variation. -/
theorem baseComplement_groundLiftedVariation_apply (x : E) :
    D.baseComplement (D.groundLiftedVariation x) =
      D.groundLiftedVariation x := by
  rw [D.baseComplement_apply,
    D.baseProjector_groundLiftedVariation_apply, sub_zero]

/-- Exact first-order reduction at an idempotent beta-zero fixed point:

`D_lift,1 = - Q T₁ Q`, where `Q = I - P₀`.

The derivative of the moving spectral projector disappears from the
complement-to-complement block. -/
theorem groundLiftedVariation_eq_neg_baseComplement_transferVariation_baseComplement_apply
    (x : E) :
    D.groundLiftedVariation x =
      -D.baseComplement
        (D.transferVariation (D.baseComplement x)) := by
  calc
    D.groundLiftedVariation x =
        D.baseComplement
          (D.groundLiftedVariation (D.baseComplement x)) := by
      rw [D.groundLiftedVariation_baseComplement_apply,
        D.baseComplement_groundLiftedVariation_apply]
    _ = D.baseComplement
        (-D.transferVariation (D.baseComplement x) +
          D.groundProjectorVariation (D.baseComplement x)) := by
      rw [D.groundLiftedVariation_apply]
    _ = -D.baseComplement
          (D.transferVariation (D.baseComplement x)) +
        D.baseComplement
          (D.groundProjectorVariation (D.baseComplement x)) := by
      rw [map_add, map_neg]
    _ = -D.baseComplement
          (D.transferVariation (D.baseComplement x)) := by
      rw [D.baseComplement_groundProjectorVariation_baseComplement_apply]
      module

/-- Operator-level form `D_lift,1 = - Q ∘ T₁ ∘ Q`. -/
theorem groundLiftedVariation_eq_neg_baseComplement_comp_transferVariation_comp_baseComplement :
    D.groundLiftedVariation =
      -(D.baseComplement.comp
        (D.transferVariation.comp D.baseComplement)) := by
  apply LinearMap.ext
  intro x
  change D.groundLiftedVariation x =
    -D.baseComplement (D.transferVariation (D.baseComplement x))
  exact
    D.groundLiftedVariation_eq_neg_baseComplement_transferVariation_baseComplement_apply x

end FiniteLinearizedTransferGroundProjectorData

/-- Cross-carrier first variation of the transfer intertwining residual. -/
def finiteLinearizedTransferIntertwiningResidualLinearMap
    {Ef Ec : Type*}
    [AddCommGroup Ef] [Module ℝ Ef]
    [AddCommGroup Ec] [Module ℝ Ec]
    (Df : FiniteLinearizedTransferGroundProjectorData Ef)
    (Dc : FiniteLinearizedTransferGroundProjectorData Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  Df.transferVariation.comp J - J.comp Dc.transferVariation

/-- Cross-carrier first variation of the ground-lifted defect residual. -/
def finiteLinearizedGroundLiftedIntertwiningResidualLinearMap
    {Ef Ec : Type*}
    [AddCommGroup Ef] [Module ℝ Ef]
    [AddCommGroup Ec] [Module ℝ Ec]
    (Df : FiniteLinearizedTransferGroundProjectorData Ef)
    (Dc : FiniteLinearizedTransferGroundProjectorData Ec)
    (J : Ec →ₗ[ℝ] Ef) : Ec →ₗ[ℝ] Ef :=
  Df.groundLiftedVariation.comp J - J.comp Dc.groundLiftedVariation

/-- Beta-zero ground-projector intertwining implies intertwining of the
complementary projectors. -/
theorem finiteLinearized_baseComplement_intertwines
    {Ef Ec : Type*}
    [AddCommGroup Ef] [Module ℝ Ef]
    [AddCommGroup Ec] [Module ℝ Ec]
    (Df : FiniteLinearizedTransferGroundProjectorData Ef)
    (Dc : FiniteLinearizedTransferGroundProjectorData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hJ : ∀ x : Ec,
      Df.baseProjector (J x) = J (Dc.baseProjector x))
    (x : Ec) :
    Df.baseComplement (J x) = J (Dc.baseComplement x) := by
  rw [Df.baseComplement_apply, Dc.baseComplement_apply, hJ, map_sub]

/-- Exact cross-carrier first-order reduction:

`R_lift,1 = - Q_f R_T,1 Q_c`.

Thus only the complement-to-complement block of the transfer first-variation
residual can survive in the ground-lifted defect. -/
theorem finiteLinearizedGroundLiftedIntertwiningResidual_eq_neg_complementedTransfer_apply
    {Ef Ec : Type*}
    [AddCommGroup Ef] [Module ℝ Ef]
    [AddCommGroup Ec] [Module ℝ Ec]
    (Df : FiniteLinearizedTransferGroundProjectorData Ef)
    (Dc : FiniteLinearizedTransferGroundProjectorData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hJ : ∀ x : Ec,
      Df.baseProjector (J x) = J (Dc.baseProjector x))
    (x : Ec) :
    finiteLinearizedGroundLiftedIntertwiningResidualLinearMap Df Dc J x =
      -Df.baseComplement
        (finiteLinearizedTransferIntertwiningResidualLinearMap Df Dc J
          (Dc.baseComplement x)) := by
  have hf :=
    Df.groundLiftedVariation_eq_neg_baseComplement_transferVariation_baseComplement_apply (J x)
  have hc :=
    Dc.groundLiftedVariation_eq_neg_baseComplement_transferVariation_baseComplement_apply x
  have hQx := finiteLinearized_baseComplement_intertwines Df Dc J hJ x
  have hQT := finiteLinearized_baseComplement_intertwines Df Dc J hJ
    (Dc.transferVariation (Dc.baseComplement x))
  unfold finiteLinearizedGroundLiftedIntertwiningResidualLinearMap
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, hf, hc]
  rw [map_neg, hQx, ← hQT]
  unfold finiteLinearizedTransferIntertwiningResidualLinearMap
  rw [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_sub]
  module

/-- Operator-level cross-carrier form of the complemented first-variation
identity. -/
theorem finiteLinearizedGroundLiftedIntertwiningResidual_eq_neg_complementedTransfer
    {Ef Ec : Type*}
    [AddCommGroup Ef] [Module ℝ Ef]
    [AddCommGroup Ec] [Module ℝ Ec]
    (Df : FiniteLinearizedTransferGroundProjectorData Ef)
    (Dc : FiniteLinearizedTransferGroundProjectorData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hJ : ∀ x : Ec,
      Df.baseProjector (J x) = J (Dc.baseProjector x)) :
    finiteLinearizedGroundLiftedIntertwiningResidualLinearMap Df Dc J =
      -(Df.baseComplement.comp
        ((finiteLinearizedTransferIntertwiningResidualLinearMap Df Dc J).comp
          Dc.baseComplement)) := by
  apply LinearMap.ext
  intro x
  change
    finiteLinearizedGroundLiftedIntertwiningResidualLinearMap Df Dc J x =
      -Df.baseComplement
        (finiteLinearizedTransferIntertwiningResidualLinearMap Df Dc J
          (Dc.baseComplement x))
  exact
    finiteLinearizedGroundLiftedIntertwiningResidual_eq_neg_complementedTransfer_apply
      Df Dc J hJ x

/-- A single nonzero complemented transfer-variation witness certifies a
nonzero ground-lifted first-variation residual. -/
theorem finiteLinearizedGroundLiftedIntertwiningResidual_ne_zero_of_complementedTransfer
    {Ef Ec : Type*}
    [AddCommGroup Ef] [Module ℝ Ef]
    [AddCommGroup Ec] [Module ℝ Ec]
    (Df : FiniteLinearizedTransferGroundProjectorData Ef)
    (Dc : FiniteLinearizedTransferGroundProjectorData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hJ : ∀ x : Ec,
      Df.baseProjector (J x) = J (Dc.baseProjector x))
    (x : Ec)
    (hx : Df.baseComplement
        (finiteLinearizedTransferIntertwiningResidualLinearMap Df Dc J
          (Dc.baseComplement x)) ≠ 0) :
    finiteLinearizedGroundLiftedIntertwiningResidualLinearMap Df Dc J ≠ 0 := by
  intro hzero
  have hpoint := LinearMap.congr_fun hzero x
  rw [finiteLinearizedGroundLiftedIntertwiningResidual_eq_neg_complementedTransfer_apply
    Df Dc J hJ x] at hpoint
  exact hx (neg_eq_zero.mp hpoint)

/-- Audit-visible generic Package-T receipt. -/
structure FiniteLinearizedGroundLiftedFirstVariationPackage
    {Ef Ec : Type*}
    [AddCommGroup Ef] [Module ℝ Ef]
    [AddCommGroup Ec] [Module ℝ Ec]
    (Df : FiniteLinearizedTransferGroundProjectorData Ef)
    (Dc : FiniteLinearizedTransferGroundProjectorData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hJ : ∀ x : Ec,
      Df.baseProjector (J x) = J (Dc.baseProjector x)) where
  fineLiftedVariation : Ef →ₗ[ℝ] Ef
  fineLiftedVariation_eq : fineLiftedVariation = Df.groundLiftedVariation
  coarseLiftedVariation : Ec →ₗ[ℝ] Ec
  coarseLiftedVariation_eq : coarseLiftedVariation = Dc.groundLiftedVariation
  fineComplementReduction :
    Df.groundLiftedVariation =
      -(Df.baseComplement.comp
        (Df.transferVariation.comp Df.baseComplement))
  coarseComplementReduction :
    Dc.groundLiftedVariation =
      -(Dc.baseComplement.comp
        (Dc.transferVariation.comp Dc.baseComplement))
  crossCarrierReduction :
    finiteLinearizedGroundLiftedIntertwiningResidualLinearMap Df Dc J =
      -(Df.baseComplement.comp
        ((finiteLinearizedTransferIntertwiningResidualLinearMap Df Dc J).comp
          Dc.baseComplement))

/-- Construct the complete generic first-variation reduction receipt. -/
noncomputable def finiteLinearizedGroundLiftedFirstVariationPackage
    {Ef Ec : Type*}
    [AddCommGroup Ef] [Module ℝ Ef]
    [AddCommGroup Ec] [Module ℝ Ec]
    (Df : FiniteLinearizedTransferGroundProjectorData Ef)
    (Dc : FiniteLinearizedTransferGroundProjectorData Ec)
    (J : Ec →ₗ[ℝ] Ef)
    (hJ : ∀ x : Ec,
      Df.baseProjector (J x) = J (Dc.baseProjector x)) :
    FiniteLinearizedGroundLiftedFirstVariationPackage Df Dc J hJ where
  fineLiftedVariation := Df.groundLiftedVariation
  fineLiftedVariation_eq := rfl
  coarseLiftedVariation := Dc.groundLiftedVariation
  coarseLiftedVariation_eq := rfl
  fineComplementReduction :=
    Df.groundLiftedVariation_eq_neg_baseComplement_comp_transferVariation_comp_baseComplement
  coarseComplementReduction :=
    Dc.groundLiftedVariation_eq_neg_baseComplement_comp_transferVariation_comp_baseComplement
  crossCarrierReduction :=
    finiteLinearizedGroundLiftedIntertwiningResidual_eq_neg_complementedTransfer
      Df Dc J hJ

end

end MathlibAnalytic
end MGAP4D
