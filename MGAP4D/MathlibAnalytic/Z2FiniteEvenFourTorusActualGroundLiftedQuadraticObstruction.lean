import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusActualGroundProjectorRankOne
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusOneSlabSecondMomentCrossingReduction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossingSecondMomentEnergyWitness
import MGAP4D.MathlibAnalytic.NonzeroSecondOrderSmallPositive
import MGAP4D.MathlibAnalytic.FiniteUniformAverageComplementMixedDifferenceWitness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set TopologicalSpace
open scoped BigOperators InnerProduct

noncomputable section

/-- Kernel of the actual operator-norm-normalized one-slab coupling family.
For nonnegative coupling its finite-kernel operator is the physical one-slab
transfer used by the finite Z₂ spectral construction. -/
noncomputable def finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2OneSlabCouplingFamilyNormalization
      H energyIdentity energyNontrivial β *
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelCouplingFamily
      H energyIdentity energyNontrivial β A B

/-- Positive-side ground-lifted kernel written without differentiating either
the operator norm or the moving spectral basis.  The first term is the
canonical Perron rank-one ground projector kernel; the second is the actual
operator-norm-normalized transfer kernel. -/
noncomputable def finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension
      H energyIdentity energyNontrivial β A B -
    finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel
      H energyIdentity energyNontrivial β A B

/-- Mixed difference of the normalized transfer kernel is exactly the scalar
mixed-difference family already realized to second order. -/
theorem finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel_mixedDifference_eq
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteKernelMixedCrossDifference
        (finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel
          H energyIdentity energyNontrivial β)
        x x' y y' =
      finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyMixedDifference
        H energyIdentity energyNontrivial x x' y y' β := by
  unfold finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel
    finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyMixedDifference
    finiteEvenFourTorusZ2OneSlabCouplingFamilyMixedDifference
    finiteKernelMixedCrossDifference
  ring

/-- The ground-lifted mixed difference is projector minus normalized transfer,
with no hidden basis choices. -/
theorem finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_mixedDifference_eq
    (H : ℕ)
    (energyIdentity energyNontrivial β : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteKernelMixedCrossDifference
        (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
          H energyIdentity energyNontrivial β)
        x x' y y' =
      finiteKernelMixedCrossDifference
          (finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension
            H energyIdentity energyNontrivial β)
          x x' y y' -
        finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyMixedDifference
          H energyIdentity energyNontrivial x x' y y' β := by
  unfold finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
    finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyKernel
    finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyMixedDifference
    finiteEvenFourTorusZ2OneSlabCouplingFamilyMixedDifference
    finiteKernelMixedCrossDifference
  ring

/-- Exact scalar version of the Package-W/X second-moment reduction:

`ΔK₂ = ΔM₂_cross + (1/2) ΔS_left ΔS_right`.

All one-boundary square terms and all terms involving the boundary-independent
crossing mean cancel in the four-point mixed difference. -/
theorem finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference_eq_crossing_add_spatial
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference
        H energyIdentity energyNontrivial x x' y y' =
      finiteKernelMixedCrossDifference
          (finiteEvenFourTorusZ2TemporalCrossingSecondMoment
            H energyIdentity energyNontrivial)
          x x' y y' +
        (1 / 2 : ℝ) *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial x -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial x') *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y') := by
  let C := FiniteEvenFourTorusZ2SliceConfiguration H
  let Γ := FiniteEvenFourTorusZ2TemporalLinkField H
  let spatial : C → ℝ := fun A =>
    finiteEvenFourTorusZ2SpatialWilsonAction
      H energyIdentity energyNontrivial A
  let crossing : Γ → C → C → ℝ := fun U A B =>
    finiteEvenFourTorusZ2UnfixedGaugeCrossingAction
      H 0 energyIdentity energyNontrivial U A B
  let crossingMean :=
    finiteEvenFourTorusZ2TemporalCrossingMean
      H energyIdentity energyNontrivial
  have hMean : ∀ A B : C,
      (Fintype.card Γ : ℝ)⁻¹ * ∑ U : Γ, crossing U A B = crossingMean := by
    intro A B
    simpa [Γ, crossing, crossingMean] using
      finiteEvenFourTorusZ2TemporalLinkAverage_crossingAction_eq_crossingMean
        H energyIdentity energyNontrivial A B
  have hpoint : ∀ A B : C,
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation
          H energyIdentity energyNontrivial A B =
        finiteEvenFourTorusZ2OneSlabSecondMomentInteraction
            H energyIdentity energyNontrivial A B +
          ((1 / 2 : ℝ) * spatial A) ^ 2 +
          ((1 / 2 : ℝ) * spatial B) ^ 2 +
          2 * crossingMean * ((1 / 2 : ℝ) * spatial A) +
          2 * crossingMean * ((1 / 2 : ℝ) * spatial B) := by
    intro A B
    rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernelAnalyticSecondVariation_eq_uniformSlabSecondMoment]
    simpa [C, Γ, spatial, crossing,
      finiteEvenFourTorusZ2OneSlabSecondMomentInteraction] using
      (finiteUniformSlabSecondMoment_eq_interaction_add_additive
        (α := C) (γ := Γ)
        (fun A : C => (1 / 2 : ℝ) * spatial A)
        (fun B : C => (1 / 2 : ℝ) * spatial B)
        crossing crossingMean hMean A B)
  unfold finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference
    finiteKernelMixedCrossDifference
  rw [hpoint x y, hpoint x y', hpoint x' y, hpoint x' y']
  rw [finiteEvenFourTorusZ2OneSlabSecondMomentInteraction_eq,
    finiteEvenFourTorusZ2OneSlabSecondMomentInteraction_eq,
    finiteEvenFourTorusZ2OneSlabSecondMomentInteraction_eq,
    finiteEvenFourTorusZ2OneSlabSecondMomentInteraction_eq]
  dsimp [spatial]
  ring

/-- Exact Package-Z cancellation.  The spatial rank-one piece in the transfer
quadratic coefficient is cancelled by the quadratic motion of the canonical
ground projector.  What remains is only the temporal-crossing second moment:

`Δ(Pβ - Tβ)/β² → -(1/(2 |C_H|)) ΔM₂_cross`.

This uses only continuity of the transfer normalization and the first-order
Perron-ground slope. -/
theorem finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_mixedDifference_quadraticQuotient
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (x x' y y' : FiniteEvenFourTorusZ2SliceConfiguration H) :
    Tendsto
      (fun β : ℝ =>
        finiteKernelMixedCrossDifference
            (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
              H energyIdentity energyNontrivial β)
            x x' y y' / β ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (-((Fintype.card
              (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
            finiteKernelMixedCrossDifference
              (finiteEvenFourTorusZ2TemporalCrossingSecondMoment
                H energyIdentity energyNontrivial)
              x x' y y' / (2 : ℝ)))) := by
  have hProjector :=
    finiteEvenFourTorusZ2CanonicalGroundRankOneProjectorKernelRightExtension_mixedDifference_quadraticQuotient
      H energyIdentity energyNontrivial hEnergy x x' y y'
  have hTransfer :=
    finiteEvenFourTorusZ2NormalizedOneSlabCouplingFamilyMixedDifference_quadraticQuotient
      H energyIdentity energyNontrivial x x' y y'
  have hSub := hProjector.sub hTransfer
  have hSecond :=
    finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference_eq_crossing_add_spatial
      H energyIdentity energyNontrivial x x' y y'
  have hLimit :
      ((Fintype.card
            (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
          (1 / 4 : ℝ) *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial x -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial x') *
          (finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y -
            finiteEvenFourTorusZ2SpatialWilsonAction
              H energyIdentity energyNontrivial y')) -
        (((Fintype.card
              (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
            finiteEvenFourTorusZ2OneSlabAnalyticSecondVariationMixedDifference
              H energyIdentity energyNontrivial x x' y y') / (2 : ℝ)) =
      -((Fintype.card
            (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
          finiteKernelMixedCrossDifference
            (finiteEvenFourTorusZ2TemporalCrossingSecondMoment
              H energyIdentity energyNontrivial)
            x x' y y' / (2 : ℝ)) := by
    rw [hSecond]
    ring
  rw [hLimit] at hSub
  simpa only [
    finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_mixedDifference_eq,
    sub_div] using hSub

/-- At the explicit side-two witness (`H = 0`), the ground-lifted quadratic
coefficient is exactly minus the inverse boundary cardinality times the square
of the physical two-level energy gap. -/
theorem finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_mixedDifference_witness_zero_quadraticQuotient
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Tendsto
      (fun β : ℝ =>
        finiteKernelMixedCrossDifference
            (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
              0 energyIdentity energyNontrivial β)
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation / β ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (-((Fintype.card
              (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ)⁻¹ *
            (energyNontrivial - energyIdentity) ^ 2))) := by
  have h :=
    finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_mixedDifference_quadraticQuotient
      0 energyIdentity energyNontrivial hEnergy
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
  rw [finiteEvenFourTorusZ2TemporalCrossingSecondMoment_mixedDifference_witness_zero] at h
  convert h using 1 <;> ring

/-- The explicit Package-Z limiting coefficient is nonzero under strict
physical energy ordering. -/
theorem finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_witness_zero_quadraticCoefficient_ne_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    -((Fintype.card
          (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ)⁻¹ *
        (energyNontrivial - energyIdentity) ^ 2) ≠ 0 := by
  have hcard :
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration 0) ≠ 0)
  have hgap : energyNontrivial - energyIdentity ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt hEnergy)
  exact neg_ne_zero.mpr
    (mul_ne_zero (inv_ne_zero hcard) (pow_ne_zero 2 hgap))

/-- Unconditional finite-Z₂ small-positive ground-lifted obstruction at the
explicit side-two witness.  No second derivative of the operator norm or moving
spectral projector is assumed. -/
theorem finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_exists_smallPositive_mixedDifference_ne_zero_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, 0 < β → β < ε →
        finiteKernelMixedCrossDifference
            (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
              0 energyIdentity energyNontrivial β)
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation ≠ 0 := by
  exact
    Tendsto.exists_pos_forall_pos_lt_ne_zero_of_quadraticQuotient_ne_zero
      (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_mixedDifference_witness_zero_quadraticQuotient
        energyIdentity energyNontrivial hEnergy.le)
      (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_witness_zero_quadraticCoefficient_ne_zero
        energyIdentity energyNontrivial hEnergy)

/-- Operator-level form of the same unconditional obstruction: on a whole
small positive interval, the uniform beta-zero complement block of the actual
rank-one-ground-lifted kernel is nonzero. -/
theorem finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_exists_smallPositive_uniformComplementBlock_ne_zero_zero
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, 0 < β → β < ε →
        finiteUniformAverageComplementLinearMap.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
              0 energyIdentity energyNontrivial β)).toLinearMap.comp
            finiteUniformAverageComplementLinearMap) ≠ 0 := by
  rcases
      finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_exists_smallPositive_mixedDifference_ne_zero_zero
        energyIdentity energyNontrivial hEnergy with
    ⟨ε, hε, hMixed⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  exact
    finiteUniformAverageComplement_comp_finiteKernelOperator_comp_complement_ne_zero_of_mixedCrossDifference_ne_zero
      (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
        0 energyIdentity energyNontrivial β)
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
      finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
      (hMixed β hβ hβε)

/-- Audit-visible Package-Z receipt. -/
structure Z2FiniteEvenFourTorusActualGroundLiftedQuadraticObstructionPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) where
  exactQuadraticCoefficient :
    Tendsto
      (fun β : ℝ =>
        finiteKernelMixedCrossDifference
            (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
              0 energyIdentity energyNontrivial β)
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessIdentity
            finiteEvenFourTorusZ2CrossingSecondMomentWitnessExcitation / β ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds
        (-((Fintype.card
              (FiniteEvenFourTorusZ2SliceConfiguration 0) : ℝ)⁻¹ *
            (energyNontrivial - energyIdentity) ^ 2)))
  smallPositiveBlockNonzero :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ β : ℝ, 0 < β → β < ε →
        finiteUniformAverageComplementLinearMap.comp
          ((finiteKernelOperator
            (finiteEvenFourTorusZ2GroundLiftedKernelRightExtension
              0 energyIdentity energyNontrivial β)).toLinearMap.comp
            finiteUniformAverageComplementLinearMap) ≠ 0

/-- Construct the unconditional finite-Z₂ Package-Z receipt. -/
noncomputable def z2FiniteEvenFourTorusActualGroundLiftedQuadraticObstructionPackage
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2FiniteEvenFourTorusActualGroundLiftedQuadraticObstructionPackage
      energyIdentity energyNontrivial hEnergy where
  exactQuadraticCoefficient :=
    finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_mixedDifference_witness_zero_quadraticQuotient
      energyIdentity energyNontrivial hEnergy.le
  smallPositiveBlockNonzero :=
    finiteEvenFourTorusZ2GroundLiftedKernelRightExtension_exists_smallPositive_uniformComplementBlock_ne_zero_zero
      energyIdentity energyNontrivial hEnergy

end

end MathlibAnalytic
end MGAP4D
