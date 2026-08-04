import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedPosterior
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobParallelCouplingStability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Coordinate-coupling data for the normalized augmented one-slab posterior.
For two upper boundaries differing only at `target`, the coupling joins the
augmented states `(U,X)` and `(V,Y)`.  Only lower-slice mismatches enter the
influence matrix used by the actual Doob operator. -/
structure Z2UnfixedGaugeDoobAugmentedVolumeCouplingData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  influence :
    FiniteEvenFourTorusSpatialLink H →
      FiniteEvenFourTorusSpatialLink H → ℝ
  influence_nonneg :
    ∀ target source : FiniteEvenFourTorusSpatialLink H,
      0 ≤ influence target source
  coupling :
    FiniteEvenFourTorusSpatialLink H →
      FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2TemporalLinkField H →
      FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2TemporalLinkField H →
      FiniteEvenFourTorusZ2SliceConfiguration H → ℝ
  coupling_nonneg :
    ∀ (target : FiniteEvenFourTorusSpatialLink H)
      (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
      (U : FiniteEvenFourTorusZ2TemporalLinkField H)
      (X : FiniteEvenFourTorusZ2SliceConfiguration H)
      (V : FiniteEvenFourTorusZ2TemporalLinkField H)
      (Y : FiniteEvenFourTorusZ2SliceConfiguration H),
      FiniteProductAgreeOff A B target →
        0 ≤ coupling target A B U X V Y
  left_marginal :
    ∀ (target : FiniteEvenFourTorusSpatialLink H)
      (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
      (U : FiniteEvenFourTorusZ2TemporalLinkField H)
      (X : FiniteEvenFourTorusZ2SliceConfiguration H),
      FiniteProductAgreeOff A B target →
        (∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
            coupling target A B U X V Y) =
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
            H β energyIdentity energyNontrivial hβ.le hEnergy.le U X A
  right_marginal :
    ∀ (target : FiniteEvenFourTorusSpatialLink H)
      (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
      (V : FiniteEvenFourTorusZ2TemporalLinkField H)
      (Y : FiniteEvenFourTorusZ2SliceConfiguration H),
      FiniteProductAgreeOff A B target →
        (∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
            coupling target A B U X V Y) =
          finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
            H β energyIdentity energyNontrivial hβ.le hEnergy.le V Y B
  mismatchExpectation_le :
    ∀ (target source : FiniteEvenFourTorusSpatialLink H)
      (A B : FiniteEvenFourTorusZ2SliceConfiguration H),
      FiniteProductAgreeOff A B target →
        (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
          ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
              ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
                coupling target A B U X V Y *
                  finiteProductMismatchIndicator X Y source) ≤
          influence target source
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  columnSum_le_coefficient :
    ∀ source : FiniteEvenFourTorusSpatialLink H,
      (∑ target : FiniteEvenFourTorusSpatialLink H,
        influence target source) ≤ coefficient
  coefficient_lt_one : coefficient < 1

namespace Z2UnfixedGaugeDoobAugmentedVolumeCouplingData

variable
  {H : ℕ}
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 < β}
  {hEnergy : energyIdentity < energyNontrivial}

/-- Marginalize both temporal-link fields from an augmented coupling. -/
noncomputable def projectedSliceCoupling
    (C : Z2UnfixedGaugeDoobAugmentedVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H)
    (A B X Y : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
    ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
      C.coupling target A B U X V Y

/-- Temporal marginalization preserves nonnegativity. -/
theorem projectedSliceCoupling_nonneg
    (C : Z2UnfixedGaugeDoobAugmentedVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H)
    (A B X Y : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B target) :
    0 ≤ C.projectedSliceCoupling target A B X Y := by
  unfold projectedSliceCoupling
  exact Finset.sum_nonneg fun U _hU =>
    Finset.sum_nonneg fun V _hV =>
      C.coupling_nonneg target A B U X V Y hAgree

/-- The left marginal of the projected coupling is the actual Perron-Doob
output law at the first upper boundary. -/
theorem projectedSliceCoupling_left_marginal
    (C : Z2UnfixedGaugeDoobAugmentedVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H)
    (A B X : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B target) :
    (∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
      C.projectedSliceCoupling target A B X Y) =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le X A := by
  classical
  unfold projectedSliceCoupling
  calc
    (∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          C.coupling target A B U X V Y) =
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
            ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
              C.coupling target A B U X V Y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U _hU
      rw [Finset.sum_comm]
    _ = ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
          H β energyIdentity energyNontrivial hβ.le hEnergy.le U X A := by
      apply Finset.sum_congr rfl
      intro U _hU
      exact C.left_marginal target A B U X hAgree
    _ = finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le X A :=
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_sum_temporal
        H β energyIdentity energyNontrivial hβ.le hEnergy.le X A

/-- The right marginal of the projected coupling is the actual Perron-Doob
output law at the second upper boundary. -/
theorem projectedSliceCoupling_right_marginal
    (C : Z2UnfixedGaugeDoobAugmentedVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H)
    (A B Y : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B target) :
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      C.projectedSliceCoupling target A B X Y) =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le Y B := by
  classical
  unfold projectedSliceCoupling
  calc
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          C.coupling target A B U X V Y) =
        ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
              C.coupling target A B U X V Y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro U _hU
      rw [Finset.sum_comm]
      rw [Finset.sum_comm]
    _ = ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior
          H β energyIdentity energyNontrivial hβ.le hEnergy.le V Y B := by
      apply Finset.sum_congr rfl
      intro V _hV
      exact C.right_marginal target A B V Y hAgree
    _ = finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le Y B :=
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedPosterior_sum_temporal
        H β energyIdentity energyNontrivial hβ.le hEnergy.le Y B

/-- Lower-slice mismatch expectations are unchanged by marginalizing the
auxiliary temporal-link fields. -/
theorem projectedSliceCoupling_mismatchExpectation_le
    (C : Z2UnfixedGaugeDoobAugmentedVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B target) :
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
        C.projectedSliceCoupling target A B X Y *
          finiteProductMismatchIndicator X Y source) ≤
      C.influence target source := by
  classical
  calc
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
        C.projectedSliceCoupling target A B X Y *
          finiteProductMismatchIndicator X Y source) =
        ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
          ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
              ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
                C.coupling target A B U X V Y *
                  finiteProductMismatchIndicator X Y source := by
      apply Finset.sum_congr rfl
      intro X _hX
      apply Finset.sum_congr rfl
      intro Y _hY
      unfold projectedSliceCoupling
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro U _hU
      rw [Finset.sum_mul]
    _ ≤ C.influence target source :=
      C.mismatchExpectation_le target source A B hAgree

/-- An augmented posterior coupling projects to exactly the model-facing
finite-volume Perron-Doob coupling package. -/
noncomputable def toVolumeCouplingData
    (C : Z2UnfixedGaugeDoobAugmentedVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeDoobParallelVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy :=
  { influence := C.influence
    influence_nonneg := C.influence_nonneg
    coupling := C.projectedSliceCoupling
    coupling_nonneg := C.projectedSliceCoupling_nonneg
    left_marginal := C.projectedSliceCoupling_left_marginal
    right_marginal := C.projectedSliceCoupling_right_marginal
    mismatchExpectation_le := C.projectedSliceCoupling_mismatchExpectation_le
    coefficient := C.coefficient
    coefficient_nonneg := C.coefficient_nonneg
    columnSum_le_coefficient := C.columnSum_le_coefficient
    coefficient_lt_one := C.coefficient_lt_one }

end Z2UnfixedGaugeDoobAugmentedVolumeCouplingData

/-- All-volume augmented-posterior coupling package with a common strict
column-sum rate. -/
structure Z2UnfixedGaugeDoobAugmentedUniformCouplingCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  rate : ℝ
  crossingRate_le_rate :
    z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial ≤ rate
  rate_lt_one : rate < 1
  couplingData : ∀ H : ℕ,
    Z2UnfixedGaugeDoobAugmentedVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy
  coefficient_le_rate : ∀ H : ℕ,
    (couplingData H).coefficient ≤ rate

namespace Z2UnfixedGaugeDoobAugmentedUniformCouplingCertificate

variable
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 < β}
  {hEnergy : energyIdentity < energyNontrivial}

/-- Project every augmented finite-volume coupling to the actual Perron-Doob
slice coupling package. -/
noncomputable def toParallelUniformCouplingCertificate
    (C : Z2UnfixedGaugeDoobAugmentedUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeDoobParallelUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  { rate := C.rate
    crossingRate_le_rate := C.crossingRate_le_rate
    rate_lt_one := C.rate_lt_one
    couplingData := fun H => (C.couplingData H).toVolumeCouplingData
    coefficient_le_rate := by
      intro H
      exact C.coefficient_le_rate H }

/-- A common strict augmented coupling therefore yields the full existing
spatial-sandwich stability package. -/
noncomputable def toSpatialSandwichCertificate
    (C : Z2UnfixedGaugeDoobAugmentedUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  C.toParallelUniformCouplingCertificate.toSpatialSandwichCertificate

end Z2UnfixedGaugeDoobAugmentedUniformCouplingCertificate

end

end MathlibAnalytic
end MGAP4D
