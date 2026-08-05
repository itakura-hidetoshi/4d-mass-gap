import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedPosterior
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobParallelCouplingStability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Marginalize an augmented coupling over both temporal-link fields, retaining
only the pair of lower boundary slices. -/
def finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
    (H : ℕ)
    (coupling :
      FiniteEvenFourTorusSpatialLink H →
        FiniteEvenFourTorusZ2SliceConfiguration H →
        FiniteEvenFourTorusZ2SliceConfiguration H →
        FiniteEvenFourTorusZ2TemporalLinkField H →
        FiniteEvenFourTorusZ2SliceConfiguration H →
        FiniteEvenFourTorusZ2TemporalLinkField H →
        FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (A B X Y : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
    ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
      coupling target A B U X V Y

/-- A finite-volume coupling of the two normalized augmented Gibbs posteriors
associated with upper boundaries differing only at one target link.  Its
quantitative mismatch field concerns lower-slice coordinates, exactly the
quantity needed by the actual parallel Doob variation route. -/
structure Z2UnfixedGaugeDoobAugmentedCouplingData
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
            finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
                H coupling target A B X Y *
              finiteProductMismatchIndicator X Y source) ≤
          influence target source
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  columnSum_le_coefficient :
    ∀ source : FiniteEvenFourTorusSpatialLink H,
      (∑ target : FiniteEvenFourTorusSpatialLink H,
        influence target source) ≤ coefficient
  coefficient_lt_one : coefficient < 1

namespace Z2UnfixedGaugeDoobAugmentedCouplingData

variable
  {H : ℕ}
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 < β}
  {hEnergy : energyIdentity < energyNontrivial}

/-- Temporal-link marginalization preserves nonnegativity of the augmented
coupling. -/
theorem lowerMarginal_nonneg
    (C : Z2UnfixedGaugeDoobAugmentedCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H)
    (A B X Y : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B target) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
      H C.coupling target A B X Y := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
  apply Finset.sum_nonneg
  intro U _hU
  apply Finset.sum_nonneg
  intro V _hV
  exact C.coupling_nonneg target A B U X V Y hAgree

/-- The lower-slice marginal has the first actual Perron Doob law as its left
marginal. -/
theorem lowerMarginal_left
    (C : Z2UnfixedGaugeDoobAugmentedCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H)
    (A B X : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B target) :
    (∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
        H C.coupling target A B X Y) =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le X A := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
  calc
    (∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          C.coupling target A B U X V Y) =
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
            ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
              C.coupling target A B U X V Y := by
      rw [Finset.sum_comm]
    _ = ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
            ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
              C.coupling target A B U X V Y := by
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

/-- The lower-slice marginal has the second actual Perron Doob law as its right
marginal. -/
theorem lowerMarginal_right
    (C : Z2UnfixedGaugeDoobAugmentedCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H)
    (A B Y : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAgree : FiniteProductAgreeOff A B target) :
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
        H C.coupling target A B X Y) =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le Y B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
  calc
    (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
      ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
        ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          C.coupling target A B U X V Y) =
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
            ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
              C.coupling target A B U X V Y := by
      rw [Finset.sum_comm]
    _ = ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
            ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
              C.coupling target A B U X V Y := by
      apply Finset.sum_congr rfl
      intro U _hU
      rw [Finset.sum_comm]
    _ = ∑ V : FiniteEvenFourTorusZ2TemporalLinkField H,
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            ∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
              C.coupling target A B U X V Y := by
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

/-- Marginalizing an augmented coupling produces exactly the model-facing
actual Perron Doob coordinate-coupling package, with no loss in influence or
column-sum coefficient. -/
noncomputable def toDoobCouplingData
    (C : Z2UnfixedGaugeDoobAugmentedCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeDoobParallelVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy :=
  { influence := C.influence
    influence_nonneg := C.influence_nonneg
    coupling :=
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedCouplingLowerMarginal
        H C.coupling
    coupling_nonneg := C.lowerMarginal_nonneg
    left_marginal := C.lowerMarginal_left
    right_marginal := C.lowerMarginal_right
    mismatchExpectation_le := C.mismatchExpectation_le
    coefficient := C.coefficient
    coefficient_nonneg := C.coefficient_nonneg
    columnSum_le_coefficient := C.columnSum_le_coefficient
    coefficient_lt_one := C.coefficient_lt_one }

@[simp] theorem toDoobCouplingData_coefficient
    (C : Z2UnfixedGaugeDoobAugmentedCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    C.toDoobCouplingData.coefficient = C.coefficient :=
  rfl

end Z2UnfixedGaugeDoobAugmentedCouplingData

/-- All-volume augmented posterior coupling package with one common strict
column-sum rate. -/
structure Z2UnfixedGaugeDoobParallelUniformAugmentedCouplingCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  rate : ℝ
  crossingRate_le_rate :
    z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial ≤ rate
  rate_lt_one : rate < 1
  augmentedCouplingData : ∀ H : ℕ,
    Z2UnfixedGaugeDoobAugmentedCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy
  coefficient_le_rate : ∀ H : ℕ,
    (augmentedCouplingData H).coefficient ≤ rate

namespace Z2UnfixedGaugeDoobParallelUniformAugmentedCouplingCertificate

variable
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 < β}
  {hEnergy : energyIdentity < energyNontrivial}

/-- Exact all-volume conversion from augmented-state couplings to actual Doob
output couplings. -/
noncomputable def toUniformDoobCouplingCertificate
    (C : Z2UnfixedGaugeDoobParallelUniformAugmentedCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeDoobParallelUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  { rate := C.rate
    crossingRate_le_rate := C.crossingRate_le_rate
    rate_lt_one := C.rate_lt_one
    couplingData := fun H => (C.augmentedCouplingData H).toDoobCouplingData
    coefficient_le_rate := by
      intro H
      simpa using C.coefficient_le_rate H }

/-- The augmented coupling package therefore yields the existing terminal
spatial-sandwich stability certificate. -/
noncomputable def toSpatialSandwichCertificate
    (C : Z2UnfixedGaugeDoobParallelUniformAugmentedCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  C.toUniformDoobCouplingCertificate.toSpatialSandwichCertificate

end Z2UnfixedGaugeDoobParallelUniformAugmentedCouplingCertificate

end

end MathlibAnalytic
end MGAP4D
