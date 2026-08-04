import MGAP4D.MathlibAnalytic.FiniteProductDoobCouplingVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobParallelVariationStability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Actual finite-volume coordinate-coupling data written with the named
Perron Doob kernel in its marginal equations. Keeping this model-facing
structure independent of the generic kernel-indexed structure prevents Lean
from normalizing the full lattice carrier while declaring the all-volume
certificate. -/
structure Z2UnfixedGaugeDoobParallelVolumeCouplingData
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
      FiniteEvenFourTorusZ2SliceConfiguration H →
      FiniteEvenFourTorusZ2SliceConfiguration H → ℝ
  coupling_nonneg :
    ∀ (target : FiniteEvenFourTorusSpatialLink H)
      (A B X Y : FiniteEvenFourTorusZ2SliceConfiguration H),
      FiniteProductAgreeOff A B target →
        0 ≤ coupling target A B X Y
  left_marginal :
    ∀ (target : FiniteEvenFourTorusSpatialLink H)
      (A B X : FiniteEvenFourTorusZ2SliceConfiguration H),
      FiniteProductAgreeOff A B target →
        (∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
          coupling target A B X Y) =
            finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
              H β energyIdentity energyNontrivial hβ.le hEnergy.le X A
  right_marginal :
    ∀ (target : FiniteEvenFourTorusSpatialLink H)
      (A B Y : FiniteEvenFourTorusZ2SliceConfiguration H),
      FiniteProductAgreeOff A B target →
        (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
          coupling target A B X Y) =
            finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
              H β energyIdentity energyNontrivial hβ.le hEnergy.le Y B
  mismatchExpectation_le :
    ∀ (target source : FiniteEvenFourTorusSpatialLink H)
      (A B : FiniteEvenFourTorusZ2SliceConfiguration H),
      FiniteProductAgreeOff A B target →
        (∑ X : FiniteEvenFourTorusZ2SliceConfiguration H,
          ∑ Y : FiniteEvenFourTorusZ2SliceConfiguration H,
            coupling target A B X Y *
              finiteProductMismatchIndicator X Y source) ≤
          influence target source
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  columnSum_le_coefficient :
    ∀ source : FiniteEvenFourTorusSpatialLink H,
      (∑ target : FiniteEvenFourTorusSpatialLink H,
        influence target source) ≤ coefficient
  coefficient_lt_one : coefficient < 1

namespace Z2UnfixedGaugeDoobParallelVolumeCouplingData

variable
  {H : ℕ}
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 < β}
  {hEnergy : energyIdentity < energyNontrivial}

/-- The model-facing actual coupling package is exactly the generic coupling
package for the actual Perron Doob kernel. -/
set_option maxHeartbeats 1000000 in
noncomputable def toGeneric
    (C : Z2UnfixedGaugeDoobParallelVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    @FiniteProductKernelCouplingVariationData
      (FiniteEvenFourTorusSpatialLink H) Z2Gauge
      inferInstance inferInstance inferInstance inferInstance
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobKernel :=
  { influence := C.influence
    influence_nonneg := C.influence_nonneg
    coupling := C.coupling
    coupling_nonneg := C.coupling_nonneg
    left_marginal := by
      intro target A B X hAgree
      simpa only [finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel] using
        C.left_marginal target A B X hAgree
    right_marginal := by
      intro target A B Y hAgree
      simpa only [finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel] using
        C.right_marginal target A B Y hAgree
    mismatchExpectation_le := C.mismatchExpectation_le
    coefficient := C.coefficient
    coefficient_nonneg := C.coefficient_nonneg
    columnSum_le_coefficient := C.columnSum_le_coefficient
    coefficient_lt_one := C.coefficient_lt_one }

end Z2UnfixedGaugeDoobParallelVolumeCouplingData

/-- A proof-relevant all-volume coordinate-coupling package for the actual
Perron Doob kernels. For every finite volume it supplies genuine couplings
with the correct Doob marginals, coordinatewise output-mismatch bounds, and a
common strict column-sum rate. -/
structure Z2UnfixedGaugeDoobParallelUniformCouplingCertificate
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  rate : ℝ
  crossingRate_le_rate :
    z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial ≤ rate
  rate_lt_one : rate < 1
  couplingData : ∀ H : ℕ,
    Z2UnfixedGaugeDoobParallelVolumeCouplingData
      H β energyIdentity energyNontrivial hβ hEnergy
  coefficient_le_rate : ∀ H : ℕ,
    (couplingData H).coefficient ≤ rate

namespace Z2UnfixedGaugeDoobParallelUniformCouplingCertificate

variable
  {β energyIdentity energyNontrivial : ℝ}
  {hβ : 0 < β}
  {hEnergy : energyIdentity < energyNontrivial}

/-- Every actual finite-volume coupling certificate produces the corresponding
direct parallel Doob variation certificate, with no loss in its coefficient. -/
set_option maxHeartbeats 1000000 in
noncomputable def variationCertificate
    (C : Z2UnfixedGaugeDoobParallelUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy)
    (H : ℕ) :
    FiniteProductDoobParallelVariationCertificate
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le) :=
  FiniteProductKernelCouplingVariationData.toDoobParallelVariationCertificate
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le)
    (C.couplingData H).toGeneric

/-- The coupling coefficient is retained definitionally by the actual-to-generic
conversion and the generic coupling-to-variation bridge. -/
@[simp] theorem variationCertificate_coefficient
    (C : Z2UnfixedGaugeDoobParallelUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy)
    (H : ℕ) :
    (C.variationCertificate H).variationData.coefficient =
      (C.couplingData H).coefficient :=
  rfl

/-- The common coupling column-sum bound gives the existing all-volume direct
parallel variation package for the actual Perron Doob operators. -/
noncomputable def toUniformVariationCertificate
    (C : Z2UnfixedGaugeDoobParallelUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeDoobParallelUniformVariationCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  { rate := C.rate
    crossingRate_le_rate := C.crossingRate_le_rate
    rate_lt_one := C.rate_lt_one
    variationCertificate := C.variationCertificate
    coefficient_le_rate := by
      intro H
      simpa using C.coefficient_le_rate H }

/-- The actual coupling package directly yields the common weighted Doob
Rayleigh estimate. -/
theorem weightedDoobRayleigh
    (C : Z2UnfixedGaugeDoobParallelUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceHilbert H)
    (hMean :
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedMean f = 0) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedDoobQuadratic f ≤
      C.rate *
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).weightedNormSq f :=
  C.toUniformVariationCertificate.weightedDoobRayleigh H f hMean

/-- Exact terminal conversion from actual posterior coordinate couplings to the
existing spatial-sandwich stability package. -/
noncomputable def toSpatialSandwichCertificate
    (C : Z2UnfixedGaugeDoobParallelUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy) :
    Z2UnfixedGaugeSpatialSandwichUniformStabilityCertificate
      β energyIdentity energyNontrivial hβ hEnergy :=
  C.toUniformVariationCertificate.toSpatialSandwichCertificate

end Z2UnfixedGaugeDoobParallelUniformCouplingCertificate

end

end MathlibAnalytic
end MGAP4D
