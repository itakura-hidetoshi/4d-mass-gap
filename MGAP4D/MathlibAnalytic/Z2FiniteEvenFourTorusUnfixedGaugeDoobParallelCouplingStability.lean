import MGAP4D.MathlibAnalytic.FiniteProductDoobCouplingVariation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobParallelVariationStability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite-volume coordinate-coupling data type for the actual Perron Doob
kernel, with the finite-product coordinate and spin types fixed explicitly so
that elaboration does not unfold the full lattice carrier while inferring them. -/
abbrev Z2UnfixedGaugeDoobParallelVolumeCouplingData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :=
  @FiniteProductKernelCouplingVariationData
    (FiniteEvenFourTorusSpatialLink H) Z2Gauge
    inferInstance inferInstance inferInstance inferInstance
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobKernel

/-- A proof-relevant all-volume coordinate-coupling package for the actual
Perron Doob kernels.  For every finite volume it supplies genuine couplings
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
noncomputable def variationCertificate
    (C : Z2UnfixedGaugeDoobParallelUniformCouplingCertificate
      β energyIdentity energyNontrivial hβ hEnergy)
    (H : ℕ) :
    FiniteProductDoobParallelVariationCertificate
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le) :=
  @FiniteProductKernelCouplingVariationData.toDoobParallelVariationCertificate
    (FiniteEvenFourTorusSpatialLink H) Z2Gauge
    inferInstance inferInstance inferInstance inferInstance
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ.le hEnergy.le)
    (C.couplingData H)

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
      simpa [variationCertificate] using C.coefficient_le_rate H }

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
