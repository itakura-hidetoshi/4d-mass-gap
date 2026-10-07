import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceDecay

/-! Compile contracts for the P3 primary-seed covariance bridge. -/

namespace MGAP4D.MathlibAnalytic

noncomputable section

#check physicalYangMillsSU2PrimaryPlaquetteSeed_localFactorCovariance_abs_le_seedDistancePower
#check physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_localFactorCovariance_abs_le_seedDistancePower

variable (H : ℕ)
variable (s beta : ℝ)
variable (hs : 1 ≤ s)
variable (hbeta : 0 ≤ beta)
variable
  (hcut :
    beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
        s)
variable
  (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
variable (source : PeriodicHypercubicEvenSpatialSliceLink H)
variable (sourceValue g : Matrix.specialUnitaryGroup (Fin 2) ℂ)
variable (k : Fin 4)

example
    (hFar : 2 < physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) g)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)| ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta /
        s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source :=
  physicalYangMillsSU2PrimaryPlaquetteSeed_localFactorCovariance_abs_le_seedDistancePower
    H s hs beta hbeta hcut B source sourceValue g k hFar

example
    (hFar : source ∈ physicalYangMillsSU2PrimaryPlaquetteFarLinks H 2) :
    |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
        H 2 specialUnitaryTwoWilsonRankPositive beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B (physicalYangMillsSU2PrimaryPlaquetteSeedLink H k) g)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H 2 beta B source sourceValue)| ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCanonicalFixedRightBootstrapCovariancePrefactor
          s beta /
        s ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source :=
  physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_localFactorCovariance_abs_le_seedDistancePower
    H s hs beta hbeta hcut B source sourceValue g k hFar

#print axioms physicalYangMillsSU2PrimaryPlaquetteSeed_localFactorCovariance_abs_le_seedDistancePower
#print axioms physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_localFactorCovariance_abs_le_seedDistancePower

end

end MGAP4D.MathlibAnalytic
