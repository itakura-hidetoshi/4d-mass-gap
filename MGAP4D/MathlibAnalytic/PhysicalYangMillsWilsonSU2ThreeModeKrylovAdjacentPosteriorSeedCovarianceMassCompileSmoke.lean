import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceMass

/-! Compile contracts for the P3 primary-seed covariance-mass bridge. -/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance p3PrimarySeedCovarianceMassCompileSmokeSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

#check physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass
#check summable_physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistance_sum_geometric_le_mass
#check physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_localFactorCovarianceMass_le

variable (H : ℕ)
variable (C q : ℝ)
variable (hC : 0 ≤ C)
variable (hq0 : 0 ≤ q)
variable (hq1 : q < 1)

example :
    (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
      C * q ^ physicalYangMillsSU2PrimaryPlaquetteSeedDistance H source) ≤
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceGeometricMass C q :=
  physicalYangMillsSU2PrimaryPlaquetteSeedDistance_sum_geometric_le_mass
    H C q hC hq0 hq1

#print axioms physicalYangMillsSU2PrimaryPlaquetteSeedDistance_sum_geometric_le_mass
#print axioms physicalYangMillsSU2PrimaryPlaquetteFarLinks_two_localFactorCovarianceMass_le

end

end MGAP4D.MathlibAnalytic
