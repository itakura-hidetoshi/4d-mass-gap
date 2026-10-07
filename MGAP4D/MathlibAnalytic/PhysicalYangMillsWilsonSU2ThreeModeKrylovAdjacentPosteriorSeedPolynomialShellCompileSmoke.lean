import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedPolynomialShell

/-! Compile contracts for the P3 primary-seed polynomial shell interface. -/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

#check physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell
#check physicalYangMillsSU2PrimaryPlaquette_mem_seedDistanceShell
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_subset_fourBaseL1Shells
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_le_polynomial
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant_nonneg
#check physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_real_le_majorant
#check summable_physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant_mul_geometric

variable (H r : ℕ)

example :
    (physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r).card ≤
      12 * (2 * r + 1) ^ 3 :=
  physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_le_polynomial H r

example :
    ((physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell H r).card : ℝ) ≤
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant r :=
  physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_real_le_majorant H r

example (C q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℕ =>
      physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant m *
        (C * q ^ m)) :=
  summable_physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant_mul_geometric
    C q hq0 hq1

#print axioms physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_subset_fourBaseL1Shells
#print axioms physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_le_polynomial
#print axioms physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShell_card_real_le_majorant
#print axioms summable_physicalYangMillsSU2PrimaryPlaquetteSeedDistanceShellMajorant_mul_geometric

end

end MGAP4D.MathlibAnalytic
