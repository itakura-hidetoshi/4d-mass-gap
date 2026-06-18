import MGAP4D.MathlibAnalytic.PeriodicHypercubicSignedGeometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Four coordinate axes determine exactly six unoriented coordinate planes. -/
theorem periodicHypercubicAxisPair_card :
    Fintype.card PeriodicHypercubicAxisPair = 6 := by
  native_decide

/-- A periodic four-dimensional box of side length `L` has exactly `L^4`
vertices. -/
theorem periodicHypercubicVertex_card
    (L : ℕ) [NeZero L] :
    Fintype.card (PeriodicHypercubicVertex L) = L ^ 4 := by
  simp [PeriodicHypercubicVertex, ZMod.card]

/-- A periodic four-dimensional hypercubic box of side length `L` has exactly
`6 * L^4` positively based coordinate plaquettes. -/
theorem periodicHypercubicPlaquette_card
    (L : ℕ) [NeZero L] :
    Fintype.card (PeriodicHypercubicPlaquette L) = 6 * L ^ 4 := by
  rw [Fintype.card_prod, periodicHypercubicVertex_card,
    periodicHypercubicAxisPair_card]
  omega

end

end MathlibAnalytic
end MGAP4D
