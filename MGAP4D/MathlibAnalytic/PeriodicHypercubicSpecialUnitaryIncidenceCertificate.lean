import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryDobrushinGeometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The periodic four-dimensional compact `SU(N)` Wilson system satisfies the
exact physical-link incidence bounds for side length at least three. -/
def periodicHypercubicSpecialUnitaryIncidenceCertificate
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta) :
    ContinuousCompactOrientedGaugeWilsonFourDimensionalIncidenceCertificate
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta) :=
  { edgeCard_pos := by
      exact Fintype.card_pos_iff.mpr ⟨((fun _ => 0), 0)⟩
    activeNeighborCard_le_eighteen := by
      intro target
      rw [periodicHypercubicSpecialUnitary_activeNeighbors_eq]
      exact periodicHypercubicActiveNeighbors_card_le_eighteen n target
    activeSharedPlaquetteCard_le_one := by
      intro target source hActive
      have hNe : source ≠ target :=
        (compact_oriented_mem_activePlaquetteNeighbors_iff
          (periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta hBeta).base target source).mp hActive |>.2
      rw [periodicHypercubicSpecialUnitary_sharedPlaquettes_eq]
      exact periodicHypercubicSharedPlaquettes_card_le_one
        n hn target source hNe }

end
end MathlibAnalytic
end MGAP4D
