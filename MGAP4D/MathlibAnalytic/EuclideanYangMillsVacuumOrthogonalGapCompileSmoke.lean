import MGAP4D.MathlibAnalytic.EuclideanYangMillsVacuumOrthogonalGapBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Integration theorem forcing the complete dependency chain

`typed OS/Wightman model → reconstructed Hilbert space → Hamiltonian spectrum →
PVM vacuum orthogonality → Euclidean construction spine → exact positive gap`

to elaborate in one Lean target.  It is intentionally a theorem projection from
the fully stated bridge rather than an external audit marker. -/
theorem euclidean_yang_mills_vacuum_orthogonal_gap_compile_smoke
    (B : EuclideanYangMillsVacuumOrthogonalGapBridge) :
    0 < exactGapValueReal ∧
      (B.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (B.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  exact euclidean_yang_mills_nonvacuum_hamiltonian_exact_gap B

end

end MathlibAnalytic
end MGAP4D
