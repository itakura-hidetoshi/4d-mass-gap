import MGAP4D.MathlibAnalytic.HamiltonianPVMSpectralExactGapValue

namespace MGAP4D
namespace MathlibAnalytic

def exactGapValueRealConcreteCandidate : ℝ :=
  hamiltonianPVMSpectralExactGapValue

theorem exactGapValueRealConcreteCandidate_above_one :
    1 < exactGapValueRealConcreteCandidate := by
  exact hamiltonian_pvm_spectral_exact_gap_value_above_one

end MathlibAnalytic
end MGAP4D
