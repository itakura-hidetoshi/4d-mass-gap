import MGAP4D.MathlibAnalytic.FiniteWilsonPairingCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_wilson_pairing_core_compile_smoke
    (f g : L.Configuration → ℝ) : ℝ :=
  L.gibbsPairingReal f g

theorem finite_wilson_pairing_symmetry_compile_smoke
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f g = L.gibbsPairingReal g f :=
  finite_lattice_gibbsPairingReal_symm L f g

end

end MathlibAnalytic
end MGAP4D
