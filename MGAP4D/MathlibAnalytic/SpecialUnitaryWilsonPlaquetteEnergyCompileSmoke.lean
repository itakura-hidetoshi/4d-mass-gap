import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergy

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

example
    {N : ℕ}
    (hN : 0 < N)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonPlaquetteEnergy N U ∈ Set.Icc (0 : ℝ) 2 :=
  specialUnitaryWilsonPlaquetteEnergy_mem_Icc hN U

example (N : ℕ) :
    Continuous (specialUnitaryWilsonPlaquetteEnergy N) :=
  continuous_specialUnitaryWilsonPlaquetteEnergy N

end

end MathlibAnalytic
end MGAP4D
