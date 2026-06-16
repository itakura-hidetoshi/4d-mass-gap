import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinMatrix

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)
  (D : FiniteLatticeWilsonDobrushinMatrixData L)

example (target source : L.Edge) :
    0 ≤ D.influence target source :=
  D.influence_nonneg target source

example (target : L.Edge) :
    (∑ source : L.Edge, D.influence target source) < 1 :=
  finite_lattice_dobrushin_rowSum_lt_one L D target

end

end MathlibAnalytic
end MGAP4D
