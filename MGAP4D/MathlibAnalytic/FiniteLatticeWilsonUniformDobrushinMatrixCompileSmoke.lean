import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonUniformDobrushinMatrix

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (F : FiniteLatticeWilsonApproximationFamily)
  (D : F.UniformDobrushinMatrixData)

noncomputable def finite_lattice_uniform_dobrushin_to_system_compile_smoke
    (i : F.index) :
    FiniteLatticeWilsonDobrushinMatrixData (F.system i) :=
  D.toSystemData i

example (i : F.index) (target : (F.system i).Edge) :
    (∑ source : (F.system i).Edge,
        D.influence i target source) < 1 :=
  finite_lattice_uniform_dobrushin_rowSum_lt_one F D i target

end

end MathlibAnalytic
end MGAP4D
