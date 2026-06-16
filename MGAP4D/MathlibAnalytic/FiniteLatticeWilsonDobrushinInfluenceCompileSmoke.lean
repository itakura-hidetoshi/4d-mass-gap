import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinInfluence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable (L : FiniteLatticeWilsonSystem)

noncomputable def finite_lattice_conditional_tv_compile_smoke
    (A B : L.Configuration) (e : L.Edge) : ℝ :=
  L.singleLinkConditionalTotalVariation A B e

theorem finite_lattice_conditional_tv_nonneg_compile_smoke
    (A B : L.Configuration) (e : L.Edge) :
    0 ≤ L.singleLinkConditionalTotalVariation A B e :=
  finite_lattice_singleLinkConditionalTotalVariation_nonneg L A B e

variable (D : FiniteLatticeWilsonDobrushinInfluenceData L)

example : 0 ≤ D.dobrushinCoefficient :=
  D.dobrushinCoefficient_nonneg

example : D.dobrushinCoefficient < 1 :=
  D.dobrushinCoefficient_lt_one

variable (F : FiniteLatticeWilsonApproximationFamily)
  (U : F.UniformDobrushinInfluenceData)

noncomputable def finite_lattice_uniform_dobrushin_system_compile_smoke
    (i : F.index) :
    FiniteLatticeWilsonDobrushinInfluenceData (F.system i) :=
  U.toSystemData i

end

end MathlibAnalytic
end MGAP4D
