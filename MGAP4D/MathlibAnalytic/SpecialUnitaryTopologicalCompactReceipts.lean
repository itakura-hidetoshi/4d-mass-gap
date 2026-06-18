import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergy
import Mathlib.Topology.Algebra.Star.Unitary

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

abbrev SpecialUnitaryMatrixGroup (N : ℕ) :=
  Matrix.specialUnitaryGroup (Fin N) ℂ

/-- Inversion on `SU(N)` is continuous because it is conjugate transpose. -/
def specialUnitaryGroupContinuousInv (N : ℕ) :
    ContinuousInv (SpecialUnitaryMatrixGroup N) where
  continuous_inv :=
    continuous_induced_rng.mpr continuous_subtype_val.star

/-- The induced topology makes `SU(N)` a topological group. -/
def specialUnitaryGroupIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup N) := by
  letI : ContinuousInv (SpecialUnitaryMatrixGroup N) :=
    specialUnitaryGroupContinuousInv N
  infer_instance

/-- `SU(N)` is closed in the ambient complex matrix space. -/
theorem specialUnitaryGroup_isClosed (N : ℕ) :
    IsClosed
      (Matrix.specialUnitaryGroup (Fin N) ℂ :
        Set (Matrix (Fin N) (Fin N) ℂ)) := by
  have hUnitary :
      IsClosed
        (Matrix.unitaryGroup (Fin N) ℂ :
          Set (Matrix (Fin N) (Fin N) ℂ)) :=
    isClosed_unitary
  have hDet :
      IsClosed
        {U : Matrix (Fin N) (Fin N) ℂ | Matrix.det U = 1} :=
    isClosed_singleton.preimage continuous_id.matrix_det
  rw [show
      (Matrix.specialUnitaryGroup (Fin N) ℂ :
        Set (Matrix (Fin N) (Fin N) ℂ)) =
      (Matrix.unitaryGroup (Fin N) ℂ :
        Set (Matrix (Fin N) (Fin N) ℂ)) ∩
        {U : Matrix (Fin N) (Fin N) ℂ | Matrix.det U = 1} by
    ext U
    rfl]
  exact hUnitary.inter hDet

end

end MathlibAnalytic
end MGAP4D
