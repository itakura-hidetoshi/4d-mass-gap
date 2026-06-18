import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonPlaquetteEnergy
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.MetricSpace.ProperSpace

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

abbrev SpecialUnitaryMatrixGroup (N : ℕ) :=
  Matrix.specialUnitaryGroup (Fin N) ℂ

/-- The induced topology makes `SU(N)` a topological group: multiplication is
inherited from matrices and inversion is conjugate transpose. -/
def specialUnitaryGroupIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (SpecialUnitaryMatrixGroup N) where
  continuous_inv :=
    continuous_induced_rng.mpr continuous_induced_dom.star
  continuous_mul :=
    continuous_induced_rng.mpr <|
      (continuous_induced_dom.comp continuous_fst).mul
        (continuous_induced_dom.comp continuous_snd)

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

/-- Every special-unitary matrix has all entries in the closed unit disk;
therefore `SU(N)` is a closed subset of a compact finite matrix product. -/
theorem specialUnitaryGroup_isCompact (N : ℕ) :
    IsCompact
      (Matrix.specialUnitaryGroup (Fin N) ℂ :
        Set (Matrix (Fin N) (Fin N) ℂ)) := by
  refine
    ((isCompact_closedBall (0 : ℂ) 1).matrix).of_isClosed_subset
      (specialUnitaryGroup_isClosed N) ?_
  intro U hU
  rw [Set.mem_matrix]
  intro i j
  rw [Metric.mem_closedBall, dist_zero_right]
  exact
    entry_norm_bound_of_unitary
      (Matrix.specialUnitaryGroup_le_unitaryGroup hU) i j

/-- Canonical compact-space receipt for `SU(N)`. -/
def specialUnitaryGroupCompactSpace (N : ℕ) :
    CompactSpace (SpecialUnitaryMatrixGroup N) :=
  isCompact_iff_compactSpace.mp (specialUnitaryGroup_isCompact N)

end

end MathlibAnalytic
end MGAP4D
