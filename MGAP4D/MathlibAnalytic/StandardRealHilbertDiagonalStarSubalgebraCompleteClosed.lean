import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarAlgEquivHomeomorphCauchy
import Mathlib.Topology.UniformSpace.CompleteSeparated

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Topology

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
The diagonal complexification range is complete.

A Cauchy sequence in the bundled diagonal star-subalgebra is pulled back through
its isometric homeomorphism to the complete real bounded-endomorphism space.  The
real limit is then pushed forward again.
-/
instance diagonalComplexificationStarSubalgebraCompleteSpace :
    CompleteSpace (diagonalComplexificationStarSubalgebra (H := H)) :=
  Metric.complete_of_cauchySeq_tendsto fun f hf => by
    let e := diagonalComplexificationStarAlgEquivHomeomorph (H := H)
    have hsymm : CauchySeq (fun n => e.symm (f n)) := by
      exact
        (cauchySeq_diagonalComplexificationStarAlgEquivHomeomorph_symm_iff
          (H := H) f).2 hf
    rcases cauchySeq_tendsto_of_complete hsymm with ⟨T, hT⟩
    refine ⟨e T, ?_⟩
    have hforward := (e.continuous.tendsto T).comp hT
    change Tendsto (fun n => e (e.symm (f n))) atTop (nhds (e T)) at hforward
    simpa only [e.apply_symm_apply] using hforward

/--
The diagonal complexification star-subalgebra is closed in the ambient complex
bounded-operator space.
-/
theorem diagonalComplexificationStarSubalgebra_isClosed :
    IsClosed
      (diagonalComplexificationStarSubalgebra (H := H) :
        Set (StandardRealHilbertComplexification H →L[ℂ]
          StandardRealHilbertComplexification H)) := by
  exact
    ((completeSpace_coe_iff_isComplete (s :=
      (diagonalComplexificationStarSubalgebra (H := H) :
        Set (StandardRealHilbertComplexification H →L[ℂ]
          StandardRealHilbertComplexification H)))).1
      (diagonalComplexificationStarSubalgebraCompleteSpace (H := H))).isClosed

/--
Every Cauchy sequence in the diagonal complexification range converges to the
complexification of an actual bounded real operator.
-/
theorem cauchySeq_diagonalComplexificationStarSubalgebra_exists_real_limit
    (f : ℕ → diagonalComplexificationStarSubalgebra (H := H))
    (hf : CauchySeq f) :
    ∃ T : H →L[ℝ] H,
      Tendsto f atTop
        (nhds (diagonalComplexificationStarAlgEquivHomeomorph (H := H) T)) := by
  let e := diagonalComplexificationStarAlgEquivHomeomorph (H := H)
  have hsymm : CauchySeq (fun n => e.symm (f n)) := by
    exact
      (cauchySeq_diagonalComplexificationStarAlgEquivHomeomorph_symm_iff
        (H := H) f).2 hf
  rcases cauchySeq_tendsto_of_complete hsymm with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  change Tendsto f atTop (nhds (e T))
  have hforward := (e.continuous.tendsto T).comp hT
  change Tendsto (fun n => e (e.symm (f n))) atTop (nhds (e T)) at hforward
  simpa only [e.apply_symm_apply] using hforward

/--
The real bounded operator represented by a convergent diagonal-range sequence is
unique.
-/
theorem diagonalComplexificationStarSubalgebra_real_limit_unique
    (f : ℕ → diagonalComplexificationStarSubalgebra (H := H))
    {T U : H →L[ℝ] H}
    (hT : Tendsto f atTop
      (nhds (diagonalComplexificationStarAlgEquivHomeomorph (H := H) T)))
    (hU : Tendsto f atTop
      (nhds (diagonalComplexificationStarAlgEquivHomeomorph (H := H) U))) :
    T = U := by
  apply (diagonalComplexificationStarAlgEquivHomeomorph (H := H)).injective
  exact tendsto_nhds_unique hT hU

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
