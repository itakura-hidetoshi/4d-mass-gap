import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorWightmanCanonicalSpectralCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Module End Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

local instance spectralModeCoreSupportComplete
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- Actual transfer eigenmodes, regarded as vectors of the canonical algebraic
spectral core. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    Set (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
      T hPositive) :=
  {c |
    (c : realHilbertZeroEigenspaceSupport T) ∈
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralModeSet
        T hPositive}

/-- The subtype-valued actual transfer modes span the whole canonical spectral
core.  The induction motive is deliberately phrased with an existential subtype
witness, so it is independent of the proof witnessing ambient span membership. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet_span_eq_top
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    Submodule.span ℝ
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
          T hPositive) = ⊤ := by
  let C :=
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive
  let S :=
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralModeSet T hPositive
  let SC :=
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
      T hPositive
  apply top_unique
  intro c hc
  have hx :
      (c : realHilbertZeroEigenspaceSupport T) ∈ Submodule.span ℝ S := by
    simpa only [C, S,
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore] using c.property
  have hLift :
      ∃ d : C,
        (d : realHilbertZeroEigenspaceSupport T) =
            (c : realHilbertZeroEigenspaceSupport T) ∧
          d ∈ Submodule.span ℝ SC := by
    refine Submodule.span_induction
      (p := fun x _ =>
        ∃ d : C,
          (d : realHilbertZeroEigenspaceSupport T) = x ∧
            d ∈ Submodule.span ℝ SC)
      ?_ ?_ ?_ ?_ hx
    · intro x hxS
      let d : C := ⟨x, by
        change x ∈ Submodule.span ℝ S
        exact Submodule.subset_span hxS⟩
      refine ⟨d, rfl, ?_⟩
      apply Submodule.subset_span
      change x ∈ S
      exact hxS
    · exact ⟨0, rfl, Submodule.zero_mem _⟩
    · intro x y hx hy hxLift hyLift
      rcases hxLift with ⟨dx, hdx, hdxSpan⟩
      rcases hyLift with ⟨dy, hdy, hdySpan⟩
      refine ⟨dx + dy, ?_, Submodule.add_mem _ hdxSpan hdySpan⟩
      simpa [hdx, hdy]
    · intro a x hx hxLift
      rcases hxLift with ⟨dx, hdx, hdxSpan⟩
      refine ⟨a • dx, ?_, Submodule.smul_mem _ a hdxSpan⟩
      simpa [hdx]
  rcases hLift with ⟨d, hdc, hdSpan⟩
  have hEq : d = c := by
    apply Subtype.ext
    exact hdc
  simpa [SC, hEq] using hdSpan

end

end MathlibAnalytic
end MGAP4D
