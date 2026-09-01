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

/-- Model-facing data reduced to genuine positive-transfer eigenmodes.

The target realization is a dense isometric realization of the canonical
transfer spectral core into reconstructed Wightman `Ω⊥`.  Domain membership and
Hamiltonian action are required only on actual transfer eigenspace vectors. -/
structure CompactPositiveTransferLogGeneratorWightmanSpectralModeData
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive)
    (M : ExplicitWightmanOSReconstructedModel) where
  target :
    RealHilbertClosedSubspaceDenseCoreRealization
      (C := realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
        T hPositive)
      M.vacuumOrthogonal
  mode_mem :
    ∀ (mu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
      (v : eigenspace
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu),
      RealHilbertClosedSubspaceDenseCoreRealization.corestrict target
          ⟨(v : realHilbertZeroEigenspaceSupport T),
            realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_spectralCore
              T hPositive mu v⟩ ∈
        M.canonicalVacuumOrthogonalHamiltonian.domain
  mode_action :
    ∀ (mu : Eigenvalues
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
      (v : eigenspace
        (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
          Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu),
      let c :
          realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
            T hPositive :=
        ⟨(v : realHilbertZeroEigenspaceSupport T),
          realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_spectralCore
            T hPositive mu v⟩
      M.canonicalVacuumOrthogonalHamiltonian
          ⟨RealHilbertClosedSubspaceDenseCoreRealization.corestrict target c,
            mode_mem mu v⟩ =
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
          RealHilbertClosedSubspaceDenseCoreRealization.corestrict target c

/-- Mode-wise Wightman domain membership extends to every vector in the
canonical spectral core: the inverse image of the Wightman domain is a
submodule containing every mode and hence their full span. -/
theorem CompactPositiveTransferLogGeneratorWightmanSpectralModeData.target_mem
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanSpectralModeData
      T hCompact hPositive M)
    (c : realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
      T hPositive) :
    RealHilbertClosedSubspaceDenseCoreRealization.corestrict D.target c ∈
      M.canonicalVacuumOrthogonalHamiltonian.domain := by
  let targetMap :=
    (RealHilbertClosedSubspaceDenseCoreRealization.corestrict D.target).toLinearMap
  have hModes :
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
          T hPositive ≤
        (M.canonicalVacuumOrthogonalHamiltonian.domain.comap targetMap :
          Set (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
            T hPositive)) := by
    intro d hd
    change
      (d : realHilbertZeroEigenspaceSupport T) ∈
        realHilbertCompactPositiveZeroSupportLogGeneratorSpectralModeSet
          T hPositive at hd
    rcases hd with ⟨mu, v, hv⟩
    have hdEq :
        d =
          ⟨(v : realHilbertZeroEigenspaceSupport T),
            realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_spectralCore
              T hPositive mu v⟩ := by
      apply Subtype.ext
      exact hv.symm
    subst d
    exact D.mode_mem mu v
  have hSpan :
      Submodule.span ℝ
          (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
            T hPositive) ≤
        M.canonicalVacuumOrthogonalHamiltonian.domain.comap targetMap :=
    Submodule.span_le.2 hModes
  have hcSpan :
      c ∈ Submodule.span ℝ
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
          T hPositive) := by
    rw [realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet_span_eq_top]
    exact Submodule.mem_top
  exact hSpan hcSpan

end

end MathlibAnalytic
end MGAP4D
