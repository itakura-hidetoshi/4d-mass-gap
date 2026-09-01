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
spectral core.  The ambient spectral core is already the span of these modes;
this set records the corresponding generators on the subtype carrier used by
the transfer/Wightman common-core theorem. -/
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
core.  This is the precise algebraic statement allowing operator identities to
be checked only on genuine eigenspaces and then extended by linearity. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet_span_eq_top
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    Submodule.span ℝ
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
          T hPositive) = ⊤ := by
  apply top_unique
  intro c hc
  rcases c with ⟨x, hx⟩
  change
    x ∈ Submodule.span ℝ
      (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralModeSet
        T hPositive) at hx
  have hLift :
      ∃ hx' : x ∈
          realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
            T hPositive,
        (⟨x, hx'⟩ :
          realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
            T hPositive) ∈
          Submodule.span ℝ
            (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
              T hPositive) := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
        let hyCore : y ∈
            realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
              T hPositive :=
          Submodule.subset_span hy
        refine ⟨hyCore, ?_⟩
        apply Submodule.subset_span
        exact hy
    | zero =>
        refine ⟨Submodule.zero_mem _, ?_⟩
        simpa using
          (Submodule.zero_mem
            (Submodule.span ℝ
              (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
                T hPositive)))
    | add u v _hu _hv huLift hvLift =>
        rcases huLift with ⟨huCore, huSpan⟩
        rcases hvLift with ⟨hvCore, hvSpan⟩
        refine ⟨Submodule.add_mem _ huCore hvCore, ?_⟩
        simpa using
          (Submodule.add_mem
            (Submodule.span ℝ
              (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
                T hPositive)) huSpan hvSpan)
    | smul a u _hu huLift =>
        rcases huLift with ⟨huCore, huSpan⟩
        refine ⟨Submodule.smul_mem _ a huCore, ?_⟩
        simpa using
          (Submodule.smul_mem
            (Submodule.span ℝ
              (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
                T hPositive)) a huSpan)
  rcases hLift with ⟨hx', hspan⟩
  simpa using hspan

/-- Model-facing data reduced to genuine positive-transfer eigenmodes.

The Wightman realization is still a dense isometric realization of the
canonical transfer spectral core.  Domain membership and Hamiltonian action,
however, are required only on actual eigenspace vectors.  On a transfer mode of
eigenvalue `mu`, the Wightman Hamiltonian is required to act by the exact
logarithmic energy `-log mu` (through the repository's canonical
`realHilbertZeroEigenspaceSupportLogEnergy`).

Linearity of the Wightman graph and the fact that these modes span the
canonical spectral core will generate all remaining core-domain and
intertwining obligations. -/
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
canonical spectral core.  The proof is purely algebraic: the inverse image of
the Wightman operator domain under the target realization is a submodule and
contains every actual transfer mode, hence it contains their full span. -/
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

/-- Wightman action on the canonical spectral core as an ordinary linear map.
The previous theorem supplies the codomain restriction to the Hamiltonian
domain, so the partially-defined Hamiltonian can now be composed linearly on
the whole core. -/
noncomputable def CompactPositiveTransferLogGeneratorWightmanSpectralModeData.wightmanCoreAction
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanSpectralModeData
      T hCompact hPositive M) :
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive
      →ₗ[ℝ] M.vacuumOrthogonal :=
  M.canonicalVacuumOrthogonalHamiltonian.toFun.comp
    ((RealHilbertClosedSubspaceDenseCoreRealization.corestrict D.target).toLinearMap.codRestrict
      M.canonicalVacuumOrthogonalHamiltonian.domain D.target_mem)

/-- Transfer logarithmic-generator action on the same canonical core, transported
through the dense-core equivalence generated by the source inclusion and the
Wightman realization. -/
noncomputable def CompactPositiveTransferLogGeneratorWightmanSpectralModeData.transferCoreAction
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanSpectralModeData
      T hCompact hPositive M) :
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive
      →ₗ[ℝ] M.vacuumOrthogonal :=
  let source :=
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
      T hPositive
  let sourceDense :=
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion_denseRange
      T hCompact hPositive
  let target :=
    RealHilbertClosedSubspaceDenseCoreRealization.corestrict D.target
  let targetDense :=
    RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange D.target
  let H :=
    realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let sourceHasCore :=
    realHilbertCompactPositiveZeroSupportLogGenerator_hasCore_canonicalSpectralCoreRange
      T hCompact hPositive
  let sourceDomainMap :
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive
        →ₗ[ℝ] H.domain :=
    source.toLinearMap.codRestrict H.domain
      (fun c => sourceHasCore.le_domain ⟨c, rfl⟩)
  (realHilbertDenseCoreLinearIsometryEquiv
      source sourceDense target targetDense).toLinearMap.comp
    (H.toFun.comp sourceDomainMap)

/-- The two core action maps agree on every genuine transfer eigenmode. -/
theorem CompactPositiveTransferLogGeneratorWightmanSpectralModeData.coreAction_eqOn_modes
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanSpectralModeData
      T hCompact hPositive M) :
    Set.EqOn D.wightmanCoreAction D.transferCoreAction
      (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet
        T hPositive) := by
  intro c hc
  change
    (c : realHilbertZeroEigenspaceSupport T) ∈
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralModeSet
        T hPositive at hc
  rcases hc with ⟨mu, v, hv⟩
  have hcEq :
      c =
        ⟨(v : realHilbertZeroEigenspaceSupport T),
          realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_spectralCore
            T hPositive mu v⟩ := by
    apply Subtype.ext
    exact hv.symm
  subst c
  let cMode :
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive :=
    ⟨(v : realHilbertZeroEigenspaceSupport T),
      realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_spectralCore
        T hPositive mu v⟩
  let source :=
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
      T hPositive
  let sourceDense :=
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion_denseRange
      T hCompact hPositive
  let target :=
    RealHilbertClosedSubspaceDenseCoreRealization.corestrict D.target
  let targetDense :=
    RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange D.target
  let U := realHilbertDenseCoreLinearIsometryEquiv
    source sourceDense target targetDense
  let H := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  have hHMode :
      H ⟨source cMode,
        (realHilbertCompactPositiveZeroSupportLogGenerator_hasCore_canonicalSpectralCoreRange
          T hCompact hPositive).le_domain ⟨cMode, rfl⟩⟩ =
        realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • source cMode := by
    simpa only [H, source, cMode,
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion] using
      realHilbertCompactPositiveZeroSupportLogGenerator_apply_eigenvector
        T hCompact hPositive mu v
  calc
    D.wightmanCoreAction cMode =
        M.canonicalVacuumOrthogonalHamiltonian
          ⟨target cMode, D.target_mem cMode⟩ := by
      rfl
    _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
        target cMode := by
      simpa only [cMode, target] using D.mode_action mu v
    _ = U
        (realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
          source cMode) := by
      rw [U.map_smul]
      rw [realHilbertDenseCoreLinearIsometryEquiv_apply_source]
    _ = U
        (H ⟨source cMode,
          (realHilbertCompactPositiveZeroSupportLogGenerator_hasCore_canonicalSpectralCoreRange
            T hCompact hPositive).le_domain ⟨cMode, rfl⟩⟩) := by
      rw [hHMode]
    _ = D.transferCoreAction cMode := by
      rfl

/-- Since the genuine transfer modes span the canonical core, their Wightman
Hamiltonian identities determine the full core action. -/
theorem CompactPositiveTransferLogGeneratorWightmanSpectralModeData.coreAction_eq
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanSpectralModeData
      T hCompact hPositive M) :
    D.wightmanCoreAction = D.transferCoreAction := by
  apply LinearMap.ext
  intro c
  apply LinearMap.eqOn_span' D.coreAction_eqOn_modes
  rw [realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreModeSet_span_eq_top]
  exact Submodule.mem_top

/-- Mode-wise logarithmic energy identities therefore generate the exact
common-core intertwining equation required by self-adjoint maximality. -/
theorem CompactPositiveTransferLogGeneratorWightmanSpectralModeData.core_intertwines
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
    M.canonicalVacuumOrthogonalHamiltonian
        ⟨RealHilbertClosedSubspaceDenseCoreRealization.corestrict D.target c,
          D.target_mem c⟩ =
      realHilbertDenseCoreLinearIsometryEquiv
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
          T hPositive)
        (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion_denseRange
          T hCompact hPositive)
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict D.target)
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange D.target)
        (realHilbertCompactPositiveZeroSupportLogGenerator
          T hCompact hPositive
          ⟨realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCoreInclusion
              T hPositive c,
            (realHilbertCompactPositiveZeroSupportLogGenerator_hasCore_canonicalSpectralCoreRange
              T hCompact hPositive).le_domain ⟨c, rfl⟩⟩) := by
  have h := LinearMap.congr_fun D.coreAction_eq c
  exact h

/-- Spectral-mode data generate the canonical-spectral-core package from PR
#3020.  Thus all global unitary/domain/point-spectrum consequences remain
unchanged while the hard operator identity is now localized to actual transfer
eigenmodes. -/
noncomputable def CompactPositiveTransferLogGeneratorWightmanSpectralModeData.toCanonicalSpectralCoreData
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanSpectralModeData
      T hCompact hPositive M) :
    CompactPositiveTransferLogGeneratorWightmanCanonicalSpectralCoreData
      T hCompact hPositive M where
  target := D.target
  target_mem := D.target_mem
  core_intertwines := D.core_intertwines

/-- Consequently mode-wise realization data alone generate the full unitary
transfer/Wightman intertwining. -/
noncomputable def CompactPositiveTransferLogGeneratorWightmanSpectralModeData.toUnitaryIntertwining
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {T : E →L[ℝ] E}
    {hCompact : IsCompactOperator T}
    {hPositive : T.IsPositive}
    {M : ExplicitWightmanOSReconstructedModel}
    (D : CompactPositiveTransferLogGeneratorWightmanSpectralModeData
      T hCompact hPositive M) :
    RealLinearPMapUnitaryIntertwining
      (realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive)
      M.canonicalVacuumOrthogonalHamiltonian :=
  D.toCanonicalSpectralCoreData.toUnitaryIntertwining

end

end MathlibAnalytic
end MGAP4D
