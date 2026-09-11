import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorSelfAdjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Module End Topology
open scoped InnerProductSpace lp LinearPMap

noncomputable section

universe u

local instance spectralCoreSupportComplete
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E) :
    CompleteSpace (realHilbertZeroEigenspaceSupport T) :=
  (realHilbertZeroEigenspaceSupport_isClosed T).completeSpace_coe

/-- The algebraic spectral-mode set on the strictly-positive support of a
compact positive real-Hilbert operator. A vector belongs to this set exactly
when it lies in one of the actual support eigenspaces. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGeneratorSpectralModeSet
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    Set (realHilbertZeroEigenspaceSupport T) :=
  {x | ∃ mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)),
    ∃ v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu,
      (v : realHilbertZeroEigenspaceSupport T) = x}

/-- The canonical algebraic spectral core is the real linear span of all actual
positive-support eigenspaces. No enumeration of the compact spectrum is
chosen. -/
noncomputable def realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive) :
    Submodule ℝ (realHilbertZeroEigenspaceSupport T) :=
  Submodule.span ℝ
    (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralModeSet T hPositive)

theorem realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_spectralCore
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hPositive : T.IsPositive)
    (mu : Eigenvalues
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)))
    (v : eigenspace
      (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
        Module.End ℝ (realHilbertZeroEigenspaceSupport T)) mu) :
    (v : realHilbertZeroEigenspaceSupport T) ∈
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive := by
  apply Submodule.subset_span
  exact ⟨mu, v, rfl⟩

/-- Every vector in the algebraic spectral span lies in the maximal logarithmic
Hamiltonian domain. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore_le_domain
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive ≤
      (realHilbertCompactPositiveZeroSupportLogGenerator
        T hCompact hPositive).domain := by
  rw [realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore]
  apply Submodule.span_le.2
  rintro x ⟨mu, v, rfl⟩
  exact
    realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_domain
      T hCompact hPositive mu v

/-- The algebraic span of actual positive-support eigenmodes is dense in the
whole positive-support Hilbert space. This is the intrinsic, enumeration-free
finite-spectral-support density statement. -/
theorem realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore_topologicalClosure_eq_top
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
      T hPositive).topologicalClosure = ⊤ := by
  classical
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let I := Eigenvalues
    (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T))
  apply top_unique
  intro x hx
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  let mode : I → realHilbertZeroEigenspaceSupport T := fun mu =>
    U.symm (lp.single 2 mu ((U x) mu))
  have hsum0 :
      HasSum
        (fun mu : I => lp.single 2 mu ((U x) mu))
        (U x) :=
    lp.hasSum_single ENNReal.ofNat_ne_top (U x)
  have hsum : HasSum mode x := by
    have hmap :=
      U.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum hsum0
    simpa only [mode, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply] using hmap
  refine mem_closure_of_tendsto hsum (Eventually.of_forall ?_)
  intro s
  apply Submodule.sum_mem
  intro mu hmu
  have hmode :
      ((U x) mu : realHilbertZeroEigenspaceSupport T) ∈
        realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
          T hPositive :=
    realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_spectralCore
      T hPositive mu ((U x) mu)
  simpa only [mode, U,
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single]
    using hmode

/-- The algebraic spectral span is a genuine Mathlib operator core for the
self-adjoint logarithmic generator on the actual positive spectral support.

The proof closes the graph by unconditional Hilbert-sum expansion. For a graph
point `(x,Hx)`, `lp.hasSum_single` expands both `x` and `Hx` into the same
spectral coordinates; every coordinate pair is already a graph point because
`H` acts on a support eigenspace by the exact weight `-log mu`. Finite partial
sums therefore lie in the restricted graph and converge to the full graph
point. -/
theorem realHilbertCompactPositiveZeroSupportLogGenerator_hasCore_spectralCore
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (hCompact : IsCompactOperator T)
    (hPositive : T.IsPositive) :
    (realHilbertCompactPositiveZeroSupportLogGenerator
      T hCompact hPositive).HasCore
      (realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore
        T hPositive) := by
  classical
  let H := realHilbertCompactPositiveZeroSupportLogGenerator T hCompact hPositive
  let C := realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore T hPositive
  let U :=
    realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv
      T hCompact hPositive
  let I := Eigenvalues
    (realHilbertZeroEigenspaceSupportRestriction T hPositive.isSymmetric :
      Module.End ℝ (realHilbertZeroEigenspaceSupport T))
  let R := H.domRestrict C
  have hC : C ≤ H.domain := by
    simpa only [C, H] using
      realHilbertCompactPositiveZeroSupportLogGeneratorSpectralCore_le_domain
        T hCompact hPositive
  have hHClosed : H.IsClosed := by
    simpa only [H] using
      realHilbertCompactPositiveZeroSupportLogGenerator_isClosed
        T hCompact hPositive
  have hRleH : R ≤ H := by
    simpa only [R] using
      (LinearPMap.domRestrict_le : H.domRestrict C ≤ H)
  have hRClosable : R.IsClosable :=
    hHClosed.isClosable.leIsClosable hRleH
  have hGraphClosure : R.graph.topologicalClosure = H.graph := by
    apply le_antisymm
    · rw [← hHClosed.submodule_topologicalClosure_eq]
      exact Submodule.topologicalClosure_mono
        (LinearPMap.le_graph_of_le hRleH)
    · intro p hp
      rw [LinearPMap.mem_graph_iff] at hp
      rcases hp with ⟨x, hxBase, hxValue⟩
      have hpEq : ((x : realHilbertZeroEigenspaceSupport T), H x) = p := by
        exact Prod.ext hxBase hxValue
      rw [← hpEq]
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      let base : I → realHilbertZeroEigenspaceSupport T := fun mu =>
        U.symm
          (lp.single 2 mu
            ((U (x : realHilbertZeroEigenspaceSupport T)) mu))
      let value : I → realHilbertZeroEigenspaceSupport T := fun mu =>
        U.symm (lp.single 2 mu ((U (H x)) mu))
      have hBase0 :
          HasSum
            (fun mu : I =>
              lp.single 2 mu
                ((U (x : realHilbertZeroEigenspaceSupport T)) mu))
            (U (x : realHilbertZeroEigenspaceSupport T)) :=
        lp.hasSum_single ENNReal.ofNat_ne_top
          (U (x : realHilbertZeroEigenspaceSupport T))
      have hBase :
          HasSum base (x : realHilbertZeroEigenspaceSupport T) := by
        have hmap :=
          U.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum hBase0
        simpa only [base, ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.symm_apply_apply] using hmap
      have hValue0 :
          HasSum
            (fun mu : I => lp.single 2 mu ((U (H x)) mu))
            (U (H x)) :=
        lp.hasSum_single ENNReal.ofNat_ne_top (U (H x))
      have hValue : HasSum value (H x) := by
        have hmap :=
          U.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum hValue0
        simpa only [value, ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv,
          LinearIsometryEquiv.symm_apply_apply] using hmap
      have hGraph :
          HasSum (fun mu : I => (base mu, value mu))
            ((x : realHilbertZeroEigenspaceSupport T), H x) :=
        hBase.prodMk hValue
      refine mem_closure_of_tendsto hGraph (Eventually.of_forall ?_)
      intro s
      apply Submodule.sum_mem
      intro mu hmu
      let v := (U (x : realHilbertZeroEigenspaceSupport T)) mu
      have hbaseEq : base mu = (v : realHilbertZeroEigenspaceSupport T) := by
        simpa only [base, v] using
          realHilbertCompactPositive_zeroEigenspaceSupport_eigenspacesHilbertSumEquiv_symm_single
            T hCompact hPositive mu v
      have hbaseC : base mu ∈ C := by
        rw [hbaseEq]
        exact
          realHilbertCompactPositiveZeroSupportLogGenerator_eigenvector_mem_spectralCore
            T hPositive mu v
      have hbaseDomain : base mu ∈ H.domain := hC hbaseC
      have hcoord := congrArg (fun z => z mu)
        (realHilbertCompactPositiveZeroSupportLogGenerator_coordinates
          T hCompact hPositive x)
      have hcoordPoint :
          (U (H x)) mu =
            realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
              (U (x : realHilbertZeroEigenspaceSupport T)) mu := by
        simpa only [H, U,
          realHilbertCompactPositiveZeroSupportLogGeneratorCoordinates_apply]
          using hcoord
      have hvalueEnergy :
          value mu =
            realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • base mu := by
        apply U.injective
        simp only [value, base, LinearIsometryEquiv.apply_symm_apply,
          LinearIsometryEquiv.map_smul]
        rw [hcoordPoint]
        apply lp.ext
        funext nu
        by_cases hnu : nu = mu
        · subst nu
          simp
        · simp [lp.single_apply, hnu]
      have hvDomain : (v : realHilbertZeroEigenspaceSupport T) ∈ H.domain := by
        rw [← hbaseEq]
        exact hbaseDomain
      let xv : H.domain := ⟨(v : realHilbertZeroEigenspaceSupport T), hvDomain⟩
      have hxv : (⟨base mu, hbaseDomain⟩ : H.domain) = xv := by
        apply Subtype.ext
        exact hbaseEq
      have hHbase :
          H ⟨base mu, hbaseDomain⟩ =
            realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • base mu := by
        calc
          H ⟨base mu, hbaseDomain⟩ = H xv := by rw [hxv]
          _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu •
              (v : realHilbertZeroEigenspaceSupport T) := by
            simpa only [H, xv] using
              realHilbertCompactPositiveZeroSupportLogGenerator_apply_eigenvector
                T hCompact hPositive mu v
          _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • base mu := by
            rw [hbaseEq]
      apply (LinearPMap.mem_graph_iff' R).2
      let y : R.domain :=
        ⟨base mu, by
          change base mu ∈ C ⊓ H.domain
          exact ⟨hbaseC, hbaseDomain⟩⟩
      refine ⟨y, ?_⟩
      apply Prod.ext
      · rfl
      · change R y = value mu
        calc
          R y = H ⟨base mu, hbaseDomain⟩ := by
            exact LinearPMap.domRestrict_apply
              (x := y) (y := ⟨base mu, hbaseDomain⟩) rfl
          _ = realHilbertZeroEigenspaceSupportLogEnergy T hPositive mu • base mu :=
            hHbase
          _ = value mu := hvalueEnergy.symm
  refine ⟨hC, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  rw [← hRClosable.graph_closure_eq_closure_graph]
  exact hGraphClosure

end

end MathlibAnalytic
end MGAP4D
