import MGAP4D.MathlibAnalytic.RealLinearPMapCommonCoreClosureIntertwining
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

/-- Pullback through a real linear isometric equivalence preserves self-adjointness.

This is the unbounded-operator version of unitary conjugation invariance.  The
proof stays inside Mathlib's `LinearPMap` API: density is transported by the
homeomorphism, formal symmetry by preservation of the real inner product, and
adjoint-domain maximality by transporting the defining adjoint pairing. -/
theorem realLinearPMapPullback_isSelfAdjoint
    {E F : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (U : E ≃ₗᵢ[ℝ] F)
    (B : F →ₗ.[ℝ] F)
    (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (realLinearPMapPullback U B) := by
  let PB : E →ₗ.[ℝ] E := realLinearPMapPullback U B
  have hDenseB : Dense (B.domain : Set F) := hB.dense_domain
  have hDensePB : Dense (PB.domain : Set E) := by
    change Dense (U ⁻¹' (B.domain : Set F))
    rw [dense_iff_closure_eq]
    change closure (U.toHomeomorph ⁻¹' (B.domain : Set F)) = Set.univ
    rw [← U.toHomeomorph.preimage_closure]
    rw [hDenseB.closure_eq]
    simp
  have hBFormal : B.IsFormalAdjoint B := by
    have hFormal := LinearPMap.adjoint_isFormalAdjoint hDenseB
    rw [LinearPMap.isSelfAdjoint_def.mp hB] at hFormal
    exact hFormal
  have hPBFormal : PB.IsFormalAdjoint PB := by
    intro x y
    let xB : B.domain := ⟨U (x : E), x.property⟩
    let yB : B.domain := ⟨U (y : E), y.property⟩
    calc
      inner ℝ (PB x) (y : E) =
          inner ℝ (U (PB x)) (U (y : E)) :=
        (U.inner_map_map _ _).symm
      _ = inner ℝ (B xB) (U (y : E)) := by
        rw [realLinearPMapPullback_apply]
        simp only [U.apply_symm_apply]
        rfl
      _ = inner ℝ (B xB) (yB : F) := rfl
      _ = inner ℝ (xB : F) (B yB) := hBFormal xB yB
      _ = inner ℝ (U (x : E)) (B yB) := rfl
      _ = inner ℝ (U (x : E)) (U (PB y)) := by
        rw [realLinearPMapPullback_apply]
        simp only [U.apply_symm_apply]
        rfl
      _ = inner ℝ (x : E) (PB y) := U.inner_map_map _ _
  have hPB_le_adjoint : PB ≤ PB.adjoint :=
    hPBFormal.le_adjoint hDensePB
  have hAdjoint_le_PB : PB.adjoint ≤ PB := by
    refine ⟨?_, ?_⟩
    · intro y hy
      let yAdjoint : PB.adjoint.domain := ⟨y, hy⟩
      have hyTargetAdjoint : U y ∈ B.adjoint.domain := by
        apply LinearPMap.mem_adjoint_domain_of_exists
        refine ⟨U (PB.adjoint yAdjoint), ?_⟩
        intro z
        let x : PB.domain :=
          ⟨U.symm (z : F), by
            change U (U.symm (z : F)) ∈ B.domain
            simpa using z.property⟩
        have hxU : U (x : E) = (z : F) := by
          simp [x]
        let z' : B.domain := ⟨U (x : E), x.property⟩
        have hz' : z' = z := by
          apply Subtype.ext
          exact hxU
        calc
          inner ℝ (U (PB.adjoint yAdjoint)) (z : F) =
              inner ℝ (U (PB.adjoint yAdjoint)) (U (x : E)) := by
            rw [hxU]
          _ = inner ℝ (PB.adjoint yAdjoint) (x : E) :=
            U.inner_map_map _ _
          _ = inner ℝ (y : E) (PB x) :=
            LinearPMap.adjoint_isFormalAdjoint hDensePB yAdjoint x
          _ = inner ℝ (U (y : E)) (U (PB x)) :=
            (U.inner_map_map _ _).symm
          _ = inner ℝ (U (y : E)) (B z) := by
            congr 1
            rw [realLinearPMapPullback_apply]
            simp only [U.apply_symm_apply]
            change B z' = B z
            rw [hz']
      have hyTarget : U y ∈ B.domain := by
        simpa only [LinearPMap.isSelfAdjoint_def.mp hB] using hyTargetAdjoint
      exact (realLinearPMapPullback_domain_iff U B y).2 hyTarget
    · intro x y hxy
      exact (hPB_le_adjoint.2 hxy.symm).symm
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hAdjoint_le_PB hPB_le_adjoint

/-- A closed `LinearPMap` is equal to its Mathlib graph closure. -/
theorem realLinearPMap_closure_eq_self_of_isClosed
    {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →ₗ.[ℝ] F)
    (hA : A.IsClosed) :
    A.closure = A := by
  apply LinearPMap.eq_of_eq_graph
  rw [← hA.isClosable.graph_closure_eq_closure_graph]
  exact hA.submodule_topologicalClosure_eq

/-- Self-adjoint partially-defined operators are maximal among self-adjoint
extensions.

If `A ≤ B` and both operators are self-adjoint, symmetry of `B` makes `B` a
formal adjoint extension of `A`; maximality of the Mathlib adjoint then forces
`B ≤ A† = A`. -/
theorem realLinearPMap_eq_of_le_of_isSelfAdjoint
    {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A B : E →ₗ.[ℝ] E)
    (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B)
    (hAB : A ≤ B) :
    A = B := by
  have hDenseB : Dense (B.domain : Set E) := hB.dense_domain
  have hBFormal : B.IsFormalAdjoint B := by
    have hFormal := LinearPMap.adjoint_isFormalAdjoint hDenseB
    rw [LinearPMap.isSelfAdjoint_def.mp hB] at hFormal
    exact hFormal
  have hAFormalB : A.IsFormalAdjoint B := by
    intro x y
    let xb : B.domain := ⟨(x : E), hAB.1 x.property⟩
    calc
      inner ℝ (A x) (y : E) = inner ℝ (B xb) (y : E) := by
        rw [hAB.2 (x := x) (y := xb) rfl]
      _ = inner ℝ (xb : E) (B y) := hBFormal xb y
      _ = inner ℝ (x : E) (B y) := rfl
  have hBA : B ≤ A.adjoint :=
    hAFormalB.le_adjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hBA
  exact le_antisymm hAB hBA

/-- Common-core data in which the second `HasCore` hypothesis is generated,
not assumed.

Two dense isometric realizations determine the unitary `U`.  The source
operator is assumed self-adjoint and to have the realized algebraic core as a
Mathlib `HasCore`; the target operator is only assumed self-adjoint.  Exact
core action agreement then makes the source core restriction a suboperator of
`U⁻¹ B U`.  Closing that restriction gives `A ≤ U⁻¹ B U`, while self-adjoint
maximality upgrades the inclusion to equality.

Compared with `RealLinearPMapCommonCoreClosureIntertwining`, there is no
independent `pullback_hasCore` field and no global domain/intertwining field. -/
structure RealLinearPMapSelfAdjointCommonCoreIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F) where
  source : C →ₗᵢ[ℝ] E
  target : C →ₗᵢ[ℝ] F
  source_dense : DenseRange source
  target_dense : DenseRange target
  source_selfAdjoint : IsSelfAdjoint A
  target_selfAdjoint : IsSelfAdjoint B
  source_hasCore : A.HasCore (LinearMap.range source.toLinearMap)
  target_mem : ∀ c : C, target c ∈ B.domain
  core_intertwines : ∀ c : C,
    B ⟨target c, target_mem c⟩ =
      realHilbertDenseCoreLinearIsometryEquiv
        source source_dense target target_dense
        (A ⟨source c, source_hasCore.le_domain ⟨c, rfl⟩⟩)

/-- Membership of the source realization in the source operator domain is
already contained in `source_hasCore`; it is not an extra hypothesis. -/
theorem RealLinearPMapSelfAdjointCommonCoreIntertwining.source_mem
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapSelfAdjointCommonCoreIntertwining (C := C) A B)
    (c : C) :
    D.source c ∈ A.domain :=
  D.source_hasCore.le_domain ⟨c, rfl⟩

/-- The generated unitary sends the source realization of every core vector to
the target realization. -/
theorem RealLinearPMapSelfAdjointCommonCoreIntertwining.eq_on_source
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapSelfAdjointCommonCoreIntertwining (C := C) A B)
    (c : C) :
    realLinearPMapPullback
        (realHilbertDenseCoreLinearIsometryEquiv
          D.source D.source_dense D.target D.target_dense) B
        ⟨D.source c, by
          rw [realLinearPMapPullback_domain_iff]
          simpa only [realHilbertDenseCoreLinearIsometryEquiv_apply_source] using
            D.target_mem c⟩ =
      A ⟨D.source c, D.source_mem c⟩ := by
  let U : E ≃ₗᵢ[ℝ] F :=
    realHilbertDenseCoreLinearIsometryEquiv
      D.source D.source_dense D.target D.target_dense
  change realLinearPMapPullback U B ⟨D.source c, _⟩ =
    A ⟨D.source c, D.source_mem c⟩
  rw [realLinearPMapPullback_apply]
  apply U.injective
  simp only [U.apply_symm_apply]
  simpa only [U, realHilbertDenseCoreLinearIsometryEquiv_apply_source] using
    D.core_intertwines c

/-- The source restriction to the realized algebraic core equals the pullback
target restriction on that same core. -/
theorem RealLinearPMapSelfAdjointCommonCoreIntertwining.domRestrict_eq
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapSelfAdjointCommonCoreIntertwining (C := C) A B) :
    A.domRestrict (LinearMap.range D.source.toLinearMap) =
      (realLinearPMapPullback
        (realHilbertDenseCoreLinearIsometryEquiv
          D.source D.source_dense D.target D.target_dense) B).domRestrict
        (LinearMap.range D.source.toLinearMap) := by
  let S : Submodule ℝ E := LinearMap.range D.source.toLinearMap
  let U : E ≃ₗᵢ[ℝ] F :=
    realHilbertDenseCoreLinearIsometryEquiv
      D.source D.source_dense D.target D.target_dense
  let PB : E →ₗ.[ℝ] E := realLinearPMapPullback U B
  have hAS : S ≤ A.domain := D.source_hasCore.le_domain
  have hPBS : S ≤ PB.domain := by
    rintro x ⟨c, hc⟩
    have hxc : D.source c = x := by
      simpa [S] using hc
    subst x
    rw [realLinearPMapPullback_domain_iff]
    change U (D.source c) ∈ B.domain
    simpa only [U, realHilbertDenseCoreLinearIsometryEquiv_apply_source] using
      D.target_mem c
  apply LinearPMap.ext
  · rw [LinearPMap.domRestrict_domain, LinearPMap.domRestrict_domain,
      inf_eq_left.mpr hAS, inf_eq_left.mpr hPBS]
  · intro x hxA hxPB
    have hxS : x ∈ S := hxA.1
    rcases hxS with ⟨c, hc⟩
    have hxc : D.source c = x := by
      simpa [S] using hc
    subst x
    have hsourceS : D.source c ∈ S := hxA.1
    calc
      A.domRestrict S ⟨D.source c, hxA⟩ =
          A ⟨D.source c, D.source_mem c⟩ :=
        LinearPMap.domRestrict_apply
          (x := ⟨D.source c, hxA⟩)
          (y := ⟨D.source c, D.source_mem c⟩) rfl
      _ = PB ⟨D.source c, hPBS hsourceS⟩ := by
        symm
        simpa only [PB, U] using D.eq_on_source c
      _ = PB.domRestrict S ⟨D.source c, hxPB⟩ := by
        symm
        exact LinearPMap.domRestrict_apply
          (x := ⟨D.source c, hxPB⟩)
          (y := ⟨D.source c, hPBS hsourceS⟩) rfl

/-- The source core restriction is contained in the pulled-back target operator. -/
theorem RealLinearPMapSelfAdjointCommonCoreIntertwining.domRestrict_le_pullback
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapSelfAdjointCommonCoreIntertwining (C := C) A B) :
    A.domRestrict (LinearMap.range D.source.toLinearMap) ≤
      realLinearPMapPullback
        (realHilbertDenseCoreLinearIsometryEquiv
          D.source D.source_dense D.target D.target_dense) B := by
  rw [D.domRestrict_eq]
  exact LinearPMap.domRestrict_le

/-- One source `HasCore`, self-adjointness on both completed carriers, and exact
core action agreement force equality of the full operators after unitary
pullback.  The target `HasCore` condition from the previous closure bridge is a
theorem, not an assumption, in this self-adjoint setting. -/
theorem RealLinearPMapSelfAdjointCommonCoreIntertwining.eq_pullback
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapSelfAdjointCommonCoreIntertwining (C := C) A B) :
    A = realLinearPMapPullback
      (realHilbertDenseCoreLinearIsometryEquiv
        D.source D.source_dense D.target D.target_dense) B := by
  let S : Submodule ℝ E := LinearMap.range D.source.toLinearMap
  let U : E ≃ₗᵢ[ℝ] F :=
    realHilbertDenseCoreLinearIsometryEquiv
      D.source D.source_dense D.target D.target_dense
  let PB : E →ₗ.[ℝ] E := realLinearPMapPullback U B
  have hPBSelf : IsSelfAdjoint PB := by
    simpa only [PB] using
      realLinearPMapPullback_isSelfAdjoint U B D.target_selfAdjoint
  have hClosureLe : (A.domRestrict S).closure ≤ PB.closure := by
    apply hPBSelf.isClosed.isClosable.closure_mono
    simpa only [S, PB, U] using D.domRestrict_le_pullback
  have hAlePB : A ≤ PB := by
    rw [D.source_hasCore.closure_eq,
      realLinearPMap_closure_eq_self_of_isClosed PB hPBSelf.isClosed] at hClosureLe
    exact hClosureLe
  have hEq : A = PB :=
    realLinearPMap_eq_of_le_of_isSelfAdjoint
      A PB D.source_selfAdjoint hPBSelf hAlePB
  simpa only [PB, U] using hEq

/-- Self-adjoint common-core data generate the full unitary intertwining receipt
used by the transfer/Wightman spectral bridge, without a second graph-core
assumption. -/
noncomputable def RealLinearPMapSelfAdjointCommonCoreIntertwining.toUnitaryIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapSelfAdjointCommonCoreIntertwining (C := C) A B) :
    RealLinearPMapUnitaryIntertwining A B :=
  realLinearPMapUnitaryIntertwining_of_eq_pullback A B
    (realHilbertDenseCoreLinearIsometryEquiv
      D.source D.source_dense D.target D.target_dense)
    D.eq_pullback

end

end MathlibAnalytic
end MGAP4D
