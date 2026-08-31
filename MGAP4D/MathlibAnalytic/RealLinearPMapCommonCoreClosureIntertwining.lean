import MGAP4D.MathlibAnalytic.DenseLinearIsometryClosedSubspaceCorestriction
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set

noncomputable section

/-- The canonical map from the inverse-image domain of `B` to `B.domain`
induced by a real linear-isometric equivalence. -/
noncomputable def realLinearPMapPullbackDomainMap
    {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E ≃ₗᵢ[ℝ] F) (B : F →ₗ.[ℝ] F) :
    (B.domain.comap U.toLinearEquiv.toLinearMap) →ₗ[ℝ] B.domain where
  toFun := fun x => ⟨U (x : E), x.property⟩
  map_add' := by
    intro x y
    ext
    exact U.map_add (x : E) (y : E)
  map_smul' := by
    intro c x
    ext
    exact U.map_smul c (x : E)

/-- Pull a partially-defined real-linear operator back through a real linear-isometric
equivalence. Its domain is the exact inverse image of the target domain and its
action is conjugation by the equivalence. -/
noncomputable def realLinearPMapPullback
    {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E ≃ₗᵢ[ℝ] F) (B : F →ₗ.[ℝ] F) : E →ₗ.[ℝ] E where
  domain := B.domain.comap U.toLinearEquiv.toLinearMap
  toFun := U.symm.toLinearEquiv.toLinearMap.comp
    (B.toFun.comp (realLinearPMapPullbackDomainMap U B))

@[simp] theorem realLinearPMapPullback_domain_iff
    {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E ≃ₗᵢ[ℝ] F) (B : F →ₗ.[ℝ] F) (x : E) :
    x ∈ (realLinearPMapPullback U B).domain ↔ U x ∈ B.domain :=
  Iff.rfl

@[simp] theorem realLinearPMapPullback_apply
    {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E ≃ₗᵢ[ℝ] F) (B : F →ₗ.[ℝ] F)
    (x : (realLinearPMapPullback U B).domain) :
    realLinearPMapPullback U B x =
      U.symm (B ⟨U (x : E), x.property⟩) :=
  rfl

/-- Equality with the pullback operator is exactly an operator-level unitary
intertwining certificate. -/
noncomputable def realLinearPMapUnitaryIntertwining_of_eq_pullback
    {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F)
    (U : E ≃ₗᵢ[ℝ] F)
    (hEq : A = realLinearPMapPullback U B) :
    RealLinearPMapUnitaryIntertwining A B := by
  subst A
  exact
    { equiv := U.toLinearEquiv
      norm_map := U.norm_map
      domain_iff := fun _ => Iff.rfl
      intertwines := by
        intro x
        change B ⟨U (x : E), x.property⟩ =
          U (U.symm (B ⟨U (x : E), x.property⟩))
        simp }

/-- Common-core closure data for two closed/completed realizations of one
partially-defined operator.

The Hilbert equivalence is not an input: it is generated canonically from the
two dense isometric realizations. The operator assumptions live only at the
common algebraic core. `source_hasCore` says that closing the source operator
restricted to the source realization recovers `A`; `pullback_hasCore` says the
same after transporting `B` back by the generated equivalence. Thus neither
exact global domain transport nor global intertwining is assumed. -/
structure RealLinearPMapCommonCoreClosureIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F) where
  source : C →ₗᵢ[ℝ] E
  target : C →ₗᵢ[ℝ] F
  source_dense : DenseRange source
  target_dense : DenseRange target
  source_hasCore : A.HasCore (LinearMap.range source.toLinearMap)
  pullback_hasCore :
    (realLinearPMapPullback
      (realHilbertDenseCoreLinearIsometryEquiv
        source source_dense target target_dense) B).HasCore
      (LinearMap.range source.toLinearMap)
  source_mem : ∀ c : C, source c ∈ A.domain
  target_mem : ∀ c : C, target c ∈ B.domain
  core_intertwines : ∀ c : C,
    B ⟨target c, target_mem c⟩ =
      realHilbertDenseCoreLinearIsometryEquiv
        source source_dense target target_dense
        (A ⟨source c, source_mem c⟩)

/-- On the source realization of the common core, the pullback target operator
has exactly the same value as the source operator. -/
theorem RealLinearPMapCommonCoreClosureIntertwining.eq_on_source
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapCommonCoreClosureIntertwining (C := C) A B)
    (c : C) :
    realLinearPMapPullback
        (realHilbertDenseCoreLinearIsometryEquiv
          D.source D.source_dense D.target D.target_dense) B
        ⟨D.source c, by
          rw [realLinearPMapPullback_domain_iff]
          simpa using D.target_mem c⟩ =
      A ⟨D.source c, D.source_mem c⟩ := by
  rw [realLinearPMapPullback_apply]
  rw [realHilbertDenseCoreLinearIsometryEquiv_apply_source]
  rw [D.core_intertwines]
  simp

/-- The two common-core restrictions are literally the same `LinearPMap` after
pulling the target operator back by the generated unitary. -/
theorem RealLinearPMapCommonCoreClosureIntertwining.domRestrict_eq
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapCommonCoreClosureIntertwining (C := C) A B) :
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
  have hPBS : S ≤ PB.domain := D.pullback_hasCore.le_domain
  apply LinearPMap.ext
  · rw [LinearPMap.domRestrict_domain, LinearPMap.domRestrict_domain,
      inf_eq_left.mpr hAS, inf_eq_left.mpr hPBS]
  · intro x hxA hxPB
    have hxS : x ∈ S := by
      exact hxA.1
    rcases hxS with ⟨c, hc⟩
    have hxc : D.source c = x := by
      simpa [S] using hc
    subst x
    rw [LinearPMap.domRestrict_apply rfl, LinearPMap.domRestrict_apply rfl]
    change A ⟨D.source c, _⟩ = PB ⟨D.source c, _⟩
    symm
    exact D.eq_on_source c

/-- Mathlib's `HasCore` closure identity upgrades common-core action equality to
exact equality of the full source operator and the pullback of the target
operator. -/
theorem RealLinearPMapCommonCoreClosureIntertwining.eq_pullback
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapCommonCoreClosureIntertwining (C := C) A B) :
    A = realLinearPMapPullback
      (realHilbertDenseCoreLinearIsometryEquiv
        D.source D.source_dense D.target D.target_dense) B := by
  let S : Submodule ℝ E := LinearMap.range D.source.toLinearMap
  let PB : E →ₗ.[ℝ] E :=
    realLinearPMapPullback
      (realHilbertDenseCoreLinearIsometryEquiv
        D.source D.source_dense D.target D.target_dense) B
  calc
    A = (A.domRestrict S).closure := D.source_hasCore.closure_eq.symm
    _ = (PB.domRestrict S).closure := by
      rw [D.domRestrict_eq]
    _ = PB := D.pullback_hasCore.closure_eq

/-- A common operator core therefore generates the full unitary intertwining
receipt. This is the closure-level bridge needed to replace a generator-level
OS/Wightman assumption by algebraic-core data. -/
noncomputable def RealLinearPMapCommonCoreClosureIntertwining.toUnitaryIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapCommonCoreClosureIntertwining (C := C) A B) :
    RealLinearPMapUnitaryIntertwining A B :=
  realLinearPMapUnitaryIntertwining_of_eq_pullback A B
    (realHilbertDenseCoreLinearIsometryEquiv
      D.source D.source_dense D.target D.target_dense)
    D.eq_pullback

end

end MathlibAnalytic
end MGAP4D
