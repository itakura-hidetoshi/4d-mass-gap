import MGAP4D.MathlibAnalytic.DenseLinearIsometryCompletionEquiv
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorWightmanDenseCoreIntertwining
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set

noncomputable section

/-- A dense isometric realization of one normed core inside a linear subspace,
stated on the stable ambient normed carrier.

The range-density hypothesis is deliberately phrased in the ambient space.
This keeps model-facing constructions away from fragile typeclass paths on
closed spectral-support subtypes until the final corestriction step. -/
structure RealHilbertClosedSubspaceDenseCoreRealization
    {C E : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) where
  ambient : C →ₗᵢ[ℝ] E
  map_mem : ∀ x : C, ambient x ∈ S
  closure_range : closure (Set.range ambient) = (S : Set E)

/-- The underlying linear map of the corestriction, with its codomain fixed
before any normed-space synthesis is attempted. -/
noncomputable def RealHilbertClosedSubspaceDenseCoreRealization.corestrictLinearMap
    {C E : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Submodule ℝ E}
    (R : RealHilbertClosedSubspaceDenseCoreRealization (C := C) S) :
    C →ₗ[ℝ] S where
  toFun := fun x => ⟨R.ambient x, R.map_mem x⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    exact R.ambient.map_add x y
  map_smul' := by
    intro c x
    apply Subtype.ext
    exact R.ambient.map_smul c x

/-- Corestrict a stable ambient linear isometry to the subspace in which its
range actually lands. -/
noncomputable def RealHilbertClosedSubspaceDenseCoreRealization.corestrict
    {C E : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Submodule ℝ E}
    (R : RealHilbertClosedSubspaceDenseCoreRealization (C := C) S) :
    C →ₗᵢ[ℝ] S where
  toLinearMap :=
    RealHilbertClosedSubspaceDenseCoreRealization.corestrictLinearMap
      (C := C) (E := E) (S := S) R
  norm_map' := by
    intro x
    change ‖R.ambient x‖ = ‖x‖
    exact R.ambient.norm_map x

@[simp] theorem RealHilbertClosedSubspaceDenseCoreRealization.corestrict_coe
    {C E : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Submodule ℝ E}
    (R : RealHilbertClosedSubspaceDenseCoreRealization (C := C) S)
    (x : C) :
    (((RealHilbertClosedSubspaceDenseCoreRealization.corestrict
          (C := C) (E := E) (S := S) R) x : S) : E) =
      R.ambient x :=
  rfl

/-- Ambient density in a subspace becomes ordinary dense range after
corestriction. -/
theorem RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange
    {C E : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Submodule ℝ E}
    (R : RealHilbertClosedSubspaceDenseCoreRealization (C := C) S) :
    DenseRange
      (RealHilbertClosedSubspaceDenseCoreRealization.corestrict
        (C := C) (E := E) (S := S) R) := by
  rw [DenseRange, Subtype.dense_iff]
  intro y hy
  change
    (y : E) ∈ closure
      (((↑) : S → E) '' Set.range
        (RealHilbertClosedSubspaceDenseCoreRealization.corestrict
          (C := C) (E := E) (S := S) R))
  have h_range :
      (((↑) : S → E) '' Set.range
          (RealHilbertClosedSubspaceDenseCoreRealization.corestrict
            (C := C) (E := E) (S := S) R)) =
        Set.range R.ambient := by
    ext z
    constructor
    · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact
        ⟨(RealHilbertClosedSubspaceDenseCoreRealization.corestrict
            (C := C) (E := E) (S := S) R) x,
          ⟨x, rfl⟩, rfl⟩
  rw [h_range, R.closure_range]
  exact y.property

/-- If the ambient target is complete and the target subspace is closed, the
common core completion is canonically the subspace itself. -/
noncomputable def RealHilbertClosedSubspaceDenseCoreRealization.completionEquiv
    {C E : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {S : Submodule ℝ E}
    (R : RealHilbertClosedSubspaceDenseCoreRealization (C := C) S)
    (hS : IsClosed (S : Set E)) :
    UniformSpace.Completion C ≃ₗᵢ[ℝ] S := by
  letI : CompleteSpace S := hS.completeSpace_coe
  exact denseLinearIsometryCompletionEquiv
    (RealHilbertClosedSubspaceDenseCoreRealization.corestrict
      (C := C) (E := E) (S := S) R)
    (RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange
      (C := C) (E := E) (S := S) R)

/-- Two ambient dense-core realizations into closed Hilbert subspaces generate
a canonical isometric equivalence of the subspaces without requiring either
subspace's inherited normed-space instance to be named in the input data. -/
noncomputable def realHilbertClosedSubspaceDenseCoreLinearIsometryEquiv
    {C E F : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Submodule ℝ E} {T : Submodule ℝ F}
    (source : RealHilbertClosedSubspaceDenseCoreRealization (C := C) S)
    (target : RealHilbertClosedSubspaceDenseCoreRealization (C := C) T)
    (hS : IsClosed (S : Set E))
    (hT : IsClosed (T : Set F)) :
    S ≃ₗᵢ[ℝ] T :=
  (RealHilbertClosedSubspaceDenseCoreRealization.completionEquiv
      (C := C) (E := E) (S := S) source hS).symm.trans
    (RealHilbertClosedSubspaceDenseCoreRealization.completionEquiv
      (C := C) (E := F) (S := T) target hT)

/-- On the common dense core, the generated closed-subspace equivalence is
exactly the pair of original ambient realizations after corestriction. -/
@[simp] theorem realHilbertClosedSubspaceDenseCoreLinearIsometryEquiv_apply_corestrict
    {C E F : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Submodule ℝ E} {T : Submodule ℝ F}
    (source : RealHilbertClosedSubspaceDenseCoreRealization (C := C) S)
    (target : RealHilbertClosedSubspaceDenseCoreRealization (C := C) T)
    (hS : IsClosed (S : Set E))
    (hT : IsClosed (T : Set F))
    (x : C) :
    realHilbertClosedSubspaceDenseCoreLinearIsometryEquiv
        (C := C) (E := E) (F := F) (S := S) (T := T)
        source target hS hT
        ((RealHilbertClosedSubspaceDenseCoreRealization.corestrict
          (C := C) (E := E) (S := S) source) x) =
      (RealHilbertClosedSubspaceDenseCoreRealization.corestrict
        (C := C) (E := F) (S := T) target) x := by
  change
    RealHilbertClosedSubspaceDenseCoreRealization.completionEquiv
        (C := C) (E := F) (S := T) target hT
        ((RealHilbertClosedSubspaceDenseCoreRealization.completionEquiv
            (C := C) (E := E) (S := S) source hS).symm
          ((RealHilbertClosedSubspaceDenseCoreRealization.corestrict
            (C := C) (E := E) (S := S) source) x)) =
      (RealHilbertClosedSubspaceDenseCoreRealization.corestrict
        (C := C) (E := F) (S := T) target) x
  rw [← denseLinearIsometryCompletionEquiv_apply_coe
    (RealHilbertClosedSubspaceDenseCoreRealization.corestrict
      (C := C) (E := E) (S := S) source)
    (RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange
      (C := C) (E := E) (S := S) source) x]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  exact denseLinearIsometryCompletionEquiv_apply_coe
    (RealHilbertClosedSubspaceDenseCoreRealization.corestrict
      (C := C) (E := F) (S := T) target)
    (RealHilbertClosedSubspaceDenseCoreRealization.corestrict_denseRange
      (C := C) (E := F) (S := T) target) x

/-- Operator-specific data on two closed subspaces, while both dense core
realizations are supplied on their stable ambient carriers. -/
structure RealLinearPMapClosedSubspaceDenseCoreIntertwining
    {C E F : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Submodule ℝ E} {T : Submodule ℝ F}
    (hS : IsClosed (S : Set E))
    (hT : IsClosed (T : Set F))
    (A : S →ₗ.[ℝ] S) (B : T →ₗ.[ℝ] T) where
  source : RealHilbertClosedSubspaceDenseCoreRealization (C := C) S
  target : RealHilbertClosedSubspaceDenseCoreRealization (C := C) T
  domain_iff : ∀ x : S,
    x ∈ A.domain ↔
      realHilbertClosedSubspaceDenseCoreLinearIsometryEquiv
        (C := C) (E := E) (F := F) (S := S) (T := T)
        source target hS hT x ∈ B.domain
  intertwines : ∀ x : A.domain,
    B ⟨realHilbertClosedSubspaceDenseCoreLinearIsometryEquiv
          (C := C) (E := E) (F := F) (S := S) (T := T)
          source target hS hT (x : S),
        (domain_iff (x : S)).1 x.property⟩ =
      realHilbertClosedSubspaceDenseCoreLinearIsometryEquiv
        (C := C) (E := E) (F := F) (S := S) (T := T)
        source target hS hT (A x)

/-- Ambient closed-subspace dense-core data generate the already-canonical
operator-level unitary intertwining certificate. -/
noncomputable def RealLinearPMapClosedSubspaceDenseCoreIntertwining.toUnitaryIntertwining
    {C E F : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Submodule ℝ E} {T : Submodule ℝ F}
    {hS : IsClosed (S : Set E)}
    {hT : IsClosed (T : Set F)}
    {A : S →ₗ.[ℝ] S} {B : T →ₗ.[ℝ] T}
    (D : RealLinearPMapClosedSubspaceDenseCoreIntertwining
      (C := C) (E := E) (F := F) hS hT A B) :
    RealLinearPMapUnitaryIntertwining A B := by
  let U := realHilbertClosedSubspaceDenseCoreLinearIsometryEquiv
    (C := C) (E := E) (F := F) (S := S) (T := T)
    D.source D.target hS hT
  exact
    { equiv := U.toLinearEquiv
      norm_map := U.norm_map
      domain_iff := D.domain_iff
      intertwines := D.intertwines }

/-- Consequently the actual nonzero point-energy sets agree, with no globally
chosen subspace equivalence as independent input. -/
theorem realLinearPMapPointEnergySet_eq_of_closedSubspaceDenseCoreIntertwining
    {C E F : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Submodule ℝ E} {T : Submodule ℝ F}
    {hS : IsClosed (S : Set E)}
    {hT : IsClosed (T : Set F)}
    (A : S →ₗ.[ℝ] S) (B : T →ₗ.[ℝ] T)
    (D : RealLinearPMapClosedSubspaceDenseCoreIntertwining
      (C := C) (E := E) (F := F) hS hT A B) :
    realLinearPMapPointEnergySet A = realLinearPMapPointEnergySet B :=
  realLinearPMapPointEnergySet_eq_of_unitaryIntertwining
    A B
    (RealLinearPMapClosedSubspaceDenseCoreIntertwining.toUnitaryIntertwining
      (C := C) (E := E) (F := F) (S := S) (T := T) D)

end

end MathlibAnalytic
end MGAP4D
