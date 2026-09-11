import MGAP4D.MathlibAnalytic.DenseLinearIsometryCompletionEquiv
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorWightmanIntertwining
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Function Set

noncomputable section

/-- Two dense isometric realizations of one common real normed core determine a
canonical linear-isometric equivalence between the two complete carriers.
Both carriers are identified with Mathlib's canonical completion of the common
core, so no independently chosen global equivalence is required. -/
noncomputable def realHilbertDenseCoreLinearIsometryEquiv
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (source : C →ₗᵢ[ℝ] E) (source_dense : DenseRange source)
    (target : C →ₗᵢ[ℝ] F) (target_dense : DenseRange target) :
    E ≃ₗᵢ[ℝ] F :=
  (denseLinearIsometryCompletionEquiv source source_dense).symm.trans
    (denseLinearIsometryCompletionEquiv target target_dense)

/-- On the common dense core, the induced equivalence is exactly the change of
realization from the source copy to the target copy. -/
@[simp] theorem realHilbertDenseCoreLinearIsometryEquiv_apply_source
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (source : C →ₗᵢ[ℝ] E) (source_dense : DenseRange source)
    (target : C →ₗᵢ[ℝ] F) (target_dense : DenseRange target)
    (x : C) :
    realHilbertDenseCoreLinearIsometryEquiv
        source source_dense target target_dense (source x) = target x := by
  change
    denseLinearIsometryCompletionEquiv target target_dense
        ((denseLinearIsometryCompletionEquiv source source_dense).symm
          (source x)) = target x
  rw [← denseLinearIsometryCompletionEquiv_apply_coe source source_dense x]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  exact denseLinearIsometryCompletionEquiv_apply_coe target target_dense x

/-- Dense-core input for unitary intertwining of partially-defined real-linear
operators on stable complete normed carriers.

The global carrier equivalence and its norm preservation are theorem-generated
from `source` and `target`.  The only operator-specific obligations left as
fields are exact domain transport and the operator intertwining identity. -/
structure RealLinearPMapDenseCoreIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F) where
  source : C →ₗᵢ[ℝ] E
  target : C →ₗᵢ[ℝ] F
  source_dense : DenseRange source
  target_dense : DenseRange target
  domain_iff : ∀ x : E,
    x ∈ A.domain ↔
      realHilbertDenseCoreLinearIsometryEquiv
        source source_dense target target_dense x ∈ B.domain
  intertwines : ∀ x : A.domain,
    B ⟨realHilbertDenseCoreLinearIsometryEquiv
          source source_dense target target_dense (x : E),
        (domain_iff (x : E)).1 x.property⟩ =
      realHilbertDenseCoreLinearIsometryEquiv
        source source_dense target target_dense (A x)

/-- Common dense-core data automatically generate the already-canonical
operator-level unitary intertwining structure. -/
noncomputable def RealLinearPMapDenseCoreIntertwining.toUnitaryIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapDenseCoreIntertwining (C := C) A B) :
    RealLinearPMapUnitaryIntertwining A B := by
  let U : E ≃ₗᵢ[ℝ] F :=
    realHilbertDenseCoreLinearIsometryEquiv
      D.source D.source_dense D.target D.target_dense
  exact
    { equiv := U.toLinearEquiv
      norm_map := U.norm_map
      domain_iff := D.domain_iff
      intertwines := D.intertwines }

/-- Hence common dense-core data imply equality of the actual nonzero point
energies, without assuming spectral equality or a global Hilbert equivalence. -/
theorem realLinearPMapPointEnergySet_eq_of_denseCoreIntertwining
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F)
    (D : RealLinearPMapDenseCoreIntertwining (C := C) A B) :
    realLinearPMapPointEnergySet A = realLinearPMapPointEnergySet B :=
  realLinearPMapPointEnergySet_eq_of_unitaryIntertwining A B
    (D.toUnitaryIntertwining (C := C) (E := E) (F := F) (A := A) (B := B))

/-- The generated equivalence is norm preserving by construction; this receipt
is useful when a model-facing dense-core realization is built on a stable
ambient carrier before corestricting to a closed spectral support. -/
theorem RealLinearPMapDenseCoreIntertwining.generated_norm_map
    {C E F : Type}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A : E →ₗ.[ℝ] E} {B : F →ₗ.[ℝ] F}
    (D : RealLinearPMapDenseCoreIntertwining (C := C) A B)
    (x : E) :
    ‖D.toUnitaryIntertwining.equiv x‖ = ‖x‖ :=
  D.toUnitaryIntertwining.norm_map x

end

end MathlibAnalytic
end MGAP4D
