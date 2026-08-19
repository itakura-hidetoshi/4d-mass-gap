import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpatialSignedPermutationVertexAction
import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidence
import Mathlib.Tactic

/-!
# Signed-shift covariance of the abstract spatial permutation action

The abstract signed-coordinate group now acts on the actual periodic vertex carrier.  To lift that
action to positively oriented physical links, one must know exactly what happens to a unit lattice
step.  This file proves that geometric covariance before introducing any edge or configuration
transport.

Euclidean time is fixed, so a positive time step stays a positive time step.  For an abstract
spatial axis `k : Fin 3`, write `σ = g.right`.  The corresponding physical axis is `Fin.succ k`,
and its image is `Fin.succ (σ k)`.  The sign attached to the image coordinate is
`g.left (σ k) ∈ ℤˣ = {+1,-1}`:

* sign `+1` sends a positive source step to a positive step along the image axis;
* sign `-1` sends it to one negative step, represented geometrically by `periodicHypercubicUnshift`.

The final theorem packages these two cases into the exact `if` form needed by the subsequent
positive-edge representative.  No edge/configuration action, plaquette transport, cubic irrep,
continuum-spin identification, or spectral claim is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Physical four-dimensional axis corresponding to the image of an abstract spatial axis under a
signed permutation. -/
def periodicHypercubicSpatialSignedPermutationAxis
    (g : SpatialSignedPermutationGroup)
    (k : Fin 3) : PeriodicHypercubicAxis :=
  Fin.succ (g.right k)

@[simp]
theorem periodicHypercubicSpatialSignedPermutationAxis_val
    (g : SpatialSignedPermutationGroup)
    (k : Fin 3) :
    periodicHypercubicSpatialSignedPermutationAxis g k = Fin.succ (g.right k) :=
  rfl

/-- Euclidean time axis `0 : Fin 4` is distinct from every embedded spatial axis. -/
@[simp]
theorem periodicHypercubicTimeAxis_ne_spatialSucc
    (k : Fin 3) :
    (0 : Fin 4) ≠ Fin.succ k := by
  intro h
  have hval := congrArg Fin.val h
  omega

/-- The sign carried by the image of any spatial axis is exactly `+1` or `-1`. -/
theorem spatialSignedPermutation_imageSign_eq_one_or_neg_one
    (g : SpatialSignedPermutationGroup)
    (k : Fin 3) :
    g.left (g.right k) = 1 ∨ g.left (g.right k) = (-1 : ℤˣ) :=
  Int.units_eq_one_or _

/-- If an output spatial axis is not the image of `k`, then its inverse-permuted source axis is not
`k`. -/
theorem spatialAxisPermutation_symm_ne_of_ne_image
    (σ : Equiv.Perm (Fin 3))
    {j k : Fin 3}
    (h : j ≠ σ k) :
    σ.symm j ≠ k := by
  intro hpre
  apply h
  simpa using congrArg σ hpre

/-- Signed spatial permutations fix Euclidean time translations. -/
theorem periodicHypercubicVertexSpatialSignedPermutation_shift_time
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (x : PeriodicHypercubicVertex n) :
    periodicHypercubicVertexSpatialSignedPermutation n g
        (periodicHypercubicShift n x 0) =
      periodicHypercubicShift n
        (periodicHypercubicVertexSpatialSignedPermutation n g x) 0 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [periodicHypercubicVertexSpatialSignedPermutation,
      periodicHypercubicShift_apply, periodicHypercubicUnit]
  · simp [periodicHypercubicVertexSpatialSignedPermutation,
      periodicHypercubicShift_apply, periodicHypercubicUnit]

/-- With positive image sign, a positive spatial unit step maps to a positive unit step along the
permuted axis. -/
theorem periodicHypercubicVertexSpatialSignedPermutation_shift_spatial_of_pos
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (x : PeriodicHypercubicVertex n)
    (k : Fin 3)
    (hpos : g.left (g.right k) = 1) :
    periodicHypercubicVertexSpatialSignedPermutation n g
        (periodicHypercubicShift n x (Fin.succ k)) =
      periodicHypercubicShift n
        (periodicHypercubicVertexSpatialSignedPermutation n g x)
        (periodicHypercubicSpatialSignedPermutationAxis g k) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [periodicHypercubicVertexSpatialSignedPermutation,
      periodicHypercubicSpatialSignedPermutationAxis,
      periodicHypercubicShift_apply, periodicHypercubicUnit]
  · by_cases hj : j = g.right k
    · subst j
      simp [periodicHypercubicVertexSpatialSignedPermutation,
        periodicHypercubicSpatialSignedPermutationAxis,
        periodicHypercubicShift_apply, periodicHypercubicUnit, hpos]
    · have hpre : g.right.symm j ≠ k :=
        spatialAxisPermutation_symm_ne_of_ne_image g.right hj
      simp [periodicHypercubicVertexSpatialSignedPermutation,
        periodicHypercubicSpatialSignedPermutationAxis,
        periodicHypercubicShift_apply, periodicHypercubicUnit, hj, hpre]

/-- With negative image sign, a positive spatial unit step maps to one negative unit step along the
permuted axis. -/
theorem periodicHypercubicVertexSpatialSignedPermutation_shift_spatial_of_neg
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (x : PeriodicHypercubicVertex n)
    (k : Fin 3)
    (hneg : g.left (g.right k) = (-1 : ℤˣ)) :
    periodicHypercubicVertexSpatialSignedPermutation n g
        (periodicHypercubicShift n x (Fin.succ k)) =
      periodicHypercubicUnshift n
        (periodicHypercubicVertexSpatialSignedPermutation n g x)
        (periodicHypercubicSpatialSignedPermutationAxis g k) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [periodicHypercubicVertexSpatialSignedPermutation,
      periodicHypercubicSpatialSignedPermutationAxis,
      periodicHypercubicShift_apply, periodicHypercubicUnshift,
      periodicHypercubicUnit]
  · by_cases hj : j = g.right k
    · subst j
      simp [periodicHypercubicVertexSpatialSignedPermutation,
        periodicHypercubicSpatialSignedPermutationAxis,
        periodicHypercubicShift_apply, periodicHypercubicUnshift,
        periodicHypercubicUnit, hneg]
      ring
    · have hpre : g.right.symm j ≠ k :=
        spatialAxisPermutation_symm_ne_of_ne_image g.right hj
      simp [periodicHypercubicVertexSpatialSignedPermutation,
        periodicHypercubicSpatialSignedPermutationAxis,
        periodicHypercubicShift_apply, periodicHypercubicUnshift,
        periodicHypercubicUnit, hj, hpre]

/-- Unified signed covariance of a positive spatial unit step.  This is the exact orientation split
needed to define the positive-link representative of a general signed spatial permutation. -/
theorem periodicHypercubicVertexSpatialSignedPermutation_shift_spatial
    (n : ℕ)
    (g : SpatialSignedPermutationGroup)
    (x : PeriodicHypercubicVertex n)
    (k : Fin 3) :
    periodicHypercubicVertexSpatialSignedPermutation n g
        (periodicHypercubicShift n x (Fin.succ k)) =
      if g.left (g.right k) = 1 then
        periodicHypercubicShift n
          (periodicHypercubicVertexSpatialSignedPermutation n g x)
          (periodicHypercubicSpatialSignedPermutationAxis g k)
      else
        periodicHypercubicUnshift n
          (periodicHypercubicVertexSpatialSignedPermutation n g x)
          (periodicHypercubicSpatialSignedPermutationAxis g k) := by
  rcases spatialSignedPermutation_imageSign_eq_one_or_neg_one g k with hpos | hneg
  · rw [if_pos hpos]
    exact periodicHypercubicVertexSpatialSignedPermutation_shift_spatial_of_pos
      n g x k hpos
  · have hne : g.left (g.right k) ≠ 1 := by
      rw [hneg]
      native_decide
    rw [if_neg hne]
    exact periodicHypercubicVertexSpatialSignedPermutation_shift_spatial_of_neg
      n g x k hneg

end

end MathlibAnalytic
end MGAP4D
