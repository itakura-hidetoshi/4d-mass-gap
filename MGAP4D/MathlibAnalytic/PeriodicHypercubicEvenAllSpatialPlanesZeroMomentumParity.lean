import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialParityGeometry
import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedRealTraceConjugation
import Mathlib.Tactic

/-!
# Spatial-parity invariance of the all-spatial zero-momentum plaquette operator

Spatial parity reverses each spatial link traversal.  For a plaquette in a fixed spatial plane
`(mu,nu)`, the canonical positively based image plaquette is therefore based at
`P(a) - e_mu - e_nu`.  This affine map of the time-zero displacement carrier is involutive.

With that rebasing, the parity-transformed four-edge holonomy is not a new physical object: it is a
cyclic rebase of the original boundary word, hence a group conjugate of the original plaquette
holonomy.  The canonical normalized-real-trace conjugation theorem then gives exact equality of the
scalar plaquette observable.  Reindexing the finite displacement sum proves parity invariance for
each spatial plane and therefore for the equal-weight all-spatial zero-momentum operator.

This is the finite-lattice `P = +` receipt for this concrete Wilson observable.  Charge
conjugation, a final discrete-channel package, continuum spin identification, and spectral mass
claims remain downstream.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- First coordinate direction of a purely spatial plane. -/
def PeriodicHypercubicSpatialPlane.firstAxis :
    PeriodicHypercubicSpatialPlane → PeriodicHypercubicAxis
  | .plane12 => 1
  | .plane13 => 1
  | .plane23 => 2

/-- Second coordinate direction of a purely spatial plane. -/
def PeriodicHypercubicSpatialPlane.secondAxis :
    PeriodicHypercubicSpatialPlane → PeriodicHypercubicAxis
  | .plane12 => 2
  | .plane13 => 3
  | .plane23 => 3

@[simp] theorem PeriodicHypercubicSpatialPlane.firstAxis_plane12 :
    PeriodicHypercubicSpatialPlane.firstAxis .plane12 = 1 := rfl
@[simp] theorem PeriodicHypercubicSpatialPlane.firstAxis_plane13 :
    PeriodicHypercubicSpatialPlane.firstAxis .plane13 = 1 := rfl
@[simp] theorem PeriodicHypercubicSpatialPlane.firstAxis_plane23 :
    PeriodicHypercubicSpatialPlane.firstAxis .plane23 = 2 := rfl
@[simp] theorem PeriodicHypercubicSpatialPlane.secondAxis_plane12 :
    PeriodicHypercubicSpatialPlane.secondAxis .plane12 = 2 := rfl
@[simp] theorem PeriodicHypercubicSpatialPlane.secondAxis_plane13 :
    PeriodicHypercubicSpatialPlane.secondAxis .plane13 = 3 := rfl
@[simp] theorem PeriodicHypercubicSpatialPlane.secondAxis_plane23 :
    PeriodicHypercubicSpatialPlane.secondAxis .plane23 = 3 := rfl

/-- Applying spatial parity twice returns the original vertex.  Exposing the involution as a simp
rule keeps later positive-link rebase calculations local and deterministic. -/
@[simp]
theorem periodicHypercubicEvenSpatialParity_apply_apply
    (H : ℕ) (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenSpatialParity H
        (periodicHypercubicEvenSpatialParity H v) = v :=
  periodicHypercubicEvenSpatialParity_involutive H v

/-- Cancel a positive shift in direction `mu` after commuting a second positive shift past it. -/
@[simp]
theorem periodicHypercubicUnshift_shift_shift_cancel_left
    (n : ℕ)
    (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis) :
    periodicHypercubicUnshift n
        (periodicHypercubicShift n (periodicHypercubicShift n x mu) nu) mu =
      periodicHypercubicShift n x nu := by
  rw [periodicHypercubicShift_comm n x mu nu]
  exact periodicHypercubicUnshift_shift n (periodicHypercubicShift n x nu) mu

/-- Cancel both shifts after the two corresponding negative rebase steps. -/
@[simp]
theorem periodicHypercubicUnshift_unshift_shift_shift_cancel
    (n : ℕ)
    (x : PeriodicHypercubicVertex n)
    (mu nu : PeriodicHypercubicAxis) :
    periodicHypercubicUnshift n
        (periodicHypercubicUnshift n
          (periodicHypercubicShift n (periodicHypercubicShift n x mu) nu) mu) nu =
      x := by
  rw [periodicHypercubicUnshift_shift_shift_cancel_left]
  exact periodicHypercubicUnshift_shift n x nu

/-- Parity-rebased time-zero plaquette base:
`a ↦ P(a) - e_mu - e_nu` in the chosen spatial plane. -/
def periodicHypercubicEvenSpatialPlaneParityRebase
    (H : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    PeriodicHypercubicEvenSpatialDisplacement H :=
  ⟨periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicEvenSpatialParity H a.1) plane.firstAxis)
      plane.secondAxis,
    by
      cases plane <;>
        simp [PeriodicHypercubicSpatialPlane.firstAxis,
          PeriodicHypercubicSpatialPlane.secondAxis,
          periodicHypercubicUnshift, periodicHypercubicUnit,
          a.2]⟩

@[simp]
theorem periodicHypercubicEvenSpatialPlaneParityRebase_val
    (H : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialPlaneParityRebase H plane a).1 =
      periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
        (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialParity H a.1) plane.firstAxis)
        plane.secondAxis :=
  rfl

/-- The parity rebase is involutive in every spatial plane. -/
theorem periodicHypercubicEvenSpatialPlaneParityRebase_involutive
    (H : ℕ)
    (plane : PeriodicHypercubicSpatialPlane) :
    Function.Involutive (periodicHypercubicEvenSpatialPlaneParityRebase H plane) := by
  intro a
  apply Subtype.ext
  funext i
  cases plane <;> fin_cases i <;>
    simp [periodicHypercubicEvenSpatialPlaneParityRebase,
      PeriodicHypercubicSpatialPlane.firstAxis,
      PeriodicHypercubicSpatialPlane.secondAxis,
      periodicHypercubicEvenSpatialParity,
      periodicHypercubicUnshift, periodicHypercubicUnit,
      a.2]

/-- The parity rebase as a finite-carrier equivalence used for zero-momentum reindexing. -/
def periodicHypercubicEvenSpatialPlaneParityRebaseEquiv
    (H : ℕ)
    (plane : PeriodicHypercubicSpatialPlane) :
    PeriodicHypercubicEvenSpatialDisplacement H ≃
      PeriodicHypercubicEvenSpatialDisplacement H where
  toFun := periodicHypercubicEvenSpatialPlaneParityRebase H plane
  invFun := periodicHypercubicEvenSpatialPlaneParityRebase H plane
  left_inv := periodicHypercubicEvenSpatialPlaneParityRebase_involutive H plane
  right_inv := periodicHypercubicEvenSpatialPlaneParityRebase_involutive H plane

@[simp]
theorem periodicHypercubicEvenSpatialPlaneParityRebaseEquiv_apply
    (H : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    periodicHypercubicEvenSpatialPlaneParityRebaseEquiv H plane a =
      periodicHypercubicEvenSpatialPlaneParityRebase H plane a :=
  rfl

@[simp]
theorem periodicHypercubicEvenSpatialPlaneParityRebaseEquiv_symm_apply
    (H : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H) :
    (periodicHypercubicEvenSpatialPlaneParityRebaseEquiv H plane).symm a =
      periodicHypercubicEvenSpatialPlaneParityRebase H plane a :=
  rfl

/-- Group element implementing the cyclic rebasing of a plaquette boundary word under parity. -/
def periodicHypercubicEvenSpatialPlaneParityConjugator
    {Gauge : Type} [Group Gauge]
    (H : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H → Gauge) : Gauge :=
  (A (a.1, plane.firstAxis) *
    A (periodicHypercubicShift (PeriodicHypercubicEvenSideLength H)
      a.1 plane.firstAxis, plane.secondAxis))⁻¹

/-- After the canonical parity rebase, a purely spatial plaquette holonomy is conjugate to the
original holonomy.  This is the exact finite positive-link realization of cyclic boundary rebasing. -/
theorem periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_parity_conj
    {Gauge : Type} [Group Gauge]
    (H : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicPlaquetteHolonomy
        (periodicHypercubicEvenConfigurationSpatialParity H A)
        (periodicHypercubicEvenSpatialPlanePlaquette H
          (periodicHypercubicEvenSpatialPlaneParityRebase H plane a) plane) =
      periodicHypercubicEvenSpatialPlaneParityConjugator H plane a A *
        periodicHypercubicPlaquetteHolonomy A
          (periodicHypercubicEvenSpatialPlanePlaquette H a plane) *
        (periodicHypercubicEvenSpatialPlaneParityConjugator H plane a A)⁻¹ := by
  cases plane <;>
    simp [periodicHypercubicPlaquetteHolonomy,
      periodicHypercubicStepValue,
      periodicHypercubicBoundaryStep,
      periodicHypercubicPlaquetteFirstAxis,
      periodicHypercubicPlaquetteSecondAxis,
      periodicHypercubicEvenSpatialPlanePlaquette,
      periodicHypercubicEvenSpatialPlaneParityRebase,
      periodicHypercubicEvenSpatialPlaneParityConjugator,
      PeriodicHypercubicSpatialPlane.firstAxis,
      PeriodicHypercubicSpatialPlane.secondAxis,
      periodicHypercubicEvenConfigurationSpatialParity,
      periodicHypercubicEvenEdgeSpatialParity,
      periodicHypercubicEvenSpatialParity_shift_spatial,
      periodicHypercubicEvenSpatialParity_unshift_spatial] <;>
    group

/-- The normalized real-trace plaquette observable is parity even after the canonical displacement
rebase. -/
theorem periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_parity
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (a : PeriodicHypercubicEvenSpatialDisplacement H)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane
        (periodicHypercubicEvenSpatialPlaneParityRebase H plane a)
        (periodicHypercubicEvenConfigurationSpatialParity H A) =
      periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace H N plane a A := by
  unfold periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace
  rw [periodicHypercubicEvenSpatialPlanePlaquetteHolonomy_parity_conj]
  exact normalizedSpecialUnitaryRealTrace_conjInvariant
    (periodicHypercubicEvenSpatialPlaneParityConjugator H plane a A)
    (periodicHypercubicPlaquetteHolonomy A
      (periodicHypercubicEvenSpatialPlanePlaquette H a plane))

/-- Every fixed spatial-plane zero-momentum component is parity even. -/
theorem periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_parityInvariant
    (H N : ℕ)
    (plane : PeriodicHypercubicSpatialPlane)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane
        (periodicHypercubicEvenConfigurationSpatialParity H A) =
      periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace H N plane A := by
  classical
  unfold periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace
  rw [← Equiv.sum_comp
    (periodicHypercubicEvenSpatialPlaneParityRebaseEquiv H plane)]
  apply Finset.sum_congr rfl
  intro a _ha
  exact periodicHypercubicEvenSpatialPlaneTranslatedNormalizedTrace_parity
    H N plane a A

/-- The equal-weight all-spatial zero-momentum normalized-trace observable is spatial-parity even. -/
theorem periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace_parityInvariant
    (H N : ℕ)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N
        (periodicHypercubicEvenConfigurationSpatialParity H A) =
      periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace H N A := by
  classical
  unfold periodicHypercubicEvenAllSpatialPlanesZeroMomentumNormalizedTrace
  apply Finset.sum_congr rfl
  intro plane _hplane
  exact periodicHypercubicEvenSpatialPlaneZeroMomentumNormalizedTrace_parityInvariant
    H N plane A

end

end MathlibAnalytic
end MGAP4D
