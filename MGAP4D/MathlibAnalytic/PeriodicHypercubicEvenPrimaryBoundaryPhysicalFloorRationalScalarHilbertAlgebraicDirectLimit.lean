import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSHilbertIndexedSystem

/-!
# Algebraic direct limit of finite-slot primary scalar OS Hilbert sectors

The preceding layer packages the finite nonnegative rational slot sectors as a
Mathlib `DirectedSystem` of real Hilbert spaces with isometric linear transition
maps.  This file takes only the algebraic direct limit of that system using
`Module.DirectLimit`.

Each finite-slot Hilbert sector maps canonically into the algebraic direct
limit.  The transition compatibility is inherited from Mathlib's direct-limit
API, and the canonical maps are injective because every transition map is the
linear-map view of a `LinearIsometry`.  Every algebraic direct-limit vector is
represented by a vector from one finite-slot sector.

No norm is imposed on the algebraic direct limit here, and no completion,
positive-time closedness assertion, time translation, semigroup, Hamiltonian,
spectral statement, or mass-gap transfer is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {latticeSpacing : ℕ → ℝ}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta latticeSpacing}

/-- The algebraic direct limit of the canonically indexed finite-slot primary
scalar OS Hilbert sectors.  This is a real module; no direct-limit norm or
completion is introduced at this layer. -/
abbrev fixedSlotHilbertAlgebraicDirectLimit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : Type :=
  Module.DirectLimit
    (fun J : PrimaryScalarFiniteNonnegativeSlotIndex =>
      P.fixedSlotIndexedHilbert J)
    (fun J K hJK => P.fixedSlotIndexedHilbertMap J K hJK)

/-- Canonical real-linear map from one finite-slot Hilbert sector into the
algebraic direct limit. -/
noncomputable def fixedSlotHilbertAlgebraicOf
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    P.fixedSlotIndexedHilbert J →ₗ[ℝ]
      P.fixedSlotHilbertAlgebraicDirectLimit :=
  Module.DirectLimit.of
    ℝ PrimaryScalarFiniteNonnegativeSlotIndex
    (fun K : PrimaryScalarFiniteNonnegativeSlotIndex =>
      P.fixedSlotIndexedHilbert K)
    (fun K M hKM => P.fixedSlotIndexedHilbertMap K M hKM)
    J

/-- The canonical maps identify a vector with every isometric transition of
that vector into a larger finite-slot sector. -/
@[simp]
theorem fixedSlotHilbertAlgebraicOf_map
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J K : PrimaryScalarFiniteNonnegativeSlotIndex)
    (hJK : J ≤ K)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertAlgebraicOf K
        (P.fixedSlotIndexedHilbertMap J K hJK x) =
      P.fixedSlotHilbertAlgebraicOf J x := by
  exact
    Module.DirectLimit.of_f
      (R := ℝ)
      (ι := PrimaryScalarFiniteNonnegativeSlotIndex)
      (G := fun M : PrimaryScalarFiniteNonnegativeSlotIndex =>
        P.fixedSlotIndexedHilbert M)
      (f := fun M Q hMQ => P.fixedSlotIndexedHilbertMap M Q hMQ)

/-- Every indexed transition map is injective because it is the linear-map view
of a real linear isometry. -/
theorem fixedSlotIndexedHilbertMap_injective
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J K : PrimaryScalarFiniteNonnegativeSlotIndex)
    (hJK : J ≤ K) :
    Function.Injective (P.fixedSlotIndexedHilbertMap J K hJK) := by
  simpa [fixedSlotIndexedHilbertMap] using
    (P.fixedSlotIndexedHilbertLinearIsometry J K hJK).injective

/-- Every finite-slot Hilbert sector embeds injectively into the algebraic
primary scalar OS direct limit. -/
theorem fixedSlotHilbertAlgebraicOf_injective
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    Function.Injective (P.fixedSlotHilbertAlgebraicOf J) := by
  intro x y hxy
  have hxy' :
      Module.DirectLimit.of
          ℝ PrimaryScalarFiniteNonnegativeSlotIndex
          (fun M : PrimaryScalarFiniteNonnegativeSlotIndex =>
            P.fixedSlotIndexedHilbert M)
          (fun M Q hMQ => P.fixedSlotIndexedHilbertMap M Q hMQ)
          J x =
        Module.DirectLimit.of
          ℝ PrimaryScalarFiniteNonnegativeSlotIndex
          (fun M : PrimaryScalarFiniteNonnegativeSlotIndex =>
            P.fixedSlotIndexedHilbert M)
          (fun M Q hMQ => P.fixedSlotIndexedHilbertMap M Q hMQ)
          J y := by
    simpa [fixedSlotHilbertAlgebraicOf] using hxy
  obtain ⟨K, hJK, hEq⟩ :=
    Module.DirectLimit.exists_eq_of_of_eq
      (R := ℝ)
      (ι := PrimaryScalarFiniteNonnegativeSlotIndex)
      (G := fun M : PrimaryScalarFiniteNonnegativeSlotIndex =>
        P.fixedSlotIndexedHilbert M)
      (f := fun M Q hMQ => P.fixedSlotIndexedHilbertMap M Q hMQ)
      hxy'
  exact P.fixedSlotIndexedHilbertMap_injective J K hJK hEq

/-- Every algebraic direct-limit vector has a representative in one finite-slot
primary scalar OS Hilbert sector. -/
theorem fixedSlotHilbertAlgebraic_exists_representation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
      ∃ x : P.fixedSlotIndexedHilbert J,
        P.fixedSlotHilbertAlgebraicOf J x = z := by
  simpa [fixedSlotHilbertAlgebraicDirectLimit, fixedSlotHilbertAlgebraicOf] using
    (Module.DirectLimit.exists_of
      (R := ℝ)
      (ι := PrimaryScalarFiniteNonnegativeSlotIndex)
      (G := fun M : PrimaryScalarFiniteNonnegativeSlotIndex =>
        P.fixedSlotIndexedHilbert M)
      (f := fun M Q hMQ => P.fixedSlotIndexedHilbertMap M Q hMQ)
      z)

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
