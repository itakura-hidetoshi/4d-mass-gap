import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSHilbert

/-!
# Inclusion coherence of fixed-slot primary scalar OS sectors

The reconstructed Hilbert carrier is currently defined separately for each
finite nonnegative rational slot set.  Before taking any directed union, the
finite sectors must be related by exact same-root maps.

For `J ⊆ K`, a `J`-slot observable is regarded as a `K`-slot observable by
ignoring the additional coordinates.  This file proves that its pullback to the
full rational path is literally unchanged.  Consequently the continuum OS
bilinear form is exactly preserved by slot inclusion.

No direct limit, closure, time translation, semigroup, Hamiltonian, or spectral
claim is made here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Restrict a `K`-coordinate point to the coordinates selected by `J ⊆ K`, as
a continuous map between finite product spaces. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotCoordinateRestrictionContinuousMap
    (J K : Finset ℚ)
    (hJK : J ⊆ K) :
    C((∀ q : K, ℝ), ∀ q : J, ℝ) :=
  ⟨(fun x q => x ⟨q.1, hJK q.2⟩),
    continuous_pi (fun q => continuous_apply ⟨q.1, hJK q.2⟩)⟩

/-- Covariant inclusion of cylinder observables along `J ⊆ K`: the larger-slot
observable simply ignores coordinates outside `J`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
    (J K : Finset ℚ)
    (hJK : J ⊆ K) :
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J →ₗ[ℝ]
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable K where
  toFun F :=
    F.compContinuous
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotCoordinateRestrictionContinuousMap
        J K hJK)
  map_add' F G := by
    ext x
    rfl
  map_smul' c F := by
    ext x
    rfl

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion_apply
    (J K : Finset ℚ)
    (hJK : J ⊆ K)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J)
    (x : ∀ q : K, ℝ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        J K hJK F x =
      F (fun q : J => x ⟨q.1, hJK q.2⟩) :=
  rfl

/-- Enlarging the finite slot carrier does not alter the induced observable on
the complete scalar rational path. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_inclusion
    (J K : Finset ℚ)
    (hJK : J ⊆ K)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable K
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J K hJK F) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable J F := by
  ext x
  rfl

/-- Identity slot inclusion is the identity linear map. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion_refl
    (J : Finset ℚ)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        J J (fun _ h => h) F = F := by
  ext x
  rfl

/-- Successive slot enlargements are coherent. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion_trans
    (J K M : Finset ℚ)
    (hJK : J ⊆ K)
    (hKM : K ⊆ M)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        K M hKM
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J K hJK F) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        J M (fun q hq => hKM (hJK hq)) F := by
  ext x
  rfl

/-- Exact OS-kernel compatibility under slot inclusion.  Both sides are the
same reflected expectation on the same continuum scalar path law. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.fixedSlotOSBilinForm_inclusion
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J K : Finset ℚ)
    (hJK : J ⊆ K)
    (F G : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing K
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J K hJK F)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J K hJK G) =
      L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing J F G := by
  rw [L.fixedSlotOSBilinForm_apply, L.fixedSlotOSBilinForm_apply]
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_inclusion,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotPathObservable_inclusion]

/-- In particular, the OS quadratic form is exactly preserved when a finite
slot set is enlarged. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.fixedSlotOSQuadratic_inclusion
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (latticeSpacing : ℕ → ℝ)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta latticeSpacing)
    (J K : Finset ℚ)
    (hJK : J ⊆ K)
    (F : PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservable J) :
    L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing K
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J K hJK F)
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          J K hJK F) =
      L.fixedSlotOSBilinForm H N hN beta hbeta latticeSpacing J F F :=
  L.fixedSlotOSBilinForm_inclusion
    H N hN beta hbeta latticeSpacing J K hJK F F

end

end MathlibAnalytic
end MGAP4D
