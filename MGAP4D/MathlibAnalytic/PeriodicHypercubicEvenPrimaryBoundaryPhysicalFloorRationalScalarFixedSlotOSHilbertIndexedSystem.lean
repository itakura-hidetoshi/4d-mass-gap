import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSHilbertDirected
import Mathlib.Algebra.Colimit.Module

/-!
# Canonically indexed directed system of finite-slot primary scalar OS Hilbert sectors

The preceding layer proves that arbitrary fixed-slot OS Hilbert sectors over the
same continuum scalar law have finite common upper bounds and coherent
isometric inclusion maps.  Before taking a direct limit, we remove irrelevant
proof-field dependence from the index.

The index is exactly a finite set of nonnegative rational Euclidean times.  A
single fixed-slot reconstruction datum supplies the global analytic hypotheses
(positive lattice spacing and divergent primary temporal reach), and every
index determines a canonical reconstruction datum carrying those same global
proofs.  Thus the resulting Hilbert family is indexed only by finite slot
geometry.

The inclusion maps are the already-canonical Hilbert `LinearIsometry`s.  Their
linear-map views satisfy Mathlib's `DirectedSystem` laws by the identity and
transitivity coherence proved previously, and each transition map preserves
norm exactly.

No direct-limit carrier, positive-time closedness assertion, time translation,
semigroup, Hamiltonian, spectral statement, or mass-gap transfer is introduced
here.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical index type for the finite-slot primary scalar OS reconstruction:
a finite set of nonnegative rational Euclidean times. -/
abbrev PrimaryScalarFiniteNonnegativeSlotIndex :=
  {J : Finset ℚ // ∀ q ∈ J, 0 ≤ q}

/-- The finite nonnegative slot indices are nonempty; the empty slot set is an
index. -/
instance : Nonempty PrimaryScalarFiniteNonnegativeSlotIndex :=
  ⟨⟨∅, by simp⟩⟩

/-- Finite nonnegative slot indices are upward directed by finite union. -/
instance : IsDirectedOrder PrimaryScalarFiniteNonnegativeSlotIndex where
  directed J K := by
    refine ⟨⟨J.1 ∪ K.1, ?_⟩, ?_, ?_⟩
    · intro q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact J.2 q hq
      · exact K.2 q hq
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {latticeSpacing : ℕ → ℝ}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta latticeSpacing}

/-- The finite nonnegative slot index carried by an existing fixed-slot datum. -/
def fixedSlotIndex
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    PrimaryScalarFiniteNonnegativeSlotIndex :=
  ⟨P.slots, P.slots_nonneg⟩

@[simp]
theorem fixedSlotIndex_val
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    P.fixedSlotIndex.1 = P.slots :=
  rfl

/-- Canonical fixed-slot reconstruction datum attached to a finite nonnegative
slot index.  The global analytic input is inherited from one datum over the
same continuum scalar law, so only the finite slot geometry varies. -/
def fixedSlotDataOfIndex
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L where
  slots := J.1
  slots_nonneg := J.2
  latticeSpacing_pos := P.latticeSpacing_pos
  temporalReach_tendsto := P.temporalReach_tendsto

@[simp]
theorem fixedSlotDataOfIndex_slots
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    (P.fixedSlotDataOfIndex J).slots = J.1 :=
  rfl

/-- Passing an existing datum to its slot index and reconstructing canonically
returns that datum exactly.  Hence the indexed system stays on the same fixed
OS root rather than replacing it by an unrelated family. -/
@[simp]
theorem fixedSlotDataOfIndex_fixedSlotIndex
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    P.fixedSlotDataOfIndex P.fixedSlotIndex = P := by
  cases P
  rfl

/-- Hilbert sector attached canonically to a finite nonnegative rational slot
index. -/
abbrev fixedSlotIndexedHilbert
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) : Type :=
  (P.fixedSlotDataOfIndex J).Hilbert

/-- Canonical isometric transition map between indexed Hilbert sectors. -/
noncomputable def fixedSlotIndexedHilbertLinearIsometry
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J K : PrimaryScalarFiniteNonnegativeSlotIndex)
    (hJK : J ≤ K) :
    P.fixedSlotIndexedHilbert J →ₗᵢ[ℝ] P.fixedSlotIndexedHilbert K :=
  (P.fixedSlotDataOfIndex J).fixedSlotHilbertLinearIsometry
    (P.fixedSlotDataOfIndex K) hJK

/-- Linear-map view of the indexed isometric transition.  This is the morphism
family consumed by Mathlib's algebraic direct-limit API. -/
noncomputable def fixedSlotIndexedHilbertMap
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J K : PrimaryScalarFiniteNonnegativeSlotIndex)
    (hJK : J ≤ K) :
    P.fixedSlotIndexedHilbert J →ₗ[ℝ] P.fixedSlotIndexedHilbert K :=
  (P.fixedSlotIndexedHilbertLinearIsometry J K hJK).toLinearMap

/-- Every indexed transition preserves Hilbert norm exactly. -/
theorem fixedSlotIndexedHilbertMap_norm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J K : PrimaryScalarFiniteNonnegativeSlotIndex)
    (hJK : J ≤ K)
    (x : P.fixedSlotIndexedHilbert J) :
    ‖P.fixedSlotIndexedHilbertMap J K hJK x‖ = ‖x‖ :=
  (P.fixedSlotIndexedHilbertLinearIsometry J K hJK).norm_map x

/-- The indexed transition at a reflexive inclusion is the identity. -/
@[simp]
theorem fixedSlotIndexedHilbertMap_refl
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotIndexedHilbertMap J J le_rfl x = x := by
  exact (P.fixedSlotDataOfIndex J).fixedSlotHilbertInclusion_refl x

/-- Indexed Hilbert transitions compose exactly along slot inclusions. -/
@[simp]
theorem fixedSlotIndexedHilbertMap_trans
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J K M : PrimaryScalarFiniteNonnegativeSlotIndex)
    (hJK : J ≤ K)
    (hKM : K ≤ M)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotIndexedHilbertMap K M hKM
        (P.fixedSlotIndexedHilbertMap J K hJK x) =
      P.fixedSlotIndexedHilbertMap J M (hJK.trans hKM) x := by
  exact
    (P.fixedSlotDataOfIndex J).fixedSlotHilbertInclusion_trans
      (P.fixedSlotDataOfIndex K) (P.fixedSlotDataOfIndex M)
      hJK hKM x

/-- The canonical finite-slot Hilbert family, with the already-proved isometric
inclusions, is a Mathlib `DirectedSystem`. -/
noncomputable instance fixedSlotIndexedHilbertDirectedSystem
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    DirectedSystem
      (fun J : PrimaryScalarFiniteNonnegativeSlotIndex =>
        P.fixedSlotIndexedHilbert J)
      (fun _ _ h => P.fixedSlotIndexedHilbertMap _ _ h) where
  map_self := fun {i} x =>
    P.fixedSlotIndexedHilbertMap_refl i x
  map_map := fun {k j i} hij hjk x =>
    P.fixedSlotIndexedHilbertMap_trans i j k hij hjk x

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D