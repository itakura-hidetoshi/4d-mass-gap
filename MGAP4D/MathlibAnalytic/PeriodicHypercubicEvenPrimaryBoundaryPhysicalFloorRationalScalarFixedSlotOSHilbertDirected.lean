import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSHilbertIsometry

/-!
# Directed finite-slot primary scalar OS Hilbert sectors

The preceding layer gives a canonical real linear isometry between fixed-slot OS
Hilbert completions whenever one finite nonnegative rational slot set is
contained in another.  This file records the next structural fact needed before
any inductive/direct-limit construction: two fixed-slot sectors have a canonical
finite common upper bound, namely the union of their slot sets.

For fixed reconstruction data `P` and `Q` over the same continuum scalar law,
we construct `P.fixedSlotUnionData Q` with slots `P.slots ∪ Q.slots`, together
with the canonical Hilbert isometries from both factors into the union sector.
The already-proved transitivity theorem then gives coherence from the union
sector into every larger finite-slot sector.

This is only the directed-system layer.  No direct limit, positive-time
closedness assertion, time translation, semigroup, Hamiltonian, spectral
statement, or mass-gap transfer is introduced here.
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

/-- Canonical finite common upper bound of two fixed-slot reconstruction data:
take the union of the two finite nonnegative rational slot sets.  All analytic
input is unchanged and remains on the same continuum scalar law. -/
def fixedSlotUnionData
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L where
  slots := P.slots ∪ Q.slots
  slots_nonneg := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact P.slots_nonneg q hq
    · exact Q.slots_nonneg q hq
  latticeSpacing_pos := P.latticeSpacing_pos
  temporalReach_tendsto := P.temporalReach_tendsto

@[simp]
theorem fixedSlotUnionData_slots
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    (P.fixedSlotUnionData Q).slots = P.slots ∪ Q.slots :=
  rfl

/-- The left slot set is contained in the canonical union sector. -/
theorem fixedSlotUnionData_left_subset
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    P.slots ⊆ (P.fixedSlotUnionData Q).slots := by
  intro q hq
  change q ∈ P.slots ∪ Q.slots
  simp [hq]

/-- The right slot set is contained in the canonical union sector. -/
theorem fixedSlotUnionData_right_subset
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    Q.slots ⊆ (P.fixedSlotUnionData Q).slots := by
  intro q hq
  change q ∈ P.slots ∪ Q.slots
  simp [hq]

/-- Canonical Hilbert isometry from the left sector into the finite union
sector. -/
noncomputable def fixedSlotHilbertUnionLeftLinearIsometry
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    P.Hilbert →ₗᵢ[ℝ] (P.fixedSlotUnionData Q).Hilbert :=
  P.fixedSlotHilbertLinearIsometry
    (P.fixedSlotUnionData Q)
    (P.fixedSlotUnionData_left_subset Q)

/-- Canonical Hilbert isometry from the right sector into the finite union
sector. -/
noncomputable def fixedSlotHilbertUnionRightLinearIsometry
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    Q.Hilbert →ₗᵢ[ℝ] (P.fixedSlotUnionData Q).Hilbert :=
  Q.fixedSlotHilbertLinearIsometry
    (P.fixedSlotUnionData Q)
    (P.fixedSlotUnionData_right_subset Q)

/-- The left canonical embedding into the common upper bound preserves norm. -/
theorem fixedSlotHilbertUnionLeft_norm
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (x : P.Hilbert) :
    ‖P.fixedSlotHilbertUnionLeftLinearIsometry Q x‖ = ‖x‖ :=
  (P.fixedSlotHilbertUnionLeftLinearIsometry Q).norm_map x

/-- The right canonical embedding into the common upper bound preserves norm. -/
theorem fixedSlotHilbertUnionRight_norm
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (x : Q.Hilbert) :
    ‖P.fixedSlotHilbertUnionRightLinearIsometry Q x‖ = ‖x‖ :=
  (P.fixedSlotHilbertUnionRightLinearIsometry Q).norm_map x

/-- Any two finite fixed-slot OS Hilbert sectors admit a finite common upper
bound in the slot-inclusion relation. -/
theorem fixedSlotHilbert_exists_common_upper_bound
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    ∃ R : PrimaryScalarFixedSlotOSPreHilbertData
        H N hN beta hbeta latticeSpacing L,
      P.slots ⊆ R.slots ∧ Q.slots ⊆ R.slots := by
  refine ⟨P.fixedSlotUnionData Q, ?_, ?_⟩
  · exact P.fixedSlotUnionData_left_subset Q
  · exact P.fixedSlotUnionData_right_subset Q

/-- The left inclusion through the canonical union sector agrees exactly with
the direct inclusion into every larger finite-slot sector. -/
theorem fixedSlotHilbertUnionLeft_trans
    (P Q R : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hUR : (P.fixedSlotUnionData Q).slots ⊆ R.slots)
    (x : P.Hilbert) :
    (P.fixedSlotUnionData Q).fixedSlotHilbertInclusion R hUR
        (P.fixedSlotHilbertInclusion
          (P.fixedSlotUnionData Q)
          (P.fixedSlotUnionData_left_subset Q) x) =
      P.fixedSlotHilbertInclusion R
        (fun _ hq => hUR (P.fixedSlotUnionData_left_subset Q hq)) x := by
  exact
    P.fixedSlotHilbertInclusion_trans
      (P.fixedSlotUnionData Q) R
      (P.fixedSlotUnionData_left_subset Q) hUR x

/-- The right inclusion through the canonical union sector agrees exactly with
the direct inclusion into every larger finite-slot sector. -/
theorem fixedSlotHilbertUnionRight_trans
    (P Q R : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hUR : (P.fixedSlotUnionData Q).slots ⊆ R.slots)
    (x : Q.Hilbert) :
    (P.fixedSlotUnionData Q).fixedSlotHilbertInclusion R hUR
        (Q.fixedSlotHilbertInclusion
          (P.fixedSlotUnionData Q)
          (P.fixedSlotUnionData_right_subset Q) x) =
      Q.fixedSlotHilbertInclusion R
        (fun _ hq => hUR (P.fixedSlotUnionData_right_subset Q hq)) x := by
  exact
    Q.fixedSlotHilbertInclusion_trans
      (P.fixedSlotUnionData Q) R
      (P.fixedSlotUnionData_right_subset Q) hUR x

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
