import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSSeparatedIsometry
import MGAP4D.MathlibAnalytic.RealLinearIsometrySeparationCompletion

/-!
# Isometric inclusion of fixed-slot primary scalar OS Hilbert sectors

The separated fixed-slot OS sectors are already connected by canonical real
linear isometries whenever one finite nonnegative rational slot set is contained
in another.  This file extends those inclusions to the corresponding Hilbert
completions using Mathlib's canonical completion embedding and the already
canonical `realLinearIsometryCompletionExtension`.

For `P.slots ⊆ Q.slots`, this gives a real linear isometry

`P.Hilbert →ₗᵢ[ℝ] Q.Hilbert`

which agrees exactly with the separated inclusion on the dense separated
carrier, preserves norm, and satisfies identity and transitivity coherence.

No direct limit, positive-time closedness assertion, time translation,
semigroup, Hamiltonian, spectral theorem, or mass-gap statement is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open UniformSpace

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

/-- First compose the separated fixed-slot isometry with the canonical dense
embedding of the larger separated carrier into its Hilbert completion. -/
noncomputable def fixedSlotSeparatedToHilbertLinearIsometry
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.Separated →ₗᵢ[ℝ] Q.Hilbert := by
  change P.Separated →ₗᵢ[ℝ] Completion Q.Separated
  exact
    (Completion.toComplₗᵢ :
      Q.Separated →ₗᵢ[ℝ] Completion Q.Separated).comp
      (P.fixedSlotSeparatedLinearIsometry Q hPQ)

/-- Canonical isometric inclusion of fixed-slot OS Hilbert completions. -/
noncomputable def fixedSlotHilbertLinearIsometry
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.Hilbert →ₗᵢ[ℝ] Q.Hilbert := by
  change Completion P.Separated →ₗᵢ[ℝ] Q.Hilbert
  exact
    realLinearIsometryCompletionExtension
      (P.fixedSlotSeparatedToHilbertLinearIsometry Q hPQ)

/-- Linear-map view of the Hilbert-completion inclusion. -/
noncomputable def fixedSlotHilbertInclusion
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.Hilbert →ₗ[ℝ] Q.Hilbert :=
  (P.fixedSlotHilbertLinearIsometry Q hPQ).toLinearMap

/-- The Hilbert-completion inclusion agrees exactly with the separated inclusion
on the canonical dense embedding. -/
@[simp]
theorem fixedSlotHilbertLinearIsometry_coe
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (x : P.Separated) :
    P.fixedSlotHilbertLinearIsometry Q hPQ
        (x : Completion P.Separated) =
      (P.fixedSlotSeparatedLinearIsometry Q hPQ x :
        Completion Q.Separated) := by
  change
    realLinearIsometryCompletionExtension
        (P.fixedSlotSeparatedToHilbertLinearIsometry Q hPQ)
        (x : Completion P.Separated) =
      (P.fixedSlotSeparatedLinearIsometry Q hPQ x :
        Completion Q.Separated)
  rw [realLinearIsometryCompletionExtension_coe]
  rfl

@[simp]
theorem fixedSlotHilbertInclusion_coe
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (x : P.Separated) :
    P.fixedSlotHilbertInclusion Q hPQ
        (x : Completion P.Separated) =
      (P.fixedSlotSeparatedInclusion Q hPQ x :
        Completion Q.Separated) := by
  exact P.fixedSlotHilbertLinearIsometry_coe Q hPQ x

/-- The Hilbert-completion inclusion preserves norm exactly. -/
theorem fixedSlotHilbertInclusion_norm
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (x : P.Hilbert) :
    ‖P.fixedSlotHilbertInclusion Q hPQ x‖ = ‖x‖ := by
  exact (P.fixedSlotHilbertLinearIsometry Q hPQ).norm_map x

/-- On dense OS vectors represented by fixed-slot observables, the Hilbert
inclusion is exactly the previously constructed carrier/separated inclusion. -/
@[simp]
theorem fixedSlotHilbertInclusion_hilbertState
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotHilbertInclusion Q hPQ (P.hilbertState F) =
      Q.hilbertState (P.fixedSlotCarrierInclusion Q hPQ F) := by
  change
    P.fixedSlotHilbertLinearIsometry Q hPQ
        (P.osClass F : Completion P.Separated) =
      (Q.osClass (P.fixedSlotCarrierInclusion Q hPQ F) :
        Completion Q.Separated)
  rw [P.fixedSlotHilbertLinearIsometry_coe]
  rw [P.fixedSlotSeparatedLinearIsometry_osClass]

/-- Identity slot inclusion extends to the identity on the Hilbert completion. -/
theorem fixedSlotHilbertInclusion_refl
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (x : P.Hilbert) :
    P.fixedSlotHilbertInclusion P (fun _ h => h) x = x := by
  change P.fixedSlotHilbertLinearIsometry P (fun _ h => h) x = x
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq
        (P.fixedSlotHilbertLinearIsometry P (fun _ h => h)).continuous
        continuous_id
  | ih x =>
      rw [P.fixedSlotHilbertLinearIsometry_coe]
      change
        (P.fixedSlotSeparatedInclusion P (fun _ h => h) x :
          Completion P.Separated) =
        (x : Completion P.Separated)
      rw [P.fixedSlotSeparatedInclusion_refl]

/-- Successive Hilbert-completion inclusions are coherent. -/
theorem fixedSlotHilbertInclusion_trans
    (P Q R : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (hQR : Q.slots ⊆ R.slots)
    (x : P.Hilbert) :
    Q.fixedSlotHilbertInclusion R hQR
        (P.fixedSlotHilbertInclusion Q hPQ x) =
      P.fixedSlotHilbertInclusion R (fun _ h => hQR (hPQ h)) x := by
  change
    Q.fixedSlotHilbertLinearIsometry R hQR
        (P.fixedSlotHilbertLinearIsometry Q hPQ x) =
      P.fixedSlotHilbertLinearIsometry R (fun _ h => hQR (hPQ h)) x
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq
        ((Q.fixedSlotHilbertLinearIsometry R hQR).continuous.comp
          (P.fixedSlotHilbertLinearIsometry Q hPQ).continuous)
        (P.fixedSlotHilbertLinearIsometry R
          (fun _ h => hQR (hPQ h))).continuous
  | ih x =>
      rw [P.fixedSlotHilbertLinearIsometry_coe]
      rw [Q.fixedSlotHilbertLinearIsometry_coe]
      rw [P.fixedSlotHilbertLinearIsometry_coe]
      change
        (Q.fixedSlotSeparatedInclusion R hQR
            (P.fixedSlotSeparatedInclusion Q hPQ x) :
          Completion R.Separated) =
        (P.fixedSlotSeparatedInclusion R (fun _ h => hQR (hPQ h)) x :
          Completion R.Separated)
      rw [P.fixedSlotSeparatedInclusion_trans Q R hPQ hQR x]

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
