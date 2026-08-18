import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSCarrierIsometry
import MGAP4D.MathlibAnalytic.RealLinearIsometrySeparationCompletion

/-!
# Isometric inclusion of separated fixed-slot primary scalar OS sectors

The preceding layer proves that enlarging a finite nonnegative rational slot set
induces an exact linear isometry on the OS seminormed carriers and preserves the
null submodule.  This file descends that map through Mathlib's
`SeparationQuotient`.

For `P.slots ⊆ Q.slots`, the separated OS carrier of `P` therefore embeds
linearly and isometrically into the separated OS carrier of `Q`.  The map agrees
with the carrier inclusion on OS classes and satisfies identity/transitivity
coherence.

The descent uses the already-canonical generic
`realLinearIsometrySeparationQuotient`; no parallel quotient machinery is
introduced.

No Hilbert-completion extension, direct limit, time translation, semigroup,
Hamiltonian, or spectral statement is introduced here.
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

/-- First send the smaller fixed-slot seminormed carrier isometrically into the
larger separated carrier by taking the OS class after carrier inclusion. -/
noncomputable def fixedSlotCarrierToSeparatedLinearIsometry
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.FixedSlotCarrier →ₗᵢ[ℝ] Q.Separated where
  toLinearMap :=
    { toFun := fun F => Q.osClass (P.fixedSlotCarrierInclusion Q hPQ F)
      map_add' := by
        intro F G
        simp [osClass]
      map_smul' := by
        intro r F
        simp [osClass] }
  norm_map' := by
    intro F
    simp [osClass, P.fixedSlotCarrierInclusion_norm Q hPQ F]

/-- Canonical fixed-slot inclusion on separated OS carriers.  Mathlib's generic
separation-quotient theorem performs the descent from the seminormed source. -/
noncomputable def fixedSlotSeparatedLinearIsometry
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.Separated →ₗᵢ[ℝ] Q.Separated :=
  realLinearIsometrySeparationQuotient
    (P.fixedSlotCarrierToSeparatedLinearIsometry Q hPQ)

/-- Linear-map view of the separated fixed-slot isometric inclusion. -/
noncomputable def fixedSlotSeparatedInclusion
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.Separated →ₗ[ℝ] Q.Separated :=
  (P.fixedSlotSeparatedLinearIsometry Q hPQ).toLinearMap

/-- The separated inclusion agrees exactly with the wrapped carrier inclusion on
OS classes. -/
@[simp]
theorem fixedSlotSeparatedLinearIsometry_osClass
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotSeparatedLinearIsometry Q hPQ (P.osClass F) =
      Q.osClass (P.fixedSlotCarrierInclusion Q hPQ F) := by
  simpa [fixedSlotSeparatedLinearIsometry,
    fixedSlotCarrierToSeparatedLinearIsometry] using
    realLinearIsometrySeparationQuotient_mk
      (P.fixedSlotCarrierToSeparatedLinearIsometry Q hPQ) F

@[simp]
theorem fixedSlotSeparatedInclusion_osClass
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotSeparatedInclusion Q hPQ (P.osClass F) =
      Q.osClass (P.fixedSlotCarrierInclusion Q hPQ F) := by
  exact P.fixedSlotSeparatedLinearIsometry_osClass Q hPQ F

/-- The quotient inclusion preserves norm exactly. -/
theorem fixedSlotSeparatedInclusion_norm
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (x : P.Separated) :
    ‖P.fixedSlotSeparatedInclusion Q hPQ x‖ = ‖x‖ := by
  exact (P.fixedSlotSeparatedLinearIsometry Q hPQ).norm_map x

/-- Identity slot inclusion is the identity on the separated OS carrier. -/
theorem fixedSlotSeparatedInclusion_refl
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (x : P.Separated) :
    P.fixedSlotSeparatedInclusion P (fun _ h => h) x = x := by
  obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
  change
    P.fixedSlotSeparatedInclusion P (fun _ h => h) (P.osClass F) =
      P.osClass F
  rw [P.fixedSlotSeparatedInclusion_osClass]
  rw [P.fixedSlotCarrierInclusion_refl F]

/-- Successive separated OS inclusions are coherent. -/
theorem fixedSlotSeparatedInclusion_trans
    (P Q R : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (hQR : Q.slots ⊆ R.slots)
    (x : P.Separated) :
    Q.fixedSlotSeparatedInclusion R hQR
        (P.fixedSlotSeparatedInclusion Q hPQ x) =
      P.fixedSlotSeparatedInclusion R (fun q hq => hQR (hPQ hq)) x := by
  obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
  change
    Q.fixedSlotSeparatedInclusion R hQR
        (P.fixedSlotSeparatedInclusion Q hPQ (P.osClass F)) =
      P.fixedSlotSeparatedInclusion R (fun q hq => hQR (hPQ hq))
        (P.osClass F)
  rw [P.fixedSlotSeparatedInclusion_osClass]
  rw [Q.fixedSlotSeparatedInclusion_osClass]
  rw [P.fixedSlotSeparatedInclusion_osClass]
  rw [P.fixedSlotCarrierInclusion_trans Q R hPQ hQR F]

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
