import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSCarrierIsometry
import Mathlib.Analysis.Normed.Group.SeparationQuotient

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

/-- The carrier inclusion descends through the zero-seminorm separation
quotients.  Well-definedness follows from exact distance preservation of the
carrier `LinearIsometry`. -/
noncomputable def fixedSlotSeparatedInclusion
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.Separated →ₗ[ℝ] Q.Separated where
  toFun :=
    Quotient.map'
      (P.fixedSlotCarrierInclusion Q hPQ)
      (by
        intro F G hFG
        rw [Metric.inseparable_iff] at hFG ⊢
        simpa using
          (P.fixedSlotCarrierLinearIsometry Q hPQ).dist_map F G ▸ hFG)
  map_add' := by
    intro x y
    obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨G, rfl⟩ := SeparationQuotient.surjective_mk y
    simp [fixedSlotCarrierInclusion]
  map_smul' := by
    intro r x
    obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
    simp [fixedSlotCarrierInclusion]

/-- The quotient inclusion agrees exactly with the wrapped carrier inclusion on
OS classes. -/
@[simp]
theorem fixedSlotSeparatedInclusion_osClass
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotSeparatedInclusion Q hPQ (P.osClass F) =
      Q.osClass (P.fixedSlotCarrierInclusion Q hPQ F) :=
  rfl

/-- The quotient inclusion preserves norm exactly. -/
theorem fixedSlotSeparatedInclusion_norm
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (x : P.Separated) :
    ‖P.fixedSlotSeparatedInclusion Q hPQ x‖ = ‖x‖ := by
  obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
  rw [P.fixedSlotSeparatedInclusion_osClass]
  simp [osClass, P.fixedSlotCarrierInclusion_norm Q hPQ F]

/-- Canonical fixed-slot inclusion on separated OS carriers as a real linear
isometry. -/
noncomputable def fixedSlotSeparatedLinearIsometry
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.Separated →ₗᵢ[ℝ] Q.Separated where
  toLinearMap := P.fixedSlotSeparatedInclusion Q hPQ
  norm_map' := P.fixedSlotSeparatedInclusion_norm Q hPQ

@[simp]
theorem fixedSlotSeparatedLinearIsometry_osClass
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotSeparatedLinearIsometry Q hPQ (P.osClass F) =
      Q.osClass (P.fixedSlotCarrierInclusion Q hPQ F) :=
  rfl

/-- Identity slot inclusion is the identity on the separated OS carrier. -/
theorem fixedSlotSeparatedInclusion_refl
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (x : P.Separated) :
    P.fixedSlotSeparatedInclusion P (fun _ h => h) x = x := by
  obtain ⟨F, rfl⟩ := SeparationQuotient.surjective_mk x
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
  rw [P.fixedSlotSeparatedInclusion_osClass]
  rw [Q.fixedSlotSeparatedInclusion_osClass]
  rw [P.fixedSlotSeparatedInclusion_osClass]
  rw [P.fixedSlotCarrierInclusion_trans Q R hPQ hQR F]

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
