import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFixedSlotOSInclusion

/-!
# Isometric inclusion of fixed-slot primary scalar OS seminormed carriers

The preceding inclusion theorem proves that enlarging a finite nonnegative
rational slot set leaves the full path observable and the continuum OS quadratic
form exactly unchanged.  This file upgrades that exact equality to the
seminormed carrier created by the OS/GNS core.

For two fixed-slot reconstruction data `P` and `Q` over the same continuum law,
with `P.slots ⊆ Q.slots`, the canonical observable inclusion is a real linear
isometry.  In particular it preserves the OS null submodule exactly.  Identity
and transitivity are inherited from the underlying cylinder inclusion.

No quotient lift, Hilbert completion map, directed limit, time translation,
semigroup, Hamiltonian, or spectral claim is made here.
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

/-- Linear inclusion of the wrapped OS seminormed carrier along an inclusion of
finite rational slot sets. -/
noncomputable def fixedSlotCarrierInclusion
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.FixedSlotCarrier →ₗ[ℝ] Q.FixedSlotCarrier where
  toFun F :=
    ⟨periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
      P.slots Q.slots hPQ F.observable⟩
  map_add' F G := by
    apply FixedSlotCarrier.observable_injective Q
    change
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          P.slots Q.slots hPQ (F.observable + G.observable) =
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
            P.slots Q.slots hPQ F.observable +
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
            P.slots Q.slots hPQ G.observable
    exact map_add _ _ _
  map_smul' r F := by
    apply FixedSlotCarrier.observable_injective Q
    change
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          P.slots Q.slots hPQ (r • F.observable) =
        r • periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          P.slots Q.slots hPQ F.observable
    exact map_smul _ _ _

@[simp]
theorem fixedSlotCarrierInclusion_observable
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F : P.FixedSlotCarrier) :
    (P.fixedSlotCarrierInclusion Q hPQ F).observable =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        P.slots Q.slots hPQ F.observable :=
  rfl

/-- Slot enlargement preserves the induced OS inner product exactly. -/
theorem fixedSlotCarrierInclusion_inner
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F G : P.FixedSlotCarrier) :
    inner ℝ (P.fixedSlotCarrierInclusion Q hPQ F)
        (P.fixedSlotCarrierInclusion Q hPQ G) =
      inner ℝ F G := by
  rw [Q.inner_eq_fixedSlotOSBilinForm, P.inner_eq_fixedSlotOSBilinForm]
  exact
    L.fixedSlotOSBilinForm_inclusion
      H N hN beta hbeta latticeSpacing
      P.slots Q.slots hPQ F.observable G.observable

/-- Exact OS quadratic preservation implies exact seminorm preservation. -/
theorem fixedSlotCarrierInclusion_norm
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F : P.FixedSlotCarrier) :
    ‖P.fixedSlotCarrierInclusion Q hPQ F‖ = ‖F‖ := by
  have hsq :
      ‖P.fixedSlotCarrierInclusion Q hPQ F‖ ^ 2 = ‖F‖ ^ 2 := by
    calc
      ‖P.fixedSlotCarrierInclusion Q hPQ F‖ ^ 2 =
          inner ℝ (P.fixedSlotCarrierInclusion Q hPQ F)
            (P.fixedSlotCarrierInclusion Q hPQ F) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ F F :=
        P.fixedSlotCarrierInclusion_inner Q hPQ F F
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
  nlinarith [norm_nonneg (P.fixedSlotCarrierInclusion Q hPQ F), norm_nonneg F]

/-- The canonical fixed-slot carrier inclusion as a Mathlib real linear
isometry. -/
noncomputable def fixedSlotCarrierLinearIsometry
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots) :
    P.FixedSlotCarrier →ₗᵢ[ℝ] Q.FixedSlotCarrier where
  toLinearMap := P.fixedSlotCarrierInclusion Q hPQ
  norm_map' := P.fixedSlotCarrierInclusion_norm Q hPQ

@[simp]
theorem fixedSlotCarrierLinearIsometry_apply
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotCarrierLinearIsometry Q hPQ F =
      P.fixedSlotCarrierInclusion Q hPQ F :=
  rfl

/-- The inclusion preserves and reflects the OS null submodule. -/
theorem mem_nullSubmodule_fixedSlotCarrierInclusion_iff
    (P Q : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotCarrierInclusion Q hPQ F ∈ Q.nullSubmodule ↔
      F ∈ P.nullSubmodule := by
  change ‖P.fixedSlotCarrierInclusion Q hPQ F‖ = 0 ↔ ‖F‖ = 0
  rw [P.fixedSlotCarrierInclusion_norm Q hPQ F]

/-- Identity slot inclusion is the identity on the wrapped OS carrier. -/
theorem fixedSlotCarrierInclusion_refl
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (F : P.FixedSlotCarrier) :
    P.fixedSlotCarrierInclusion P (fun _ h => h) F = F := by
  apply FixedSlotCarrier.observable_injective P
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        P.slots P.slots (fun _ h => h) F.observable = F.observable
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion_refl
      P.slots F.observable

/-- Successive wrapped carrier inclusions are coherent. -/
theorem fixedSlotCarrierInclusion_trans
    (P Q R : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (hPQ : P.slots ⊆ Q.slots)
    (hQR : Q.slots ⊆ R.slots)
    (F : P.FixedSlotCarrier) :
    Q.fixedSlotCarrierInclusion R hQR
        (P.fixedSlotCarrierInclusion Q hPQ F) =
      P.fixedSlotCarrierInclusion R (fun q hq => hQR (hPQ hq)) F := by
  apply FixedSlotCarrier.observable_injective R
  change
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        Q.slots R.slots hQR
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
          P.slots Q.slots hPQ F.observable) =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion
        P.slots R.slots (fun q hq => hQR (hPQ hq)) F.observable
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarFixedSlotObservableInclusion_trans
      P.slots Q.slots R.slots hPQ hQR F.observable

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
