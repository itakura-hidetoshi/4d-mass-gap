import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointPairHaarL2Equiv
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkConditionalExpectation
import Mathlib.Tactic

/-!
# Transport genuine ground-state joint conditional expectations to pair Haar

The positive ground-state joint density now gives an exact real-linear
isometric equivalence

  U : L²(pair Haar) ≃ₗᵢ[ℝ] L²(ground-state joint).

Hence every genuine bounded joint operator `A` has a lossless pair-Haar
conjugate

  U⁻¹ A U.

For the actual Wilson conditional expectations this removes the range defect
that would arise from projected compression through a non-surjective
isometry.  In particular, one-link and six-spatial-color residual norms are
preserved exactly, and the existing one-link ≤ color residual comparison
transports verbatim to pair Haar.

This file is a change-of-carrier theorem only.  It does not identify a
conditional expectation with the physical transfer operator and does not
reintroduce H1-D5 exact descent.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

local instance groundStateJointPairHaarCondExpTransportTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointPairHaarCondExpTransportCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointPairHaarCondExpTransportSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointPairHaarCondExpTransportMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointPairHaarCondExpTransportBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointPairHaarCondExpTransportSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Lossless conjugation of an arbitrary bounded ground-state joint operator
back to the ordered pair-Haar carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  (((U.symm :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) ∘L A) ∘L
    (U :
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta))

/-- Pointwise form of the lossless joint-to-pair-Haar conjugation. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate_apply
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate
        H N hN beta hbeta A x =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta).symm
        (A
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x)) := by
  rfl

/-- Conjugation through the half-density equivalence preserves every operator
residual norm exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate_residual_norm_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate
          H N hN beta hbeta A x‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x -
        A
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x)‖ := by
  let U :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
      H N hN beta hbeta
  let Q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate
      H N hN beta hbeta A
  have hQ : U (Q x) = A (U x) := by
    change
      U
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate
            H N hN beta hbeta A x) =
        A (U x)
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate_apply]
    exact U.apply_symm_apply (A (U x))
  change ‖x - Q x‖ = ‖U x - A (U x)‖
  calc
    ‖x - Q x‖ = ‖U (x - Q x)‖ := (U.norm_map (x - Q x)).symm
    _ = ‖U x - U (Q x)‖ := by rw [U.map_sub]
    _ = ‖U x - A (U x)‖ := by rw [hQ]

/-- Squared residual form of exact isometric conjugation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate_residual_sq_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →L[ℝ]
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate
          H N hN beta hbeta A x‖ ^ 2 =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x -
        A
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x)‖ ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate_residual_norm_eq]

/-- Genuine one-link ground-state conditional expectation, conjugated exactly
to pair Haar. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta target)

/-- Six-spatial-color ground-state conditional expectation, conjugated exactly
to pair Haar. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate
    H N hN beta hbeta
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
      H N hN beta hbeta color)

/-- One-link pair-Haar residual is exactly the genuine joint one-link
conditional-expectation residual of the half-density image. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2_residual_norm_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2
          H N hN beta hbeta target x‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x)‖ := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate_residual_norm_eq
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
        H N hN beta hbeta target)
      x

/-- Six-color pair-Haar residual is exactly the genuine joint color
conditional-expectation residual of the half-density image. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2_residual_norm_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2
          H N hN beta hbeta color x‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x)‖ := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOperatorPairHaarConjugate_residual_norm_eq
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
        H N hN beta hbeta color)
      x

/-- Squared one-link residual identity on pair Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2_residual_sq_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2
          H N hN beta hbeta target x‖ ^ 2 =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x)‖ ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2_residual_norm_eq]

/-- Squared six-color residual identity on pair Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2_residual_sq_eq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2
          H N hN beta hbeta color x‖ ^ 2 =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
            H N hN beta hbeta x)‖ ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2_residual_norm_eq]

/-- The genuine one-link residual remains no larger than its six-spatial-color
residual after exact transport to pair Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2_residual_norm_le_color
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2
          H N hN beta hbeta target x‖ ≤
      ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2
          H N hN beta hbeta
          (periodicHypercubicEvenSpatialSliceLinkColor H target) x‖ := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2_residual_norm_eq,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2_residual_norm_eq]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_residual_norm_le_color
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta x)

/-- Squared-energy form of the transported one-link ≤ color residual
comparison. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2_residual_sq_le_color
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (x : PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N) :
    ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2
          H N hN beta hbeta target x‖ ^ 2 ≤
      ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2
          H N hN beta hbeta
          (periodicHypercubicEvenSpatialSliceLinkColor H target) x‖ ^ 2 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpPairHaarL2_residual_sq_eq,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpPairHaarL2_residual_sq_eq]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_residual_sq_le_color
      H N hN beta hbeta target
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabPairHaarGroundStateJointL2LinearIsometryEquiv
        H N hN beta hbeta x)

end

end MathlibAnalytic
end MGAP4D
