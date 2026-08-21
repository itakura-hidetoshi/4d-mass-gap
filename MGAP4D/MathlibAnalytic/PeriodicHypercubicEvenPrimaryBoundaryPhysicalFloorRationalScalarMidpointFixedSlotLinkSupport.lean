import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPlaquetteReflectedLinkSupport
import Mathlib.Tactic

/-!
# Fixed-slot physical-link support of scalar midpoint observables

The actual Wilson-source midpoint covariance is built from two literal finite
slot observables.  The left factor reads reflected coordinates `-q`, while the
right factor reads positive coordinates `q + 2r`.  The preceding two support
layers give a concrete four-link support for each individual coordinate.

This file takes the finite union over a slot set `J`.  It thereby produces one
finite physical-link support for the complete left observable, one for the
complete right observable, and their union for the literal midpoint product.
Agreement of two full Wilson configurations on these supports is sufficient to
identify the corresponding observable values.

This is finite support geometry only.  No support-distance lower bound,
covariance decay, Dobrushin threshold, continuum premise, stochastic-time
identification, positive mass, or Hamiltonian gap is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite physical-link support of all reflected scalar coordinates `-q` read
by a fixed finite slot set `J`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftFixedSlotSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ) :
    Finset (PeriodicHypercubicEvenEdge H) := by
  classical
  exact J.biUnion fun q =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
      H latticeSpacing n q

/-- Every reflected single-coordinate support contributing to `J` is contained
in the left fixed-slot support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_subset_midpointLeftFixedSlotSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (q : J)
    (e : PeriodicHypercubicEvenEdge H)
    (he :
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
          H latticeSpacing n q.1) :
    e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftFixedSlotSupport
        H latticeSpacing n J := by
  classical
  exact Finset.mem_biUnion.mpr ⟨q.1, q.2, he⟩

/-- Finite physical-link support of all positive midpoint coordinates `q+2r`
read by the right fixed-slot observable. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightFixedSlotSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ) :
    Finset (PeriodicHypercubicEvenEdge H) := by
  classical
  exact J.biUnion fun q =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
      H latticeSpacing n ((q + r) + r)

/-- Every positive single-coordinate support contributing to the midpoint-right
slot family is contained in the right fixed-slot support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_subset_midpointRightFixedSlotSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (q : J)
    (e : PeriodicHypercubicEvenEdge H)
    (he :
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n ((q.1 + r) + r)) :
    e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightFixedSlotSupport
        H latticeSpacing n J r := by
  classical
  exact Finset.mem_biUnion.mpr ⟨q.1, q.2, he⟩

/-- The complete finite physical-link support of the literal midpoint pair. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPairFixedSlotSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ) :
    Finset (PeriodicHypercubicEvenEdge H) := by
  classical
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftFixedSlotSupport
        H latticeSpacing n J ∪
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightFixedSlotSupport
        H latticeSpacing n J r

/-- The complete left fixed-slot observable depends only on its reflected
finite-link support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftObservable_eq_of_eqOn_fixedSlotSupport
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftFixedSlotSupport
          H latticeSpacing n J →
      A e = B e) :
    F (fun q : J =>
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) (-q.1)) =
      F (fun q : J =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n B) (-q.1)) := by
  have hcoords :
      (fun q : J =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A) (-q.1)) =
        (fun q : J =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
            H N
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
              H latticeSpacing n B) (-q.1)) := by
    funext q
    apply
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_neg_eq_of_eqOn_reflectedSupport
        H N latticeSpacing n q.1 (hJ q) A B
    intro e he
    exact hAB e
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_subset_midpointLeftFixedSlotSupport
        H latticeSpacing n J q e he)
  rw [hcoords]

/-- The complete right fixed-slot observable depends only on its positive
finite-link support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightObservable_eq_of_eqOn_fixedSlotSupport
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightFixedSlotSupport
          H latticeSpacing n J r →
      A e = B e) :
    F (fun q : J =>
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) ((q.1 + r) + r)) =
      F (fun q : J =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n B) ((q.1 + r) + r)) := by
  have hcoords :
      (fun q : J =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A) ((q.1 + r) + r)) =
        (fun q : J =>
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
            H N
            (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
              H latticeSpacing n B) ((q.1 + r) + r)) := by
    funext q
    have hqr : 0 ≤ (q.1 + r) + r :=
      add_nonneg (add_nonneg (hJ q) hr) hr
    apply
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_eq_of_eqOn_support
        H N latticeSpacing n ((q.1 + r) + r) hqr A B
    intro e he
    exact hAB e
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_subset_midpointRightFixedSlotSupport
        H latticeSpacing n J r q e he)
  rw [hcoords]

/-- The literal midpoint product observable depends only on the union of the
left and right fixed-slot physical-link supports. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductObservable_eq_of_eqOn_pairFixedSlotSupport
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (hJ : ∀ q : J, (0 : ℚ) ≤ q.1)
    (hr : 0 ≤ r)
    (F G : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointPairFixedSlotSupport
          H latticeSpacing n J r →
      A e = B e) :
    F (fun q : J =>
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) (-q.1)) *
      G (fun q : J =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n A) ((q.1 + r) + r)) =
    F (fun q : J =>
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n B) (-q.1)) *
      G (fun q : J =>
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
          H N
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
            H latticeSpacing n B) ((q.1 + r) + r)) := by
  have hleft : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftFixedSlotSupport
          H latticeSpacing n J →
      A e = B e := by
    intro e he
    apply hAB e
    exact Finset.mem_union.mpr (Or.inl he)
  have hright : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightFixedSlotSupport
          H latticeSpacing n J r →
      A e = B e := by
    intro e he
    apply hAB e
    exact Finset.mem_union.mpr (Or.inr he)
  have hleftObs :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftObservable_eq_of_eqOn_fixedSlotSupport
      H N latticeSpacing n J hJ F A B hleft
  have hrightObs :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightObservable_eq_of_eqOn_fixedSlotSupport
      H N latticeSpacing n J r hJ hr G A B hright
  rw [hleftObs, hrightObs]

end

end MathlibAnalytic
end MGAP4D
