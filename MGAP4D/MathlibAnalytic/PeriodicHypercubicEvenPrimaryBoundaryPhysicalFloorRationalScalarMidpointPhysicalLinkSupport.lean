import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPlaquetteReflectedLinkSupport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteMidpointWilsonSourceCorrelation
import Mathlib.Tactic

/-!
# Physical-link support of fixed-slot primary scalar midpoint observables

The canonical Wilson-source midpoint observable evaluates one bounded continuous
finite-slot function on reflected coordinates `-q` and another on translated
positive coordinates `q + 2r`.  The preceding support layers expose the four
literal finite Wilson links used by each individual coordinate.

This file packages those single-coordinate supports over a finite rational slot
set.  The left support is the finite union of reflected four-link supports.  The
right support is the finite union of positive four-link supports at the doubled
midpoint translation.  Agreement of two full finite configurations on these
finite unions identifies the complete left and right coordinate vectors, hence
any bounded continuous midpoint observables and their product.

This is finite support geometry only.  No support-distance lower bound,
covariance decay, Dobrushin threshold, stochastic-time identification, positive
mass, or Hamiltonian gap is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite Wilson-link support of the reflected left midpoint coordinate vector
`q ↦ X(-q)` over a finite slot set `J`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ) :
    Finset (PeriodicHypercubicEvenEdge H) := by
  classical
  exact J.biUnion fun q =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
      H latticeSpacing n q

/-- Finite Wilson-link support of the translated right midpoint coordinate
vector `q ↦ X(q + 2r)` over a finite slot set `J`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
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

/-- Combined finite Wilson-link support of the literal midpoint pair. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ) :
    Finset (PeriodicHypercubicEvenEdge H) :=
  periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
      H latticeSpacing n J ∪
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
      H latticeSpacing n J r

/-- Every link in one reflected single-coordinate support belongs to the finite
left midpoint support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_subset_midpointLeftReflectedSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (q : ℚ)
    (hq : q ∈ J)
    (e : PeriodicHypercubicEvenEdge H)
    (he :
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport
          H latticeSpacing n q) :
    e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J := by
  classical
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport,
    Finset.mem_biUnion]
  exact ⟨q, hq, he⟩

/-- Every link in one translated positive single-coordinate support belongs to
the finite right midpoint support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_subset_midpointRightSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r q : ℚ)
    (hq : q ∈ J)
    (e : PeriodicHypercubicEvenEdge H)
    (he :
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n ((q + r) + r)) :
    e ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r := by
  classical
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport,
    Finset.mem_biUnion]
  exact ⟨q, hq, he⟩

/-- Agreement on the finite reflected left support identifies the complete
reflected midpoint coordinate vector. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftCoordinates_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
          H latticeSpacing n J →
      A e = B e) :
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
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_neg_eq_of_eqOn_reflectedSupport
      H N latticeSpacing n q.1 (hJ q.1 q.2) A B
      (fun e he => hAB e
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteReflectedSupport_subset_midpointLeftReflectedSupport
          H latticeSpacing n J q.1 q.2 e he))

/-- Agreement on the finite translated right support identifies the complete
right midpoint coordinate vector. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightCoordinates_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
          H latticeSpacing n J r →
      A e = B e) :
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
  exact
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_eq_of_eqOn_support
      H N latticeSpacing n ((q.1 + r) + r)
      (add_nonneg (add_nonneg (hJ q.1 q.2) hr) hr) A B
      (fun e he => hAB e
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_subset_midpointRightSupport
          H latticeSpacing n J r q.1 q.2 e he))

/-- Any bounded continuous left midpoint observable depends only on the finite
reflected left support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftObservable_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
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
  exact congrArg (fun x => F x)
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftCoordinates_eq_of_eqOn_support
      H N latticeSpacing n J hJ A B hAB)

/-- Any bounded continuous right midpoint observable depends only on the finite
translated right support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightObservable_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
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
  exact congrArg (fun x => F x)
    (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightCoordinates_eq_of_eqOn_support
      H N latticeSpacing n J hJ r hr A B hAB)

/-- The complete literal midpoint product depends only on the combined finite
Wilson-link support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointProductObservable_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (hJ : ∀ q : ℚ, q ∈ J → 0 ≤ q)
    (r : ℚ)
    (hr : 0 ≤ r)
    (F G : BoundedContinuousFunction (∀ q : J, ℝ) ℝ)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupport
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
  have hleft :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftObservable_eq_of_eqOn_support
      H N latticeSpacing n J hJ F A B (fun e he => hAB e (by
        simp [
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupport,
          he]))
  have hright :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightObservable_eq_of_eqOn_support
      H N latticeSpacing n J hJ r hr G A B (fun e he => hAB e (by
        simp [
          periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupport,
          he]))
  rw [hleft, hright]

end

end MathlibAnalytic
end MGAP4D
