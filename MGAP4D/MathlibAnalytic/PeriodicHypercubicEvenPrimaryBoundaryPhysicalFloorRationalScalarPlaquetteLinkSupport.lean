import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPlaquettePathLaw
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryTemporalHalfSectorGeometry
import Mathlib.Tactic

/-!
# Physical-link support of the primary scalar plaquette coordinate

The canonical primary scalar rational path reads one normalized-trace plaquette
coordinate at each nonnegative rational time.  This file exposes the four
actual finite Wilson links on which that scalar coordinate depends.

For a rational slot `q`, the four canonical primary spatial plaquette edges are
translated by the natural physical-floor lattice time selected by `q`.  Their
finite image is the literal link support of the scalar coordinate.  Agreement
of two full finite configurations on those four links is therefore enough to
identify the scalar readout.  Within the primary half extent, supports at two
different floor times are disjoint because all four translated edges retain the
corresponding source-time residue.

This is finite geometry only.  No decay estimate, covariance estimate,
continuum premise, stochastic-time identification, or mass-gap conclusion is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The `k`-th actual finite Wilson edge read by the canonical primary scalar
plaquette coordinate at rational physical-floor time `q`. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (k : Fin 4) :
    PeriodicHypercubicEvenEdge H :=
  periodicHypercubicEdgeTranslationEquiv
    (PeriodicHypercubicEvenSideLength H)
    (periodicHypercubicIntegerTemporalDisplacement
      (PeriodicHypercubicEvenSideLength H)
      (Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) : ℤ))
    (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k)

/-- The finite physical-link support of one canonical primary scalar plaquette
coordinate.  It contains at most the four translated plaquette edges. -/
noncomputable def
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ) :
    Finset (PeriodicHypercubicEvenEdge H) := by
  classical
  exact Finset.univ.image fun k : Fin 4 =>
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
      H latticeSpacing n q k

@[simp]
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_mem_support
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (k : Fin 4) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
        H latticeSpacing n q k ∈
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
        H latticeSpacing n q := by
  classical
  simp [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport]

/-- On a nonnegative rational slot, scalarizing the reflection-completed readout
is literally the normalized trace of the oriented word in the four actual
translated Wilson links. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_apply_eq
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hq : 0 ≤ q)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) q =
      normalizedSpecialUnitaryRealTrace N
        (orientedFourEdgePlaquetteWord
          (fun k =>
            A
              (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
                H latticeSpacing n q k))) := by
  unfold periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout_of_nonnegative
      H latticeSpacing n A q hq]
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteNormalizedTracePrimaryBoundary_eq]
  rfl

/-- The scalar coordinate depends only on its four-link physical support. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_eq_of_eqOn_support
    (H N : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hq : 0 ≤ q)
    (A B : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hAB : ∀ e,
      e ∈
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
          H latticeSpacing n q →
      A e = B e) :
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n A) q =
      periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath
        H N
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalReflectionCompletedPathReadout
          H latticeSpacing n B) q := by
  rw [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_apply_eq
      H N latticeSpacing n q hq A,
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePath_completedReadout_apply_eq
      H N latticeSpacing n q hq B]
  have hlinks :
      (fun k : Fin 4 =>
        A
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n q k)) =
      (fun k : Fin 4 =>
        B
          (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
            H latticeSpacing n q k)) := by
    funext k
    exact hAB _
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_mem_support
        H latticeSpacing n q k)
  rw [hlinks]

/-- Before wraparound, every link in the scalar plaquette support has source-time
residue equal to the selected natural physical-floor step. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTime_val
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q : ℚ)
    (hwithin :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (k : Fin 4) :
    ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
        H latticeSpacing n q k).1 0).val =
      Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) := by
  let m : ℕ :=
    Int.toNat
      (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n)
  have hadd :
      ((periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k).1 0).val + m <
        PeriodicHypercubicEvenSideLength H := by
    rw [periodicHypercubicEvenPrimarySpatialPlaquetteEdge_source_time_val_zero H k]
    simp only [PeriodicHypercubicEvenSideLength]
    dsimp [m]
    omega
  simpa [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge,
    m] using
    (periodicHypercubicEvenIntegerTemporalEdgeTranslation_sourceTime_val_of_add_lt
      H m (periodicHypercubicEvenPrimarySpatialPlaquetteEdge H k) hadd)

/-- Two admissible scalar plaquette supports at different natural floor times
are disjoint physical-link sets. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport_disjoint_of_floor_ne
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (q₁ q₂ : ℚ)
    (hwithin₁ :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q₁ : ℚ) : ℝ) n) ≤ H)
    (hwithin₂ :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q₂ : ℚ) : ℝ) n) ≤ H)
    (hne :
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q₁ : ℚ) : ℝ) n) ≠
        Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q₂ : ℚ) : ℝ) n)) :
    Disjoint
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
        H latticeSpacing n q₁)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport
        H latticeSpacing n q₂) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro e he₁ he₂
  simp only [
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteSupport,
    Finset.mem_image, Finset.mem_univ, true_and] at he₁ he₂
  rcases he₁ with ⟨k₁, hk₁⟩
  rcases he₂ with ⟨k₂, hk₂⟩
  apply hne
  calc
    Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q₁ : ℚ) : ℝ) n) =
      ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n q₁ k₁).1 0).val :=
        (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTime_val
          H latticeSpacing n q₁ hwithin₁ k₁).symm
    _ = (e.1 0).val := by rw [hk₁]
    _ =
      ((periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge
          H latticeSpacing n q₂ k₂).1 0).val := by rw [hk₂]
    _ =
      Int.toNat
        (physicalTemporalFloorStep latticeSpacing ((q₂ : ℚ) : ℝ) n) :=
        periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquetteEdge_sourceTime_val
          H latticeSpacing n q₂ hwithin₂ k₂

end

end MathlibAnalytic
end MGAP4D
