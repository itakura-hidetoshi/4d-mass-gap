import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveGraph
import MGAP4D.MathlibAnalytic.PeriodicHypercubicNondegenerateShifts
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Two distinct spatial directions at the same spatial-slice base vertex are
adjacent in the intrinsic active graph: the corresponding positive links are
two boundary edges of their common spatial plaquette. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_adj_sameBase_of_direction_ne
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu nu : PeriodicHypercubicEvenSpatialDirection)
    (hne : mu ≠ nu) :
    (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj
      (v, mu) (v, nu) := by
  have hAxes : mu.1 ≠ nu.1 := by
    intro h
    apply hne
    exact Subtype.ext h
  change
    (v, nu) ≠ (v, mu) ∧
      periodicHypercubicEvenSpatialSliceLinksSharePlaquette H (v, mu) (v, nu)
  constructor
  · intro h
    exact hne (congrArg Prod.snd h).symm
  · by_cases hlt : mu.1 < nu.1
    · let pair : PeriodicHypercubicEvenSpatialDirectionPair :=
        ⟨(mu, nu), hlt⟩
      let p : PeriodicHypercubicEvenSpatialSlicePlaquette H := (v, pair)
      have hMu :
          periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p (v, mu) := by
        unfold periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
        refine ⟨0, ?_⟩
        simpa [p, pair] using
          periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_zero H p
      have hNu :
          periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p (v, nu) := by
        unfold periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
        refine ⟨3, ?_⟩
        simpa [p, pair] using
          periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_three H p
      exact ⟨p, hMu, hNu⟩
    · have hnu_le_mu : nu.1 ≤ mu.1 := le_of_not_gt hlt
      have hnu_ne_mu : nu.1 ≠ mu.1 := Ne.symm hAxes
      have hgt : nu.1 < mu.1 := lt_of_le_of_ne hnu_le_mu hnu_ne_mu
      let pair : PeriodicHypercubicEvenSpatialDirectionPair :=
        ⟨(nu, mu), hgt⟩
      let p : PeriodicHypercubicEvenSpatialSlicePlaquette H := (v, pair)
      have hMu :
          periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p (v, mu) := by
        unfold periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
        refine ⟨3, ?_⟩
        simpa [p, pair] using
          periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_three H p
      have hNu :
          periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p (v, nu) := by
        unfold periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
        refine ⟨0, ?_⟩
        simpa [p, pair] using
          periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_zero H p
      exact ⟨p, hMu, hNu⟩

/-- If the base vertex is shifted by a spatial direction different from the
link direction, the original link and the parallel shifted link are opposite
boundary edges of one spatial plaquette, hence adjacent in the active graph. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_adj_shiftBase_of_direction_ne
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu rho : PeriodicHypercubicEvenSpatialDirection)
    (hne : mu ≠ rho) :
    (periodicHypercubicEvenSpatialSliceActiveGraph H).Adj
      (v, mu)
      (periodicHypercubicEvenSpatialSliceShift H v rho, mu) := by
  have hAxes : mu.1 ≠ rho.1 := by
    intro h
    apply hne
    exact Subtype.ext h
  have hSide : 2 ≤ PeriodicHypercubicEvenSideLength H := by
    simp [PeriodicHypercubicEvenSideLength]
  have hShiftNe :
      periodicHypercubicEvenSpatialSliceShift H v rho ≠ v := by
    intro h
    have hBase :
        periodicHypercubicShift
            (PeriodicHypercubicEvenSideLength H) v.1 rho.1 = v.1 := by
      exact congrArg Subtype.val h
    exact
      periodicHypercubicShift_ne_self
        (PeriodicHypercubicEvenSideLength H) hSide v.1 rho.1 hBase
  change
    (periodicHypercubicEvenSpatialSliceShift H v rho, mu) ≠ (v, mu) ∧
      periodicHypercubicEvenSpatialSliceLinksSharePlaquette H
        (v, mu)
        (periodicHypercubicEvenSpatialSliceShift H v rho, mu)
  constructor
  · intro h
    exact hShiftNe (congrArg Prod.fst h)
  · by_cases hlt : mu.1 < rho.1
    · let pair : PeriodicHypercubicEvenSpatialDirectionPair :=
        ⟨(mu, rho), hlt⟩
      let p : PeriodicHypercubicEvenSpatialSlicePlaquette H := (v, pair)
      have hMu :
          periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p (v, mu) := by
        unfold periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
        refine ⟨0, ?_⟩
        simpa [p, pair] using
          periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_zero H p
      have hShift :
          periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p
            (periodicHypercubicEvenSpatialSliceShift H v rho, mu) := by
        unfold periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
        refine ⟨2, ?_⟩
        simpa [p, pair] using
          periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_two H p
      exact ⟨p, hMu, hShift⟩
    · have hrho_le_mu : rho.1 ≤ mu.1 := le_of_not_gt hlt
      have hrho_ne_mu : rho.1 ≠ mu.1 := Ne.symm hAxes
      have hgt : rho.1 < mu.1 := lt_of_le_of_ne hrho_le_mu hrho_ne_mu
      let pair : PeriodicHypercubicEvenSpatialDirectionPair :=
        ⟨(rho, mu), hgt⟩
      let p : PeriodicHypercubicEvenSpatialSlicePlaquette H := (v, pair)
      have hMu :
          periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p (v, mu) := by
        unfold periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
        refine ⟨3, ?_⟩
        simpa [p, pair] using
          periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_three H p
      have hShift :
          periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink H p
            (periodicHypercubicEvenSpatialSliceShift H v rho, mu) := by
        unfold periodicHypercubicEvenSpatialSlicePlaquetteTouchesLink
        refine ⟨1, ?_⟩
        simpa [p, pair] using
          periodicHypercubicEvenSpatialSlicePlaquetteEmbedding_boundary_one H p
      exact ⟨p, hMu, hShift⟩

/-- Same-base direction changes are reachable in one graph step. -/
theorem periodicHypercubicEvenSpatialSliceActiveGraph_reachable_sameBase
    (H : Nat)
    (v : PeriodicHypercubicEvenSpatialSliceVertex H)
    (mu nu : PeriodicHypercubicEvenSpatialDirection) :
    (periodicHypercubicEvenSpatialSliceActiveGraph H).Reachable
      (v, mu) (v, nu) := by
  by_cases h : mu = nu
  · subst nu
    exact SimpleGraph.Reachable.rfl
  · exact
      (periodicHypercubicEvenSpatialSliceActiveGraph_adj_sameBase_of_direction_ne
        H v mu nu h).reachable

end

end MathlibAnalytic
end MGAP4D
