import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSourceTimeCyclicDistanceLocalStep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPlaquetteLocalPathSeparation
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

/-!
# Midpoint support lower bounds for actual plaquette-local path length

The current route now has three compatible finite-geometry ingredients:

* actual Wilson-plaquette-local physical-link paths;
* a genuine cyclic source-time distance on arbitrary physical links;
* an explicit physical-floor lower bound for that cyclic distance on the
  reflected-left / positive-right midpoint supports.

This file joins them.  First, the cyclic distance is identified with the
absolute value of the minimum-absolute `ZMod` representative of a difference.
Mathlib's `valMinAbs` triangle estimate then gives a genuine triangle
inequality.  Since every actual plaquette-local step has cyclic source-time
distance at most one, induction along a path of `d` plaquette-local steps gives
endpoint cyclic distance at most `d`.

Consequently, any uniform physical-floor lower bound `D` for the midpoint
endpoint cyclic separation implies that no actual plaquette-local path of
length `< D` connects the two midpoint supports.

This is a finite support-distance statement only.  It does not assert
covariance decay, a factorial Dobrushin bound, positive mass, a Hamiltonian
gap, or any identification of Markov update time with Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The shorter-residue cyclic distance is the natural absolute value of the
minimum-absolute representative of the corresponding `ZMod` difference. -/
theorem periodicHypercubicEvenTimeCyclicDistance_eq_natAbs_valMinAbs_sub
    (H : ℕ)
    (s t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    periodicHypercubicEvenTimeCyclicDistance H s t =
      (s - t).valMinAbs.natAbs := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  unfold periodicHypercubicEvenTimeCyclicDistance
  by_cases h : t.val ≤ s.val
  · rw [Nat.dist_eq_sub_of_le_right h,
      ZMod.valMinAbs_natAbs_eq_min,
      ZMod.val_sub h]
  · have h' : s.val ≤ t.val := by omega
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le_right h']
    rw [show s - t = -(t - s) by abel,
      ZMod.natAbs_valMinAbs_neg,
      ZMod.valMinAbs_natAbs_eq_min,
      ZMod.val_sub h']

/-- Genuine cyclic time distance satisfies the triangle inequality. -/
theorem periodicHypercubicEvenTimeCyclicDistance_triangle
    (H : ℕ)
    (s t u : ZMod (PeriodicHypercubicEvenSideLength H)) :
    periodicHypercubicEvenTimeCyclicDistance H s u ≤
      periodicHypercubicEvenTimeCyclicDistance H s t +
        periodicHypercubicEvenTimeCyclicDistance H t u := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  rw [periodicHypercubicEvenTimeCyclicDistance_eq_natAbs_valMinAbs_sub,
    periodicHypercubicEvenTimeCyclicDistance_eq_natAbs_valMinAbs_sub,
    periodicHypercubicEvenTimeCyclicDistance_eq_natAbs_valMinAbs_sub]
  have hdecomp : s - u = (s - t) + (t - u) := by
    abel
  rw [hdecomp]
  exact
    (ZMod.natAbs_valMinAbs_add_le (s - t) (t - u)).trans
      (Int.natAbs_add_le _ _)

/-- The source-time cyclic distance of physical links inherits the triangle
inequality. -/
theorem periodicHypercubicEvenSourceTimeCyclicDistance_triangle
    (H : ℕ)
    (e f g : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenSourceTimeCyclicDistance H e g ≤
      periodicHypercubicEvenSourceTimeCyclicDistance H e f +
        periodicHypercubicEvenSourceTimeCyclicDistance H f g := by
  exact
    periodicHypercubicEvenTimeCyclicDistance_triangle H
      (e.1 0) (f.1 0) (g.1 0)

/-- A chain of exactly `d` actual Wilson-plaquette-local steps has endpoint
source-time cyclic distance at most `d`. -/
theorem periodicHypercubicEvenPlaquetteLocalChain_sourceTimeCyclicDistance_le_length
    (H : ℕ) :
    ∀ d : ℕ,
      ∀ γ : Fin (d + 1) → PeriodicHypercubicEvenEdge H,
        (∀ i : Fin d,
          periodicHypercubicEvenPlaquetteLocal H
            (γ i.castSucc) (γ i.succ)) →
          periodicHypercubicEvenSourceTimeCyclicDistance H
            (γ 0) (γ (Fin.last d)) ≤ d := by
  intro d
  induction d with
  | zero =>
      intro γ _
      have hindex : (Fin.last 0 : Fin 1) = 0 := by rfl
      rw [hindex]
      simp [periodicHypercubicEvenSourceTimeCyclicDistance]
  | succ d ih =>
      intro γ hstep
      let γ' : Fin (d + 1) → PeriodicHypercubicEvenEdge H :=
        fun i => γ i.castSucc
      have hprefix :
          ∀ i : Fin d,
            periodicHypercubicEvenPlaquetteLocal H
              (γ' i.castSucc) (γ' i.succ) := by
        intro i
        simpa [γ'] using hstep i.castSucc
      have hih :
          periodicHypercubicEvenSourceTimeCyclicDistance H
              (γ 0) (γ ((Fin.last d).castSucc)) ≤ d := by
        simpa [γ'] using ih γ' hprefix
      have hlastLocal :
          periodicHypercubicEvenPlaquetteLocal H
            (γ ((Fin.last d).castSucc)) (γ (Fin.last (d + 1))) := by
        simpa using hstep (Fin.last d)
      have hlast :
          periodicHypercubicEvenSourceTimeCyclicDistance H
              (γ ((Fin.last d).castSucc)) (γ (Fin.last (d + 1))) ≤ 1 :=
        periodicHypercubicEvenPlaquetteLocal_sourceTimeCyclicDistance_le_one
          H hlastLocal
      have htri :=
        periodicHypercubicEvenSourceTimeCyclicDistance_triangle H
          (γ 0) (γ ((Fin.last d).castSucc)) (γ (Fin.last (d + 1)))
      have hsum :
          periodicHypercubicEvenSourceTimeCyclicDistance H
              (γ 0) (γ (Fin.last (d + 1))) ≤ d + 1 :=
        htri.trans (Nat.add_le_add hih hlast)
      simpa [Nat.succ_eq_add_one] using hsum

/-- Every actual plaquette-local path of length `d` has endpoint cyclic
source-time distance at most `d`. -/
theorem periodicHypercubicEvenPlaquetteLocalPath_sourceTimeCyclicDistance_le_length
    (H d : ℕ)
    {e f : PeriodicHypercubicEvenEdge H}
    (hpath : periodicHypercubicEvenPlaquetteLocalPath H d e f) :
    periodicHypercubicEvenSourceTimeCyclicDistance H e f ≤ d := by
  rcases hpath with ⟨γ, h0, hlast, hstep⟩
  have hchain :=
    periodicHypercubicEvenPlaquetteLocalChain_sourceTimeCyclicDistance_le_length
      H d γ hstep
  simpa [h0, hlast] using hchain

/-- A uniform lower bound on the explicit cyclic physical-floor separation of
the fixed-slot midpoint supports is therefore a lower bound on their actual
Wilson-plaquette-local path separation. -/
theorem
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointSupports_plaquetteLocalSeparatedBy_of_floor_min_ge
    (H : ℕ)
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ)
    (J : Finset ℚ)
    (r : ℚ)
    (D : ℕ)
    (hleftWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((q : ℚ) : ℝ) n) ≤ H)
    (hrightWithin : ∀ q : ℚ, q ∈ J →
      Int.toNat
          (physicalTemporalFloorStep latticeSpacing ((((q + r) + r : ℚ) : ℝ)) n) ≤ H)
    (hfloor : ∀ qLeft : ℚ, qLeft ∈ J → ∀ qRight : ℚ, qRight ∈ J →
      D ≤
        min
          (Int.toNat
              (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
            Int.toNat
              (physicalTemporalFloorStep latticeSpacing
                ((((qRight + r) + r : ℚ) : ℝ)) n))
          (PeriodicHypercubicEvenSideLength H -
            (Int.toNat
                (physicalTemporalFloorStep latticeSpacing ((qLeft : ℚ) : ℝ) n) +
              Int.toNat
                (physicalTemporalFloorStep latticeSpacing
                  ((((qRight + r) + r : ℚ) : ℝ)) n)))) :
    periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointLeftReflectedSupport
        H latticeSpacing n J)
      (periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpointRightSupport
        H latticeSpacing n J r) := by
  intro d hd eLeft heLeft eRight heRight hpath
  have hDdist :
      D ≤ periodicHypercubicEvenSourceTimeCyclicDistance H eLeft eRight :=
    periodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarMidpoint_sourceTimeCyclicDistance_ge_of_floor_min_ge
      H latticeSpacing n J r D hleftWithin hrightWithin hfloor
      eLeft eRight heLeft heRight
  have hdistd :
      periodicHypercubicEvenSourceTimeCyclicDistance H eLeft eRight ≤ d :=
    periodicHypercubicEvenPlaquetteLocalPath_sourceTimeCyclicDistance_le_length
      H d hpath
  omega

end

end MathlibAnalytic
end MGAP4D
