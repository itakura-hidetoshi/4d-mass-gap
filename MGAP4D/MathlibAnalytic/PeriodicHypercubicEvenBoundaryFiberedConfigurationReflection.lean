import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedCoordinates
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeSideClassification

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Orientation correction on one positive-representative open half.

Only positive time links reverse orientation under Euclidean time reflection. -/
def periodicHypercubicEvenOpenHalfOrientationCorrection
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge) :
    (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge :=
  fun e => if e.1.2 = 0 then (x e)⁻¹ else x e

/-- A reflection-fixed edge in the canonical even-periodic partition cannot be a
time-directed positive link. -/
theorem periodicHypercubicEvenEdge_direction_ne_zero_of_side_fixed
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hfixed : periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.fixed) :
    e.2 ≠ 0 := by
  rcases e with ⟨v, mu⟩
  intro htime
  have hmu : mu = 0 := by simpa using htime
  subst mu
  by_cases hle : (v 0).val ≤ H
  · have hpos :=
      periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le H v hle
    rw [hpos] at hfixed
    cases hfixed
  · have hhalf : H + 1 ≤ (v 0).val := by omega
    have hneg :=
      periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val H v hhalf
    rw [hneg] at hfixed
    cases hfixed

/-- Every edge in the shared fixed sector is fixed pointwise by the physical edge
reflection.  The sector consists of spatial links on the two fixed time slices. -/
theorem periodicHypercubicEvenEdgeReflection_eq_self_of_side_fixed
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hfixed : periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.fixed) :
    periodicHypercubicEvenEdgeReflection H e = e := by
  have hspace : e.2 ≠ 0 :=
    periodicHypercubicEvenEdge_direction_ne_zero_of_side_fixed H e hfixed
  have hval : (e.1 0).val = 0 ∨ (e.1 0).val = H + 1 := by
    by_cases hzero : (e.1 0).val = 0
    · exact Or.inl hzero
    · by_cases hle : (e.1 0).val ≤ H
      · have hpos : 1 ≤ (e.1 0).val := Nat.one_le_iff_ne_zero.mpr hzero
        have hs := periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
          H e hspace hpos hle
        rw [hs] at hfixed
        cases hfixed
      · by_cases hhalf : (e.1 0).val = H + 1
        · exact Or.inr hhalf
        · have hgt : H + 1 < (e.1 0).val := by omega
          have hs :=
            periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
              H e hspace hgt
          rw [hs] at hfixed
          cases hfixed
  rw [periodicHypercubicEvenEdgeReflection_spatial H e hspace]
  apply Prod.ext
  · change periodicHypercubicEvenTimeReflection H e.1 = e.1
    funext i
    by_cases hi : i = 0
    · subst i
      rw [periodicHypercubicEvenTimeReflection_time]
      rcases hval with hzero | hhalf
      · have ht : e.1 0 = 0 := (ZMod.val_eq_zero _).mp hzero
        simp [ht]
      · rw [← ZMod.natCast_zmod_val (e.1 0), hhalf]
        let a : ZMod (PeriodicHypercubicEvenSideLength H) :=
          ((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))
        have hsum : a + a = 0 := by
          dsimp [a]
          rw [← Nat.cast_add]
          have hnat : H + 1 + (H + 1) = PeriodicHypercubicEvenSideLength H := by
            simp only [PeriodicHypercubicEvenSideLength]
            omega
          rw [hnat]
          simp
        change -a = a
        calc
          -a = -a + 0 := by simp
          _ = -a + (a + a) := by rw [hsum]
          _ = a := by abel
    · exact periodicHypercubicEvenTimeReflection_space H e.1 hi
  · rfl

/-- Exact boundary-coordinate form of physical configuration reflection.

The shared boundary is pointwise fixed, while the positive and negative open
halves are exchanged.  On their positive-representative time links, the group
value is inverted to correct the reflected orientation. -/
theorem periodicHypercubicEvenConfigurationReflection_boundaryFiberedAssemble
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (b : (periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration Gauge)
    (x y : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge) :
    periodicHypercubicEvenConfigurationReflection H
        ((periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b x y) =
      (periodicHypercubicEvenEdgeOrbitPartition H).boundaryFiberedAssemble b
        (periodicHypercubicEvenOpenHalfOrientationCorrection H y)
        (periodicHypercubicEvenOpenHalfOrientationCorrection H x) := by
  funext e
  cases hside : periodicHypercubicEvenEdgeSide H e with
  | positive =>
      simp [periodicHypercubicEvenConfigurationReflection,
        periodicHypercubicEvenOpenHalfOrientationCorrection,
        FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
        periodicHypercubicEvenEdgeOrbitPartition, hside,
        periodicHypercubicEvenEdgeSide_reflection,
        periodicHypercubicEvenEdgeReflection_involutive H e,
        periodicHypercubicEvenEdgeReflection_direction]
  | negative =>
      simp [periodicHypercubicEvenConfigurationReflection,
        periodicHypercubicEvenOpenHalfOrientationCorrection,
        FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
        periodicHypercubicEvenEdgeOrbitPartition, hside,
        periodicHypercubicEvenEdgeSide_reflection,
        periodicHypercubicEvenEdgeReflection_involutive H e,
        periodicHypercubicEvenEdgeReflection_direction]
  | fixed =>
      have hspace : e.2 ≠ 0 :=
        periodicHypercubicEvenEdge_direction_ne_zero_of_side_fixed H e hside
      have hrefl : periodicHypercubicEvenEdgeReflection H e = e :=
        periodicHypercubicEvenEdgeReflection_eq_self_of_side_fixed H e hside
      rw [periodicHypercubicEvenConfigurationReflection_spatial H _ e hspace]
      rw [hrefl]
      simp [FiniteInvolutiveEdgeOrbitPartition.boundaryFiberedAssemble,
        periodicHypercubicEvenEdgeOrbitPartition, hside]

end

end MathlibAnalytic
end MGAP4D
