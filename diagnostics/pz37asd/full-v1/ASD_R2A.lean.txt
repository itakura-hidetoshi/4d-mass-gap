import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalParityCycleDimensionV5_PZ37ASC
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialSliceActiveGraphConnectivity
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ASD — literal spatial incidence rank (unvalidated candidate)

Keep the actual ASB boundary. Its image is the zero-total-parity subspace:
unit link columns give the sum of their endpoint deltas, and successive
actual spatial coordinate shifts connect any two vertices. A fixed root
delta then decomposes every zero-total-parity vector. Rank-nullity gives the
numeric rank and the ASC cycle dimension. No uniform spectral or continuum
claim. This source requires direct Lean and real MCP validation before use.
-/
namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

local notation "F" => ZMod 2
local notation "Vtx" => PeriodicHypercubicEvenSpatialSliceVertex
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink
local notation "Dir" => PeriodicHypercubicEvenSpatialDirection
local notation "L" => PeriodicHypercubicEvenSideLength
local notation "Shift" => periodicHypercubicEvenSpatialSliceShift
local notation "Iter" => periodicHypercubicEvenSpatialSliceShiftIterate
local notation "AdjCoord" => periodicHypercubicEvenSpatialSliceAdjustCoordinate
local notation "Bd" => p4Q2PZ37ASB_boundary
local instance p4Q2PZ37ASD_vertexFintype (H : ℕ) : Fintype (Vtx H) := Fintype.ofFinite _
local instance p4Q2PZ37ASD_linkFintype (H : ℕ) : Fintype (Link H) := Fintype.ofFinite _
local instance p4Q2PZ37ASD_sideNeZero (H : ℕ) : NeZero (L H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength, periodicHypercubicEvenPositiveHalfCylinderSlabCount]⟩

private theorem p4Q2PZ37ASD_charTwo (a : F) : a + a = 0 := by
  have h : (2 : F) = 0 := by decide
  calc
    a + a = 2 * a := by ring
    _ = 0 := by rw [h, zero_mul]

private def p4Q2PZ37ASD_root (H : ℕ) : Vtx H :=
  ⟨(0 : PeriodicHypercubicEvenVertex H), by
    simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩

private def p4Q2PZ37ASD_delta (H : ℕ) (v : Vtx H) : Vtx H → F :=
  fun w => if v = w then 1 else 0

local notation "δ" => p4Q2PZ37ASD_delta

/-- Total vertex parity on the literal spatial slice. -/
def p4Q2PZ37ASD_sumMap (H : ℕ) : (Vtx H → F) →ₗ[F] F where
  toFun f := ∑ v : Vtx H, f v
  map_add' f g := by
    change (∑ v : Vtx H, (f v + g v)) = (∑ v : Vtx H, f v) + ∑ v : Vtx H, g v
    exact Finset.sum_add_distrib
  map_smul' c f := by
    change (∑ v : Vtx H, c * f v) = c * ∑ v : Vtx H, f v
    rw [Finset.mul_sum]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_sumMap

private theorem p4Q2PZ37ASD_sum_delta (H : ℕ) (v : Vtx H) :
    p4Q2PZ37ASD_sumMap H (δ H v) = 1 := by
  classical
  change (∑ w : Vtx H, if v = w then (1 : F) else 0) = 1
  simp

/-- Unit column of the exact ASB boundary; no substitute graph. -/
theorem p4Q2PZ37ASD_boundary_column (H : ℕ) (l : Link H) :
    Bd H (fun j => if j = l then 1 else 0) =
      δ H l.1 + δ H (Shift H l.1 l.2) := by
  classical
  funext v
  change (∑ j : Link H, (p4Q2PZ37ASA_incidence H v j : F) *
    (if j = l then 1 else 0)) = δ H l.1 v + δ H (Shift H l.1 l.2) v
  have hs : (∑ j : Link H, (p4Q2PZ37ASA_incidence H v j : F) *
      (if j = l then 1 else 0)) = (p4Q2PZ37ASA_incidence H v l : F) := by
    simp [mul_ite]
  rw [hs]
  unfold p4Q2PZ37ASA_incidence p4Q2PZ37ASD_delta
  rw [Nat.cast_add]
  congr 1 <;> split_ifs <;> rfl

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_boundary_column

private theorem p4Q2PZ37ASD_incidence_eq (H : ℕ) (v : Vtx H) (l : Link H) :
    (p4Q2PZ37ASA_incidence H v l : F) =
      δ H l.1 v + δ H (Shift H l.1 l.2) v := by
  unfold p4Q2PZ37ASA_incidence p4Q2PZ37ASD_delta
  rw [Nat.cast_add]
  congr 1 <;> split_ifs <;> rfl

/-- Every boundary has total vertex parity zero. -/
theorem p4Q2PZ37ASD_range_le_zeroSum (H : ℕ) :
    LinearMap.range (Bd H) ≤ LinearMap.ker (p4Q2PZ37ASD_sumMap H) := by
  classical
  rintro f ⟨p, rfl⟩
  apply LinearMap.mem_ker.mpr
  change (∑ v : Vtx H, ∑ l : Link H,
    (p4Q2PZ37ASA_incidence H v l : F) * p l) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l _
  rw [← Finset.sum_mul]
  have h : (∑ v : Vtx H, (p4Q2PZ37ASA_incidence H v l : F)) = 0 := by
    simp_rw [p4Q2PZ37ASD_incidence_eq, Finset.sum_add_distrib]
    change p4Q2PZ37ASD_sumMap H (δ H l.1) +
      p4Q2PZ37ASD_sumMap H (δ H (Shift H l.1 l.2)) = 0
    rw [p4Q2PZ37ASD_sum_delta, p4Q2PZ37ASD_sum_delta]
    exact p4Q2PZ37ASD_charTwo 1
  rw [h, zero_mul]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_range_le_zeroSum

private theorem p4Q2PZ37ASD_pair_refl (H : ℕ) (v : Vtx H) :
    δ H v + δ H v = 0 := by
  funext w
  exact p4Q2PZ37ASD_charTwo (δ H v w)

private theorem p4Q2PZ37ASD_pair_trans (H : ℕ) (x y z : Vtx H)
    (hxy : δ H x + δ H y ∈ LinearMap.range (Bd H))
    (hyz : δ H y + δ H z ∈ LinearMap.range (Bd H)) :
    δ H x + δ H z ∈ LinearMap.range (Bd H) := by
  have h := (LinearMap.range (Bd H)).add_mem hxy hyz
  have he : (δ H x + δ H y) + (δ H y + δ H z) = δ H x + δ H z := by
    calc
      _ = δ H x + ((δ H y + δ H y) + δ H z) := by abel
      _ = _ := by rw [p4Q2PZ37ASD_pair_refl, zero_add]
  rw [he] at h
  exact h

private theorem p4Q2PZ37ASD_pair_shift (H : ℕ) (v : Vtx H) (d : Dir) :
    δ H v + δ H (Shift H v d) ∈ LinearMap.range (Bd H) := by
  classical
  exact ⟨(fun j => if j = (v,d) then 1 else 0), p4Q2PZ37ASD_boundary_column H (v,d)⟩

private theorem p4Q2PZ37ASD_pair_iterate (H : ℕ) (v : Vtx H) (d : Dir) (n : ℕ) :
    δ H v + δ H (Iter H v d n) ∈ LinearMap.range (Bd H) := by
  induction n with
  | zero =>
    rw [periodicHypercubicEvenSpatialSliceShiftIterate_zero, p4Q2PZ37ASD_pair_refl]
    exact (LinearMap.range (Bd H)).zero_mem
  | succ n ih =>
    rw [periodicHypercubicEvenSpatialSliceShiftIterate_succ]
    exact p4Q2PZ37ASD_pair_trans H _ _ _ ih
      (p4Q2PZ37ASD_pair_shift H (Iter H v d n) d)

private theorem p4Q2PZ37ASD_pair_adjust (H : ℕ) (x y : Vtx H) (d : Dir) :
    δ H x + δ H (AdjCoord H x y d) ∈ LinearMap.range (Bd H) := by
  unfold periodicHypercubicEvenSpatialSliceAdjustCoordinate
  exact p4Q2PZ37ASD_pair_iterate H x d _

/-- Use the three canonical coordinate adjustments, using only existing coordinate reachability. -/
theorem p4Q2PZ37ASD_pair_mem_range (H : ℕ) (x y : Vtx H) :
    δ H x + δ H y ∈ LinearMap.range (Bd H) := by
  let d1 : Dir := ⟨1, by decide⟩
  let d2 : Dir := ⟨2, by decide⟩
  let d3 : Dir := ⟨3, by decide⟩
  let x1 := AdjCoord H x y d1
  let x2 := AdjCoord H x1 y d2
  let x3 := AdjCoord H x2 y d3
  have h1 : δ H x + δ H x1 ∈ LinearMap.range (Bd H) :=
    p4Q2PZ37ASD_pair_adjust H x y d1
  have h2 : δ H x1 + δ H x2 ∈ LinearMap.range (Bd H) :=
    p4Q2PZ37ASD_pair_adjust H x1 y d2
  have h3 : δ H x2 + δ H x3 ∈ LinearMap.range (Bd H) :=
    p4Q2PZ37ASD_pair_adjust H x2 y d3
  have he : x3 = y := by
    change periodicHypercubicEvenSpatialSliceAdjustAllCoordinates H x y = y
    exact periodicHypercubicEvenSpatialSliceAdjustAllCoordinates_eq H x y
  have h := p4Q2PZ37ASD_pair_trans H _ _ _ h1
    (p4Q2PZ37ASD_pair_trans H _ _ _ h2 h3)
  rwa [he] at h

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_pair_mem_range

/-- Exact image characterization of the actual mod-two boundary. -/
theorem p4Q2PZ37ASD_range_eq_zeroSum (H : ℕ) :
    LinearMap.range (Bd H) = LinearMap.ker (p4Q2PZ37ASD_sumMap H) := by
  classical
  apply le_antisymm (p4Q2PZ37ASD_range_le_zeroSum H)
  intro f hf
  have hz := LinearMap.mem_ker.mp hf
  change (∑ v : Vtx H, f v) = 0 at hz
  let r := p4Q2PZ37ASD_root H
  have hm : (∑ v : Vtx H, f v • (δ H r + δ H v)) ∈ LinearMap.range (Bd H) := by
    apply Submodule.sum_mem
    intro v _
    exact (LinearMap.range (Bd H)).smul_mem (f v) (p4Q2PZ37ASD_pair_mem_range H r v)
  have he : (∑ v : Vtx H, f v • (δ H r + δ H v)) = f := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hz, zero_mul, zero_add]
    simp [p4Q2PZ37ASD_delta, mul_ite]
  rwa [he] at hm

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_range_eq_zeroSum

/-- The single remaining linear equation is nonzero. -/
theorem p4Q2PZ37ASD_sum_surjective (H : ℕ) :
    Function.Surjective (p4Q2PZ37ASD_sumMap H) := by
  intro a
  refine ⟨a • δ H (p4Q2PZ37ASD_root H), ?_⟩
  rw [map_smul, p4Q2PZ37ASD_sum_delta, smul_eq_mul, mul_one]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_sum_surjective

/-- Rank of the literal ASB map, with ASC's definition unchanged. -/
theorem p4Q2PZ37ASD_rank (H : ℕ) :
    p4Q2PZ37ASC_boundaryRank H = Nat.card (Vtx H) - 1 := by
  have hs := (p4Q2PZ37ASD_sumMap H).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (p4Q2PZ37ASD_sum_surjective H),
    finrank_top, CommSemiring.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_eq_nat_card] at hs
  rw [p4Q2PZ37ASC_boundaryRank, p4Q2PZ37ASD_range_eq_zeroSum]
  omega

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_rank

/-- Explicit coordinate equivalence of the actual time-zero vertex carrier. -/
private def p4Q2PZ37ASD_vertexEquiv (H : ℕ) :
    Vtx H ≃ (ZMod (L H) × ZMod (L H) × ZMod (L H)) where
  toFun v := (v.1 1, v.1 2, v.1 3)
  invFun p := ⟨![0,p.1,p.2.1,p.2.2], by
    simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i
    · have h := v.2
      unfold periodicHypercubicEvenOnPrimaryReflectionPlane at h
      simpa using h.symm
    · rfl
    · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨a,b,c⟩
    rfl

/-- Exact vertex count, not only the earlier cubic injection lower bound. -/
theorem p4Q2PZ37ASD_vertex_card (H : ℕ) : Nat.card (Vtx H) = 8*(H+1)^3 := by
  rw [← Fintype.card_eq_nat_card, Fintype.card_congr (p4Q2PZ37ASD_vertexEquiv H)]
  simp only [Fintype.card_prod, ZMod.card, PeriodicHypercubicEvenSideLength]
  ring

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_vertex_card

private theorem p4Q2PZ37ASD_direction_card : Nat.card Dir = 3 := by
  let e : Dir ≃ Fin 3 :=
    { toFun := fun d => ⟨d.1.val - 1, by
        have hd := d.1.isLt
        change d.1.val < 4 at hd
        omega⟩
      invFun := fun i => ⟨⟨i.val + 1, by
        have hi := i.isLt
        change i.val + 1 < 4
        omega⟩, by
        intro h
        have hh := congrArg Fin.val h
        change i.val + 1 = 0 at hh
        omega⟩
      left_inv := by
        intro d
        have hd : d.1.val ≠ 0 := by
          intro h
          apply d.2
          apply Fin.ext
          exact h
        apply Subtype.ext
        apply Fin.ext
        change d.1.val - 1 + 1 = d.1.val
        omega
      right_inv := by
        intro i
        apply Fin.ext
        change i.val + 1 - 1 = i.val
        omega }
  exact (Nat.card_congr e).trans (by simp)

/-- Count positively oriented links; parallel edges are not identified. -/
theorem p4Q2PZ37ASD_link_card (H : ℕ) : Nat.card (Link H) = 24*(H+1)^3 := by
  change Nat.card (Vtx H × Dir) = _
  rw [Nat.card_prod, p4Q2PZ37ASD_vertex_card, p4Q2PZ37ASD_direction_card]
  ring

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_link_card

/-- Numeric rank on every genuine even periodic spatial slice. -/
theorem p4Q2PZ37ASD_rank_numeric (H : ℕ) :
    p4Q2PZ37ASC_boundaryRank H = 8*(H+1)^3-1 := by
  rw [p4Q2PZ37ASD_rank, p4Q2PZ37ASD_vertex_card]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_rank_numeric

/-- Exact dimension of ASC's actual closed-pattern space. -/
theorem p4Q2PZ37ASD_cycleDim_numeric (H : ℕ) :
    p4Q2PZ37ASC_cycleDim H = 16*(H+1)^3+1 := by
  have h := p4Q2PZ37ASC_rank_nullity H
  rw [p4Q2PZ37ASD_rank_numeric, p4Q2PZ37ASD_link_card] at h
  have hp0 : 0 < (H+1)^3 := by positivity
  have hp : 1 ≤ (H+1)^3 := by omega
  omega

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_cycleDim_numeric

/-- Exact number of ASC's closed parity patterns. -/
theorem p4Q2PZ37ASD_closed_card_numeric (H : ℕ) :
    (p4Q2PZ37ASB_closedPatterns H).card = 2^(16*(H+1)^3+1) := by
  rw [p4Q2PZ37ASC_closed_card, p4Q2PZ37ASD_cycleDim_numeric]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_closed_card_numeric

/-- Concrete ASC upper bound, still finite-volume and not an actual rank equality. -/
theorem p4Q2PZ37ASD_survivors_le_numeric (H m : ℕ) :
    (p4Q2PZ37ASB_survivors H m).card ≤
      2^(16*(H+1)^3+1) * (p4Q2PZ37ASC_maxMultiplicity m)^(24*(H+1)^3) := by
  simpa only [p4Q2PZ37ASD_cycleDim_numeric, p4Q2PZ37ASD_link_card] using
    p4Q2PZ37ASC_survivors_le_cycleWeight H m

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ASD_survivors_le_numeric

end
end MGAP4D.MathlibAnalytic
