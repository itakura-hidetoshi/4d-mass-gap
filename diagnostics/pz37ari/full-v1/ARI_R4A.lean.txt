import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalInitialMomentVolumeBudgetV5_PZ37ARH
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGlobalActionBudgetWindowObstructionV5_PZ37AAB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ARI — cubic genuine global budget and physical-horizon gate obstruction

Extend ZA's genuine one-coordinate injection to three original spatial
coordinates, keeping the original time-zero plaquette carrier and lists.
The lower bound obstructs only ARH's sufficient log-degree gate, not
the complete moments themselves, the physical partition floor, or the
actual transfer gap. No substitute geometry or altered assumptions.
-/
namespace MGAP4D.MathlibAnalytic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000

local notation "L" => PeriodicHypercubicEvenSideLength
local notation "Coord" => ZMod
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette
local notation "Budget" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget
local notation "c" => ((3071 : ℝ)/3072)

private def p4Q2PZ37ARI_coordinateFamily (H : ℕ)
    (p : Coord (L H) × Coord (L H) × Coord (L H)) : Plaq H :=
  (⟨![0, p.1, p.2.1, p.2.2], by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(⟨1, by decide⟩, ⟨2, by decide⟩), by decide⟩)

private theorem p4Q2PZ37ARI_coordinateFamily_injective (H : ℕ) :
    Function.Injective (p4Q2PZ37ARI_coordinateFamily H) := by
  intro p q hpq
  have hx : p.1 = q.1 := by
    simpa [p4Q2PZ37ARI_coordinateFamily] using
      congrArg (fun z : Plaq H => z.1.1 1) hpq
  have hy : p.2.1 = q.2.1 := by
    simpa [p4Q2PZ37ARI_coordinateFamily] using
      congrArg (fun z : Plaq H => z.1.1 2) hpq
  have hz : p.2.2 = q.2.2 := by
    simpa [p4Q2PZ37ARI_coordinateFamily] using
      congrArg (fun z : Plaq H => z.1.1 3) hpq
  exact Prod.ext hx (Prod.ext hy hz)

/-- Three actual spatial coordinates inject into a single fixed orientation
of the original plaquette list. No full cardinality equality is needed. -/
theorem p4Q2PZ37ARI_spatialPlaquetteCount_ge_cube (H : ℕ) :
    (2*(H+1))^3 ≤ (periodicHypercubicEvenSpatialSlicePlaquetteList H).length := by
  classical
  letI : NeZero (L H) := ⟨by
    change 2*(H+1) ≠ 0
    omega⟩
  let s : Finset (Coord (L H) × Coord (L H) × Coord (L H)) := Finset.univ
  let f := p4Q2PZ37ARI_coordinateFamily H
  have hsub : s.image f ⊆ (periodicHypercubicEvenSpatialSlicePlaquetteList H).toFinset := by
    intro p _hp
    exact List.mem_toFinset.mpr (periodicHypercubicEvenSpatialSlicePlaquette_mem_list H p)
  have hcard : (s.image f).card = s.card :=
    Finset.card_image_of_injective s (p4Q2PZ37ARI_coordinateFamily_injective H)
  have hs : s.card = (2*(H+1))^3 := by
    dsimp [s]
    simp only [Fintype.card_prod, ZMod.card, PeriodicHypercubicEvenSideLength]
    ring
  calc
    (2*(H+1))^3 = s.card := hs.symm
    _ = (s.image f).card := hcard.symm
    _ ≤ (periodicHypercubicEvenSpatialSlicePlaquetteList H).toFinset.card :=
      Finset.card_le_card hsub
    _ ≤ _ := List.toFinset_card_le (periodicHypercubicEvenSpatialSlicePlaquetteList H)

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARI_spatialPlaquetteCount_ge_cube

/-- Cubic lower bound on the actual global action budget, sharpening AAB's
linear lower bound without computing all six orientation counts. -/
theorem p4Q2PZ37ARI_budget_ge_cubic (H : ℕ) :
    16*((H:ℝ)+1)^3 ≤ Budget H := by
  have hN := p4Q2PZ37ARI_spatialPlaquetteCount_ge_cube H
  have hR : (2*((H:ℝ)+1))^3 ≤
      ((periodicHypercubicEvenSpatialSlicePlaquetteList H).length : ℝ) := by
    exact_mod_cast hN
  have hl : 0 ≤ ((periodicHypercubicEvenSpatialSliceLinkList H).length : ℝ) :=
    Nat.cast_nonneg _
  dsimp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume]
  push_cast
  nlinarith only [hR,hl]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARI_budget_ge_cubic

private theorem p4Q2PZ37ARI_scalar_necessary
    (b t x y l : ℝ) (hb : 0 ≤ b) (ht : 0 < t)
    (hl : 0 ≤ l) (hxy : x-1 ≤ t)
    (hB : 16*t^3 ≤ y)
    (hgate : 2*(b*y) ≤ (x-1)*l) :
    32*b*t^2 ≤ l := by
  have hlow := mul_le_mul_of_nonneg_left hB (show 0 ≤ 2*b by positivity)
  have hu := mul_le_mul_of_nonneg_right hxy hl
  have h : (32*b*t^2)*t ≤ l*t := by
    nlinarith only [hlow,hgate,hu]
  by_contra! hbad
  exact (not_lt_of_ge h) (mul_lt_mul_of_pos_right hbad ht)

/-- Any degree not exceeding the actual half-cylinder horizon that passes
ARH's sufficient gate requires an inverse-square coupling budget. -/
theorem p4Q2PZ37ARI_degree_gate_requires_small_beta
    (H n : ℕ) (beta : ℝ) (hb : 0 ≤ beta) (hn : n ≤ H)
    (hgate : 2*(beta*Budget H) ≤ ((n:ℝ)-1)*(-Real.log c)) :
    32*beta*((H:ℝ)+1)^2 ≤ -Real.log c := by
  have hn' : (n:ℝ) ≤ (H:ℝ) := by exact_mod_cast hn
  have hH : 0 ≤ (H:ℝ) := Nat.cast_nonneg _
  have hl : 0 ≤ -Real.log c :=
    neg_nonneg.mpr (Real.log_neg (by norm_num) (by norm_num)).le
  exact p4Q2PZ37ARI_scalar_necessary beta ((H:ℝ)+1) (n:ℝ) (Budget H)
    (-Real.log c) hb (by linarith) hl (by linarith)
    (p4Q2PZ37ARI_budget_ge_cubic H) hgate

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARI_degree_gate_requires_small_beta

/-- For every fixed strictly positive coupling, the original sufficient
global-budget gate fails at all degrees up to the physical horizon for
all sufficiently large volumes. This says nothing negative about the
actual moment threshold, which is a different proposition. -/
theorem p4Q2PZ37ARI_eventually_no_degree_gate
    (beta : ℝ) (hb : 0 < beta) :
    ∃ N : ℕ, ∀ H : ℕ, N ≤ H → ∀ n : ℕ, n ≤ H →
      ¬ 2*(beta*Budget H) ≤ ((n:ℝ)-1)*(-Real.log c) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((-Real.log c)/(32*beta))
  refine ⟨N, ?_⟩
  intro H hNH n hn hgate
  have hN' : (N:ℝ) ≤ (H:ℝ) := by exact_mod_cast hNH
  have hH : 0 ≤ (H:ℝ) := Nat.cast_nonneg _
  have hs : (H:ℝ) ≤ ((H:ℝ)+1)^2 := by
    nlinarith only [hH,sq_nonneg (H:ℝ)]
  have hp : 0 < 32*beta := by positivity
  have hbig := (div_lt_iff₀ hp).mp hN
  have hm := mul_le_mul_of_nonneg_right (hN'.trans hs) hp.le
  have hneed := p4Q2PZ37ARI_degree_gate_requires_small_beta H n beta hb.le hn hgate
  nlinarith only [hbig,hm,hneed]

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARI_eventually_no_degree_gate

/-- No single fixed positive coupling admits ARH's sufficient degree gate
for every volume with the degree restricted by the original horizon. -/
theorem p4Q2PZ37ARI_no_uniform_positive_horizon_gate :
    ¬ ∃ beta : ℝ, 0 < beta ∧ ∀ H : ℕ, ∃ n : ℕ, n ≤ H ∧
      2*(beta*Budget H) ≤ ((n:ℝ)-1)*(-Real.log c) := by
  rintro ⟨beta,hb,hall⟩
  obtain ⟨N,hN⟩ := p4Q2PZ37ARI_eventually_no_degree_gate beta hb
  obtain ⟨n,hn,hgate⟩ := hall N
  exact hN N le_rfl n hn hgate

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ARI_no_uniform_positive_horizon_gate

end
end MGAP4D.MathlibAnalytic
