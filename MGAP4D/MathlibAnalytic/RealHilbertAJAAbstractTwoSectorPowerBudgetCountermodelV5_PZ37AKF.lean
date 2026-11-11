import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAJAEventualPowerWitnessV5_PZ37AKE
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKF — Abstract two-sector obstruction to invalid AJA descent

This leaf tests a specific *invalid deduction*, not the genuine SU(2)
Wilson model. Certified AKC/AKD moment log-convexity, positivity, monotone
retention, a small one-step Haar-like budget, and a nonzero decaying
sector do NOT logically entail the original strict AJA finite-power witness.

Consider the positive spectral moment sequence
    a_n = 1/4 + (3/4)*(1/4)^n.
It is the squared-energy moment sequence of an abstract two-sector
positive symmetric norm-one contraction with fixed top energy 1/4,
orthogonal initial energy 3/4, and decaying squared spectral factor 1/4.
Choose an abstract B=1/32 and V=a_0=1.

Then B>0, B<=a_1, B<=V/16, a_n decreases strictly, all moments are
log-convex and satisfy the full AKC Cauchy floor, yet a_n>=1/4>B
for every n. The top-orthogonal sector is nonzero and decays to zero.

This proves that a numerical comparison of the ACTUAL Wilson full-top
projection against its ACTUAL Haar budget is indispensable. The model
above is NOT a counterexample to the genuine original Wilson claim,
which remains OPEN. Never substitute these abstract numbers for the
true Wilson/Haar/ZW/AJA definitions or assert a physical no-go.
-/

namespace MGAP4D.MathlibAnalytic

open Filter
open scoped Topology Classical

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Abstract two-sector squared energy: true fixed sector plus a
nonzero decaying sector; not the original SU(2) transfer. -/
def p4Q2PZ37AKF_twoSectorEnergy (n : ℕ) : ℝ :=
  (1 : ℝ) / 4 + ((3 : ℝ) / 4) * ((1 : ℝ) / 4) ^ n

theorem p4Q2PZ37AKF_twoSectorEnergy_zero :
    p4Q2PZ37AKF_twoSectorEnergy 0 = 1 := by
  norm_num [p4Q2PZ37AKF_twoSectorEnergy]

theorem p4Q2PZ37AKF_twoSectorEnergy_one :
    p4Q2PZ37AKF_twoSectorEnergy 1 = (7 : ℝ) / 16 := by
  norm_num [p4Q2PZ37AKF_twoSectorEnergy]

/-- Adjacent squared moments satisfy EXACTLY the AKC log-convexity
condition, even though no strict budget witness exists. -/
theorem p4Q2PZ37AKF_twoSectorEnergy_logConvex :
    ∀ n : ℕ,
      (p4Q2PZ37AKF_twoSectorEnergy (n + 1)) ^ 2 ≤
        p4Q2PZ37AKF_twoSectorEnergy n *
          p4Q2PZ37AKF_twoSectorEnergy (n + 1 + 1) := by
  intro n
  let t : ℝ := ((1 : ℝ) / 4) ^ n
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hp1 : ((1 : ℝ) / 4) ^ (n + 1) = t / 4 := by
    dsimp [t]
    rw [pow_succ]
    ring
  have hp2 : ((1 : ℝ) / 4) ^ (n + 1 + 1) = t / 16 := by
    dsimp [t]
    rw [pow_succ, pow_succ]
    ring
  change
    ((1 : ℝ) / 4 + ((3 : ℝ) / 4) * ((1 : ℝ) / 4) ^ (n + 1)) ^ 2 ≤
      ((1 : ℝ) / 4 + ((3 : ℝ) / 4) * ((1 : ℝ) / 4) ^ n) *
        ((1 : ℝ) / 4 + ((3 : ℝ) / 4) * ((1 : ℝ) / 4) ^ (n + 1 + 1))
  rw [hp1, hp2]
  change (1 / 4 + 3 / 4 * (t / 4)) ^ 2 ≤
    (1 / 4 + 3 / 4 * t) * (1 / 4 + 3 / 4 * (t / 16))
  nlinarith only [ht]

/-- Despite strict one-step decay, every moment retains nonzero
fixed-top energy 1/4. -/
theorem p4Q2PZ37AKF_twoSectorEnergy_strict_drop
    (n : ℕ) :
    p4Q2PZ37AKF_twoSectorEnergy (n + 1) <
      p4Q2PZ37AKF_twoSectorEnergy n := by
  have ht : 0 < ((1 : ℝ) / 4) ^ n := by positivity
  have hp : ((1 : ℝ) / 4) ^ (n + 1) =
      ((1 : ℝ) / 4) ^ n / 4 := by
    rw [pow_succ]
    ring
  unfold p4Q2PZ37AKF_twoSectorEnergy
  rw [hp]
  nlinarith only [ht]

/-- Abstract analogue of B>0, B<=a_1 and B<=V/16: all hold
simultaneously, without any numerical strict AJA witness. -/
theorem p4Q2PZ37AKF_twoSectorHaarLikeBudget :
    (0 : ℝ) < 1 / 32 ∧
      (1 : ℝ) / 32 ≤ p4Q2PZ37AKF_twoSectorEnergy 1 ∧
      (1 : ℝ) / 32 ≤ p4Q2PZ37AKF_twoSectorEnergy 0 / 16 := by
  norm_num [p4Q2PZ37AKF_twoSectorEnergy]

/-- The all-positive power lower floor follows from the same verified
AKC generic log-convex theorem. -/
theorem p4Q2PZ37AKF_twoSectorAllPositivePowerFloor (n : ℕ) :
    ((1 : ℝ) / 32) ^ (n + 1) ≤
      (p4Q2PZ37AKF_twoSectorEnergy 0) ^ n *
        p4Q2PZ37AKF_twoSectorEnergy (n + 1) := by
  have h0 : 0 < p4Q2PZ37AKF_twoSectorEnergy 0 := by
    norm_num [p4Q2PZ37AKF_twoSectorEnergy]
  have h1 : 0 < p4Q2PZ37AKF_twoSectorEnergy 1 := by
    norm_num [p4Q2PZ37AKF_twoSectorEnergy]
  have hPow :=
    real_positive_logConvex_sequence_powerFloor_akc
      p4Q2PZ37AKF_twoSectorEnergy h0 h1
      p4Q2PZ37AKF_twoSectorEnergy_logConvex n
  have hB : (1 : ℝ) / 32 ≤ p4Q2PZ37AKF_twoSectorEnergy 1 := by
    norm_num [p4Q2PZ37AKF_twoSectorEnergy]
  exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 32)
    hB (n + 1)).trans hPow

/-- A bona fide obstruction to deriving an unconditional AJA witness
from ONLY the abstract certified numerical moment properties. -/
theorem p4Q2PZ37AKF_twoSector_no_strict_HaarLike_witness :
    ¬ ∃ n : ℕ, 0 < n ∧
      p4Q2PZ37AKF_twoSectorEnergy n < (1 : ℝ) / 32 := by
  rintro ⟨n, _hn, hSmall⟩
  have ht : 0 ≤ ((1 : ℝ) / 4) ^ n := by positivity
  unfold p4Q2PZ37AKF_twoSectorEnergy at hSmall
  nlinarith only [ht, hSmall]

/-- Even in the presence of exact convergence to the full-top energy
and a strictly decaying complementary sector, there can be no witness. -/
theorem p4Q2PZ37AKF_twoSector_tendsto_fullTop :
    Tendsto p4Q2PZ37AKF_twoSectorEnergy atTop (nhds ((1 : ℝ) / 4)) := by
  have hp :
      Tendsto (fun n : ℕ => ((1 : ℝ) / 4) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hconst :
      Tendsto (fun _ : ℕ => ((1 : ℝ) / 4)) atTop (nhds ((1 : ℝ) / 4)) :=
    tendsto_const_nhds
  have htail :
      Tendsto (fun n : ℕ => ((3 : ℝ) / 4) * ((1 : ℝ) / 4) ^ n)
        atTop (nhds 0) := by
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ) / 4)
      atTop (nhds ((3 : ℝ) / 4))).mul hp using 1 <;> norm_num
  simpa only [p4Q2PZ37AKF_twoSectorEnergy, add_zero] using
    hconst.add htail

end
end MGAP4D.MathlibAnalytic

/-! Eight kernel declarations audited on pinned Lean/mathlib; no sorry/admit/new axiom. -/
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKF_twoSectorEnergy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKF_twoSectorEnergy_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKF_twoSectorEnergy_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKF_twoSectorEnergy_logConvex
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKF_twoSectorEnergy_strict_drop
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKF_twoSectorHaarLikeBudget
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKF_twoSectorAllPositivePowerFloor
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKF_twoSector_no_strict_HaarLike_witness
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKF_twoSector_tendsto_fullTop
