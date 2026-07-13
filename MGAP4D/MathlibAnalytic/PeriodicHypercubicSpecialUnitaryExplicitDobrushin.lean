import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedBoundedTestInfluence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.PeriodicHypercubicActiveNeighborBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSharedPlaquetteUniqueness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Membership in the four-link physical boundary, stated without passing
through the older finite-group instantiation. -/
theorem periodicHypercubicPhysical_mem_plaquetteEdges_iff
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (e : PeriodicHypercubicEdge n) :
    e ∈ periodicHypercubicPlaquetteEdges n p ↔
      periodicHypercubicPlaquetteTouchesEdge n p e := by
  classical
  constructor
  · intro h
    unfold periodicHypercubicPlaquetteEdges at h
    rcases Finset.mem_image.mp h with ⟨k, _hk, rfl⟩
    exact ⟨k, rfl⟩
  · exact periodicHypercubic_mem_plaquetteEdges_of_touches n p e

/-- A physical source link is an active neighbor of the target exactly when a
plaquette touches both links and the links are distinct. -/
theorem periodicHypercubicPhysical_mem_activeNeighbors_iff
    (n : ℕ) [NeZero n]
    (target source : PeriodicHypercubicEdge n) :
    source ∈ periodicHypercubicActiveNeighbors n target ↔
      (∃ p : PeriodicHypercubicPlaquette n,
        periodicHypercubicPlaquetteTouchesEdge n p target ∧
          periodicHypercubicPlaquetteTouchesEdge n p source) ∧
        source ≠ target := by
  classical
  constructor
  · intro h
    unfold periodicHypercubicActiveNeighbors at h
    rcases Finset.mem_biUnion.mp h with ⟨p, hp, hsource⟩
    have hErase := Finset.mem_erase.mp hsource
    refine ⟨⟨p,
      (periodicHypercubic_mem_touchingPlaquettes_iff n target p).mp hp,
      (periodicHypercubicPhysical_mem_plaquetteEdges_iff n p source).mp hErase.2⟩,
      hErase.1⟩
  · rintro ⟨⟨p, hpTarget, hpSource⟩, hNe⟩
    unfold periodicHypercubicActiveNeighbors
    apply Finset.mem_biUnion.mpr
    refine ⟨p,
      (periodicHypercubic_mem_touchingPlaquettes_iff n target p).mpr hpTarget,
      ?_⟩
    apply Finset.mem_erase.mpr
    exact ⟨hNe,
      (periodicHypercubicPhysical_mem_plaquetteEdges_iff n p source).mpr hpSource⟩

/-- The generic compact-oriented shared-plaquette finset of the periodic
`SU(N)` system is exactly the concrete coordinate shared-plaquette finset. -/
theorem periodicHypercubicSpecialUnitary_sharedPlaquettes_eq
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).base.sharedPlaquettes target source =
        periodicHypercubicSharedPlaquettes n target source := by
  classical
  apply Finset.ext
  intro p
  rw [compact_oriented_mem_sharedPlaquettes_iff,
    periodicHypercubic_mem_sharedPlaquettes_iff]
  rfl

/-- Active periodic links share exactly one plaquette in the nondegenerate
periodic regime. -/
theorem periodicHypercubicSpecialUnitary_sharedPlaquetteCard_eq_one_of_active
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n)
    (hActive : source ∈ periodicHypercubicActiveNeighbors n target) :
    ((periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg).base.sharedPlaquettes target source).card = 1 := by
  classical
  have hData :=
    (periodicHypercubicPhysical_mem_activeNeighbors_iff n target source).mp hActive
  rw [periodicHypercubicSpecialUnitary_sharedPlaquettes_eq]
  apply Nat.le_antisymm
  · exact periodicHypercubicSharedPlaquettes_card_le_one
      n hn target source hData.2
  · have hNonempty :
        (periodicHypercubicSharedPlaquettes n target source).Nonempty := by
      rcases hData.1 with ⟨p, hpTarget, hpSource⟩
      exact ⟨p,
        (periodicHypercubic_mem_sharedPlaquettes_iff
          n target source p).2 ⟨hpTarget, hpSource⟩⟩
    exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr hNonempty)

/-- The common off-diagonal influence value for one active periodic neighbor. -/
def periodicHypercubicSpecialUnitaryDobrushinEta
    (beta : ℝ) : ℝ :=
  compactHaarOscillationInfluence (beta * 4)

/-- The periodic `SU(N)` shared-plaquette influence is exactly the common active
value on every active neighbor. -/
theorem periodicHypercubicSpecialUnitary_influence_eq_eta_of_active
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n)
    (hActive : source ∈ periodicHypercubicActiveNeighbors n target) :
    specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg target source =
      periodicHypercubicSpecialUnitaryDobrushinEta beta := by
  classical
  have hData :=
    (periodicHypercubicPhysical_mem_activeNeighbors_iff n target source).mp hActive
  have hNe : target ≠ source := Ne.symm hData.2
  have hCard :=
    periodicHypercubicSpecialUnitary_sharedPlaquetteCard_eq_one_of_active
      n N hn hN beta beta_nonneg target source hActive
  unfold specialUnitaryCompactOrientedSharedPlaquetteInfluence
    periodicHypercubicSpecialUnitaryDobrushinEta
  rw [if_neg hNe, hCard]
  norm_num

/-- A source outside the periodic active-neighbor set has exactly zero explicit
`SU(N)` influence. -/
theorem periodicHypercubicSpecialUnitary_influence_eq_zero_of_not_active
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n)
    (hNotActive : source ∉ periodicHypercubicActiveNeighbors n target) :
    specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg target source = 0 := by
  classical
  by_cases hEq : target = source
  · subst source
    exact specialUnitaryCompactOrientedSharedPlaquetteInfluence_diagonal_zero
      (periodicHypercubicFiniteOrientedGeometry n)
      N hN beta beta_nonneg target
  · have hSharedEmpty :
        periodicHypercubicSharedPlaquettes n target source = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hNonempty
      rcases hNonempty with ⟨p, hp⟩
      rw [periodicHypercubic_mem_sharedPlaquettes_iff] at hp
      exact hNotActive
        ((periodicHypercubicPhysical_mem_activeNeighbors_iff
          n target source).2 ⟨⟨p, hp.1, hp.2⟩, Ne.symm hEq⟩)
    unfold specialUnitaryCompactOrientedSharedPlaquetteInfluence
    rw [if_neg hEq,
      periodicHypercubicSpecialUnitary_sharedPlaquettes_eq,
      hSharedEmpty]
    simp [compactHaarOscillationInfluence,
      HaarLikelihoodRatioInfluence.coefficient]

/-- The explicit periodic compact-Haar `SU(N)` influence row is bounded by
`18` times the common active influence, uniformly in the volume. -/
theorem periodicHypercubicSpecialUnitary_influence_rowSum_le
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    (∑ source : PeriodicHypercubicEdge n,
      specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg target source) ≤
      18 * periodicHypercubicSpecialUnitaryDobrushinEta beta := by
  classical
  let active := periodicHypercubicActiveNeighbors n target
  let eta := periodicHypercubicSpecialUnitaryDobrushinEta beta
  have hSumSupport :
      (∑ source : PeriodicHypercubicEdge n,
        specialUnitaryCompactOrientedSharedPlaquetteInfluence
          (periodicHypercubicFiniteOrientedGeometry n)
          N hN beta beta_nonneg target source) =
        ∑ source ∈ active,
          specialUnitaryCompactOrientedSharedPlaquetteInfluence
            (periodicHypercubicFiniteOrientedGeometry n)
            N hN beta beta_nonneg target source := by
    symm
    apply Finset.sum_subset (Finset.subset_univ active)
    intro source _hUniv hNotMem
    exact periodicHypercubicSpecialUnitary_influence_eq_zero_of_not_active
      n N hN beta beta_nonneg target source hNotMem
  rw [hSumSupport]
  have hEach : ∀ source ∈ active,
      specialUnitaryCompactOrientedSharedPlaquetteInfluence
          (periodicHypercubicFiniteOrientedGeometry n)
          N hN beta beta_nonneg target source = eta := by
    intro source hSource
    exact periodicHypercubicSpecialUnitary_influence_eq_eta_of_active
      n N hn hN beta beta_nonneg target source hSource
  calc
    (∑ source ∈ active,
      specialUnitaryCompactOrientedSharedPlaquetteInfluence
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg target source) =
        (active.card : ℝ) * eta := by
      rw [Finset.sum_congr rfl hEach]
      simp
    _ ≤ 18 * eta := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast periodicHypercubicActiveNeighbors_card_le_eighteen n target
      · unfold eta periodicHypercubicSpecialUnitaryDobrushinEta
        apply compactHaarOscillationInfluence_nonneg
        positivity
    _ = 18 * periodicHypercubicSpecialUnitaryDobrushinEta beta := rfl

/-- The threshold `exp (4 beta) < 19/17` makes the periodic `18 × eta` row
bound strict. -/
theorem periodicHypercubicSpecialUnitary_eighteen_mul_eta_lt_one_of_exp_lt
    (beta : ℝ)
    (hExp : Real.exp (beta * 4) < (19 : ℝ) / 17) :
    18 * periodicHypercubicSpecialUnitaryDobrushinEta beta < 1 := by
  let x : ℝ := Real.exp (beta * 4)
  have hx : x < (19 : ℝ) / 17 := by
    simpa [x] using hExp
  have hden : 0 < x + 1 := by
    dsimp [x]
    positivity
  calc
    18 * periodicHypercubicSpecialUnitaryDobrushinEta beta =
        (18 * (x - 1)) / (x + 1) := by
      dsimp [periodicHypercubicSpecialUnitaryDobrushinEta,
        compactHaarOscillationInfluence,
        HaarLikelihoodRatioInfluence.coefficient, x]
      ring
    _ < 1 := by
      apply (div_lt_iff₀ hden).2
      norm_num at hx ⊢
      nlinarith

/-- The explicit logarithmic small-coupling region for the periodic `SU(N)`
compact-Haar influence matrix. -/
theorem periodicHypercubicSpecialUnitary_eighteen_mul_eta_lt_one_of_beta_lt
    (beta : ℝ)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4) :
    18 * periodicHypercubicSpecialUnitaryDobrushinEta beta < 1 := by
  have hArg : beta * 4 < Real.log ((19 : ℝ) / 17) := by
    nlinarith
  have hRatioPos : 0 < (19 : ℝ) / 17 := by
    norm_num
  have hExp : Real.exp (beta * 4) < (19 : ℝ) / 17 := by
    calc
      Real.exp (beta * 4) <
          Real.exp (Real.log ((19 : ℝ) / 17)) :=
        Real.exp_lt_exp.mpr hArg
      _ = (19 : ℝ) / 17 := Real.exp_log hRatioPos
  exact periodicHypercubicSpecialUnitary_eighteen_mul_eta_lt_one_of_exp_lt
    beta hExp

/-- The actual periodic `SU(N)` compact-Haar conditional laws form a strict
Dobrushin matrix whenever `beta < log(19/17)/4`. -/
noncomputable def periodicHypercubicSpecialUnitaryDobrushinMatrixData
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4) :
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg) where
  influence :=
    specialUnitaryCompactOrientedSharedPlaquetteInfluence
      (periodicHypercubicFiniteOrientedGeometry n)
      N hN beta beta_nonneg
  influence_nonneg := by
    intro target source
    exact specialUnitaryCompactOrientedSharedPlaquetteInfluence_nonneg
      (periodicHypercubicFiniteOrientedGeometry n)
      N hN beta beta_nonneg target source
  influence_diagonal_zero := by
    intro target
    exact specialUnitaryCompactOrientedSharedPlaquetteInfluence_diagonal_zero
      (periodicHypercubicFiniteOrientedGeometry n)
      N hN beta beta_nonneg target
  conditionalIntegral_difference_abs_le := by
    intro target source A B hAgree phi hphi hphiBound
    simpa [periodicHypercubicSpecialUnitaryWilsonSystem] using
      specialUnitaryContinuousCompactOriented_conditionalIntegral_difference_abs_le
        (periodicHypercubicFiniteOrientedGeometry n)
        N hN beta beta_nonneg A B target source hAgree phi hphi hphiBound
  coefficient := 18 * periodicHypercubicSpecialUnitaryDobrushinEta beta
  coefficient_nonneg := by
    apply mul_nonneg
    · norm_num
    · unfold periodicHypercubicSpecialUnitaryDobrushinEta
      apply compactHaarOscillationInfluence_nonneg
      positivity
  rowSum_le_coefficient := by
    intro target
    exact periodicHypercubicSpecialUnitary_influence_rowSum_le
      n N hn hN beta beta_nonneg target
  coefficient_lt_one :=
    periodicHypercubicSpecialUnitary_eighteen_mul_eta_lt_one_of_beta_lt
      beta hBetaLt

end

end MathlibAnalytic
end MGAP4D
