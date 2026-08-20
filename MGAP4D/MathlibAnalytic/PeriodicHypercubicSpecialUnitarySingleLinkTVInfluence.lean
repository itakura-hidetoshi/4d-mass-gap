import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkSharpTV
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonPlaquetteSupport
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import MGAP4D.MathlibAnalytic.PeriodicHypercubicActiveNeighborBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSharedPlaquetteUniqueness
import Mathlib.Tactic

/-!
# Periodic SU(N) one-link TV influence

This file specializes the current continuous compact-Haar one-link total-variation
bound to the actual four-dimensional periodic `SU(N)` Wilson system.

The only quantitative inputs are already-canonical finite geometry and the standard
Wilson plaquette-energy range:

* every active target/source pair shares at most one plaquette when the side length
  is at least three;
* every target has at most eighteen active physical-link neighbors;
* `SU(N)` Wilson plaquette energy is at most two.

Consequently every active single-link influence is bounded by

`(exp (4 * beta) - 1) / (exp (4 * beta) + 1)`.

We also record the row sum of the corresponding sparse active majorant and its
volume-independent `18 * q(beta)` bound.  This is still a finite-volume static Gibbs
statement.  No Dobrushin contraction hypothesis is asserted for the factorial
continuum sequence, and no heat-bath time is identified with physical OS time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Membership in the four-link physical boundary is exactly the concrete
periodic touching predicate. -/
theorem periodicHypercubic_mem_plaquetteEdges_iff_for_compactSU
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

/-- Concrete active-neighbor membership, stated without importing any finite-gauge
Dobrushin stack. -/
theorem periodicHypercubic_mem_activeNeighbors_iff_for_compactSU
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
      (periodicHypercubic_mem_plaquetteEdges_iff_for_compactSU n p source).mp hErase.2⟩,
      hErase.1⟩
  · rintro ⟨⟨p, hpTarget, hpSource⟩, hNe⟩
    unfold periodicHypercubicActiveNeighbors
    apply Finset.mem_biUnion.mpr
    refine ⟨p,
      (periodicHypercubic_mem_touchingPlaquettes_iff n target p).mpr hpTarget,
      ?_⟩
    apply Finset.mem_erase.mpr
    exact ⟨hNe,
      (periodicHypercubic_mem_plaquetteEdges_iff_for_compactSU n p source).mpr hpSource⟩

/-- Generic compact-oriented touching is definitionally the actual signed periodic
physical-link touching relation for the canonical `SU(N)` system. -/
@[simp] theorem periodicHypercubicSpecialUnitary_touches_iff_current
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (p : PeriodicHypercubicPlaquette n)
    (e : PeriodicHypercubicEdge n) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.PlaquetteTouchesEdge p e ↔
      periodicHypercubicPlaquetteTouchesEdge n p e := by
  rfl

/-- The generic shared-plaquette finset of the compact `SU(N)` system is exactly
the concrete periodic shared-plaquette finset. -/
theorem periodicHypercubicSpecialUnitary_sharedPlaquettes_eq_current
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEdge n) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.sharedPlaquettes target source =
      periodicHypercubicSharedPlaquettes n target source := by
  classical
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hGeneric :=
      (compact_oriented_mem_sharedPlaquettes_iff
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta hBeta).base target source p).mp hp
    apply (periodicHypercubic_mem_sharedPlaquettes_iff
      n target source p).mpr
    simpa only [periodicHypercubicSpecialUnitary_touches_iff_current] using hGeneric
  · intro hp
    have hConcrete :=
      (periodicHypercubic_mem_sharedPlaquettes_iff
        n target source p).mp hp
    apply (compact_oriented_mem_sharedPlaquettes_iff
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta hBeta).base target source p).mpr
    simpa only [periodicHypercubicSpecialUnitary_touches_iff_current] using hConcrete

/-- Standard periodic `SU(N)` plaquette energy is bounded by two. -/
theorem periodicHypercubicSpecialUnitary_plaquetteEnergy_le_two_current
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (U : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.plaquetteEnergy U ≤ 2 := by
  change specialUnitaryWilsonPlaquetteEnergy N U ≤ 2
  exact specialUnitaryWilsonPlaquetteEnergy_le_two hN U

/-- Exact active-neighbor conditional-TV bound for the actual periodic compact
`SU(N)` Wilson source. -/
theorem periodicHypercubicSpecialUnitary_activeSingleLinkConditionalTotalVariation_le
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (A B : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.Configuration)
    (target source : PeriodicHypercubicEdge n)
    (hActive : source ∈ periodicHypercubicActiveNeighbors n target)
    (hAgree : (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).base.AgreeOffLink A B source) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta hBeta).singleLinkConditionalTotalVariation A B target ≤
      (Real.exp (beta * 4) - 1) / (Real.exp (beta * 4) + 1) := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    n N hN beta hBeta
  have hNe : source ≠ target :=
    (periodicHypercubic_mem_activeNeighbors_iff_for_compactSU
      n target source).mp hActive |>.2
  have hCardNat :
      (C.base.sharedPlaquettes target source).card ≤ 1 := by
    rw [periodicHypercubicSpecialUnitary_sharedPlaquettes_eq_current
      n N hN beta hBeta target source]
    exact periodicHypercubicSharedPlaquettes_card_le_one
      n hn target source hNe
  have hCard :
      ((C.base.sharedPlaquettes target source).card : ℝ) ≤ 1 := by
    exact_mod_cast hCardNat
  have hR : 0 ≤ beta * 4 := mul_nonneg hBeta (by norm_num)
  apply
    continuous_compact_oriented_singleLinkConditionalTotalVariation_le_of_oscillation
      C A B target (beta * 4) hR
  intro u v
  have hRaw :=
    compact_oriented_gibbsExponent_sourceResponse_oscillation_abs_le_shared
      C.base 2 (by norm_num)
      (periodicHypercubicSpecialUnitary_plaquetteEnergy_le_two_current
        n N hN beta hBeta)
      A B target source u v hAgree
  have hScale :
      C.base.beta *
          (2 * ((C.base.sharedPlaquettes target source).card : ℝ) * 2) ≤
        beta * 4 := by
    change beta *
        (2 * ((C.base.sharedPlaquettes target source).card : ℝ) * 2) ≤
      beta * 4
    nlinarith
  exact le_trans (abs_le.mp hRaw).2 hScale

/-- Volume-independent active one-link TV majorant. -/
def periodicHypercubicSpecialUnitaryActiveTVMajorant
    (beta : ℝ) : ℝ :=
  (Real.exp (beta * 4) - 1) / (Real.exp (beta * 4) + 1)

/-- Sparse active-neighbor majorant on physical periodic links. -/
noncomputable def periodicHypercubicSpecialUnitarySparseActiveTVInfluence
    (n : ℕ) [NeZero n]
    (beta : ℝ)
    (target source : PeriodicHypercubicEdge n) : ℝ := by
  classical
  exact if source ∈ periodicHypercubicActiveNeighbors n target then
    periodicHypercubicSpecialUnitaryActiveTVMajorant beta
  else 0

/-- The active TV majorant is nonnegative for nonnegative coupling. -/
theorem periodicHypercubicSpecialUnitaryActiveTVMajorant_nonneg
    (beta : ℝ) (hBeta : 0 ≤ beta) :
    0 ≤ periodicHypercubicSpecialUnitaryActiveTVMajorant beta := by
  unfold periodicHypercubicSpecialUnitaryActiveTVMajorant
  have hR : 0 ≤ beta * 4 := mul_nonneg hBeta (by norm_num)
  exact div_nonneg
    (sub_nonneg.mpr (Real.one_le_exp hR))
    (by positivity)

/-- Exact row sum of the sparse active-neighbor majorant. -/
theorem periodicHypercubicSpecialUnitarySparseActiveTVInfluence_rowSum_eq
    (n : ℕ) [NeZero n]
    (beta : ℝ)
    (target : PeriodicHypercubicEdge n) :
    (∑ source : PeriodicHypercubicEdge n,
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        n beta target source) =
      (periodicHypercubicActiveNeighbors n target).card *
        periodicHypercubicSpecialUnitaryActiveTVMajorant beta := by
  classical
  let s := periodicHypercubicActiveNeighbors n target
  let q := periodicHypercubicSpecialUnitaryActiveTVMajorant beta
  change (∑ source : PeriodicHypercubicEdge n,
      if source ∈ s then q else 0) = (s.card : ℝ) * q
  rw [← Finset.sum_filter]
  have hFilter :
      (Finset.univ.filter fun source : PeriodicHypercubicEdge n => source ∈ s) = s := by
    ext source
    simp
  rw [hFilter]
  simp [nsmul_eq_mul]

/-- Four-dimensional incidence gives the volume-independent row majorant
`18 * q(beta)`. -/
theorem periodicHypercubicSpecialUnitarySparseActiveTVInfluence_rowSum_le_eighteen
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (target : PeriodicHypercubicEdge n) :
    (∑ source : PeriodicHypercubicEdge n,
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        n beta target source) ≤
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta := by
  rw [periodicHypercubicSpecialUnitarySparseActiveTVInfluence_rowSum_eq]
  have hCardNat := periodicHypercubicActiveNeighbors_card_le_eighteen n target
  have hCard :
      ((periodicHypercubicActiveNeighbors n target).card : ℝ) ≤ 18 := by
    exact_mod_cast hCardNat
  exact mul_le_mul_of_nonneg_right hCard
    (periodicHypercubicSpecialUnitaryActiveTVMajorant_nonneg beta hBeta)

/-- If the explicit high-temperature threshold is supplied, every sparse active
majorant row is strictly below one.  This theorem records only the finite-volume
criterion; it does not assert that the factorial continuum couplings satisfy it. -/
theorem periodicHypercubicSpecialUnitarySparseActiveTVInfluence_rowSum_lt_one_of_threshold
    (n : ℕ) [NeZero n]
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (target : PeriodicHypercubicEdge n) :
    (∑ source : PeriodicHypercubicEdge n,
      periodicHypercubicSpecialUnitarySparseActiveTVInfluence
        n beta target source) < 1 :=
  lt_of_le_of_lt
    (periodicHypercubicSpecialUnitarySparseActiveTVInfluence_rowSum_le_eighteen
      n beta hBeta target)
    hThreshold

end

end MathlibAnalytic
end MGAP4D
