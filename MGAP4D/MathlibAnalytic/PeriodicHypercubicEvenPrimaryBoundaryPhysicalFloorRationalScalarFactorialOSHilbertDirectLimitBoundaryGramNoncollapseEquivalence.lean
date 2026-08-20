import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteCenteredBoundaryGramTailReduction
import Mathlib.Tactic

/-!
# Boundary Gram noncollapse and exact excitation nontriviality

The preceding same-root layers have moved the finite quantitative inputs all the way to actual
boundary Gram moments.  This file removes an apparent extra quantitative input from the
zero-separation side.

Under explicit primary temporal-reach divergence, every fixed boundary Gram-moment sequence is
eventually exactly the finite centered Wilson sequence from the dense-core transfer theorem.
Therefore it converges to the corresponding exact same-root Hilbert correlation; at zero
subsequent separation it converges to the squared norm of the smoothed-centered literal state.

Consequently an eventual strictly positive Gram floor for one fixed literal state is equivalent to
that exact smoothed-centered state being nonzero.  Since those literal positive-time-smoothed
centered excitations are dense in the exact vacuum-orthogonal Hilbert carrier, the global
boundary-Gram noncollapse predicate is equivalent to nontriviality of the exact same-root
excitation sector itself.

This sharpens the final reduction: after temporal-reach divergence, the only genuinely quantitative
finite input is the common boundary-Gram decay rate.  The other input is exactly carrier
nontriviality, not an independent uniform numerical floor estimate.

No nonzero excitation is constructed here, no positive decay rate is proved, and no heat-bath,
old-carrier, or numerical mass constant is imported.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Under explicit temporal-reach divergence, the actual finite boundary Gram moments converge to
the exact smoothed-centered same-root Hilbert correlation. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm_tendsto_correlation_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (h : ℚ) (hh : 0 ≤ h)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    Tendsto
      (fun n =>
        P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s h hh F n)
      atTop
      (nhds
        (inner ℝ
          (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (h + h) (add_nonneg hh hh)
            (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)))) := by
  have hlim :=
    P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_tendsto_correlation J s h hh F
  have heq :
      (fun n => P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s h hh F n) =ᶠ[atTop]
        (fun n =>
          P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s h hh F n) := by
    filter_upwards [
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
        hreach J s h hh F] with n hn
    calc
      P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s h hh F n =
          P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm J s h hh F n :=
        P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eq_wilsonSourceCentered
          J s h hh F n
      _ = P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s h hh F n := hn
  exact hlim.congr' heq

/-- Zero-separation boundary Gram moments converge exactly to the squared norm of the explicit
positive-time-smoothed centered literal state. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm_tendsto_norm_sq_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    Tendsto
      (fun n =>
        P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s 0 le_rfl F n)
      atTop
      (nhds (‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2)) := by
  have hlim :=
    P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_tendsto_norm_sq J s F
  have heq :
      (fun n => P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s 0 le_rfl F n) =ᶠ[atTop]
        (fun n =>
          P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s 0 le_rfl F n) := by
    filter_upwards [
      P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm_eventually_eq_boundaryGramMoment
        hreach J s 0 le_rfl F] with n hn
    calc
      P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s 0 le_rfl F n =
          P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourceReflectionForm J s 0 le_rfl F n :=
        P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_eq_wilsonSourceCentered
          J s 0 le_rfl F n
      _ = P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s 0 le_rfl F n := hn
  exact hlim.congr' heq

/-- A positive zero-separation boundary-Gram tail floor for one fixed smoothed literal carrier. -/
def FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloorFor
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) : Prop :=
  ∃ v : ℝ, 0 < v ∧
    ∀ᶠ n : ℕ in atTop,
      v ≤ P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s 0 le_rfl F n

/-- For one fixed literal carrier, a positive boundary-Gram floor is equivalent to nonvanishing of
its exact smoothed-centered Hilbert state. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloorFor_iff_state_ne_zero_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier) :
    P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloorFor J s F ↔
      P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F ≠ 0 := by
  constructor
  · rintro ⟨v, hv, hfloor⟩
    have hlim :=
      P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm_tendsto_norm_sq_of_temporalReach
        hreach J s F
    have hvsq :
        v ≤ ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2 := by
      apply ge_of_tendsto hlim
      exact hfloor
    intro hzero
    rw [hzero] at hvsq
    simp at hvsq
    linarith
  · intro hstate
    let r : ℝ := ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2
    have hnorm :
        0 < ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ :=
      norm_pos_iff.mpr hstate
    have hr : 0 < r := by
      dsimp [r]
      positivity
    let v : ℝ := r / 2
    have hv : 0 < v := by
      dsimp [v]
      positivity
    have hvlt : v < r := by
      dsimp [v]
      linarith
    have hlim :
        Tendsto
          (fun n =>
            P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s 0 le_rfl F n)
          atTop (nhds r) := by
      simpa [r] using
        P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm_tendsto_norm_sq_of_temporalReach
          hreach J s F
    have htail :
        ∀ᶠ n : ℕ in atTop,
          v < P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramMomentForm J s 0 le_rfl F n :=
      (tendsto_order.1 hlim).1 v hvlt
    refine ⟨v, hv, ?_⟩
    filter_upwards [htail] with n hn
    exact hn.le

/-- The global boundary-Gram noncollapse predicate is equivalent to existence of one nonzero
explicit positive-time-smoothed centered literal state. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor_iff_exists_nonzero_smoothedCenteredCarrierState_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop) :
    P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor ↔
      ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
        ∃ s : NNRat, ∃ hs : 0 < s,
          ∃ F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier,
            P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F ≠ 0 := by
  constructor
  · rintro ⟨v, hv, J, s, hs, F, hfloor⟩
    refine ⟨J, s, hs, F, ?_⟩
    exact
      (P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloorFor_iff_state_ne_zero_of_temporalReach
        hreach J s F).1 ⟨v, hv, hfloor⟩
  · rintro ⟨J, s, hs, F, hstate⟩
    rcases
      (P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloorFor_iff_state_ne_zero_of_temporalReach
        hreach J s F).2 hstate with ⟨v, hv, hfloor⟩
    exact ⟨v, hv, J, s, hs, F, hfloor⟩

/-- Under temporal-reach divergence, the finite boundary-Gram noncollapse condition is exactly
nontriviality of the canonical same-root vacuum-orthogonal Hilbert carrier. -/
theorem fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor_iff_excitation_nontrivial_of_temporalReach
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop) :
    P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor ↔
      ∃ x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert, x ≠ 0 := by
  constructor
  · intro hgram
    have hwilson : P.FixedSlotCarrierFiniteSmoothedCenteredWilsonSourcePositiveFloor :=
      (P.fixedSlotCarrierFiniteSmoothedCenteredWilsonSourcePositiveFloor_iff_boundaryGram_of_temporalReach
        hreach).2 hgram
    have hfinite : P.FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor :=
      P.fixedSlotCarrierFiniteSmoothedCenteredPositiveFloor_iff_wilsonSource.mpr hwilson
    exact
      P.fixedSlotHilbertDirectLimit_exists_nonzero_smoothedCenteredCarrierExcitation_of_finiteFloor
        hfinite
  · rintro ⟨x, hx⟩
    let S : Set P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
      P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet
    have hexplicit : ∃ y, y ∈ S ∧ y ≠ 0 := by
      by_contra hnone
      have hall : ∀ y, y ∈ S → y = 0 := by
        intro y hy
        by_contra hy0
        exact hnone ⟨y, hy, hy0⟩
      have hsubset : S ⊆ ({0} : Set P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) := by
        intro y hy
        simpa using hall y hy
      have hxclosure : x ∈ closure S := by
        dsimp [S]
        rw [P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet_closure_eq_univ]
        exact Set.mem_univ x
      have hxsingleton :
          x ∈ closure ({0} : Set P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :=
        (closure_mono hsubset) hxclosure
      have hclosed : IsClosed ({0} : Set P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :=
        isClosed_singleton
      rw [hclosed.closure_eq] at hxsingleton
      have hxzero : x = 0 := by simpa using hxsingleton
      exact hx hxzero
    rcases hexplicit with ⟨y, hyS, hy⟩
    dsimp [S] at hyS
    rcases hyS with ⟨s, hs, J, F, rfl⟩
    have hstate :
        P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F ≠ 0 := by
      intro hzero
      apply hy
      apply Subtype.ext
      apply Subtype.ext
      exact hzero
    exact
      (P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor_iff_exists_nonzero_smoothedCenteredCarrierState_of_temporalReach
        hreach).2 ⟨J, s, hs, F, hstate⟩

/-- Clean final reduction after the Gram identification: positive common boundary-Gram decay plus
nontriviality of the exact same-root excitation sector gives a strictly positive coercivity
certificate for the actual graph-closed same-root Hamiltonian. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_boundaryGramDecay_of_nontrivial
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hreach :
      Tendsto
        (periodicHypercubicEvenPrimarySpatialPhysicalTemporalReach
          H periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
        atTop atTop)
    {m : ℝ}
    (hm : 0 < m)
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramUniformDecayAt m)
    (hne : ∃ x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert, x ≠ 0) :
    ∃ μ : ℝ, 0 < μ ∧
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt μ := by
  have hfiniteDecay : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m :=
    (P.fixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt_iff_boundaryGram_of_temporalReach
      hreach m).2 hdec
  have hgramFloor : P.FixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor :=
    (P.fixedSlotCarrierFiniteSmoothedCenteredBoundaryGramPositiveFloor_iff_excitation_nontrivial_of_temporalReach
      hreach).2 hne
  have hfiniteFloor : P.FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor :=
    (P.fixedSlotCarrierFiniteSmoothedCenteredPositiveFloor_iff_boundaryGram_of_temporalReach
      hreach).2 hgramFloor
  exact
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_finite
      hm hfiniteDecay hfiniteFloor

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
