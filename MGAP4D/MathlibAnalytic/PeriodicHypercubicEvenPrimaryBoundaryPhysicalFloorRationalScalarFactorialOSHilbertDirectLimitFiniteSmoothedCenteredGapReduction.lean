import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitFiniteSmoothedCenteredReflectionTransfer
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonalInfraredRayleigh
import Mathlib.Tactic

/-!
# Finite centered Wilson decay as the exact same-root mass-gap input

The preceding same-root package aligns the actual finite Wilson centered quantity

`R_n(F;s,h) = Q_n(tau_(s+h) F) - E_n[tau_(s+h) F]^2`

with the dense exact excitation vector `T_s x_F^o` and proves both

`R_n(F;s,h) -> <T_s x_F^o, T_(2h) T_s x_F^o>`

and

`R_n(F;s,0) -> ||T_s x_F^o||^2`.

This file turns that alignment into the precise reduction needed for a positive same-root mass.
Two logically independent model inputs are kept separate:

1. a common finite centered decay rate `m`, shared by every literal smoothed cylinder;
2. a positive finite centered floor for at least one literal smoothed cylinder, ruling out collapse
   of the entire excitation carrier.

The common finite decay passes to the dense literal excitation core by the already-proved limits,
then to every exact `Omega^perp` vector by Hilbert-space density, and finally from rational to real
Euclidean time by continuity.  The resulting exponential correlation envelope implies that every
nonzero statewise infrared effective mass is at least `m`.

The positive finite floor supplies a nonzero exact excitation.  Therefore the state-independent
same-root OS infrared mass set is nonempty, so the common statewise lower bound descends to its
infimum.  If the model proves `0 < m`, the already-canonical Rayleigh theorem then yields positive
coercivity for the exact graph-closed Hamiltonian on `Omega^perp`.

No numerical value is selected here, and neither finite decay nor noncollapse is asserted from the
bare Wilson action in this file.  The point is to isolate those two remaining quantitative inputs on
the literal finite Wilson quantities already attached to the dense same-root excitation core.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
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

/-- A common finite Wilson centered decay rate on every positive-time-smoothed literal cylinder.
The time parameter `t` is the full correlation separation, so the finite reflection form is sampled
at half-separation `t/2`. -/
def FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ) : Prop :=
  ∀ (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (t : NNRat),
    ∀ᶠ n : ℕ in atTop,
      P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm
          J s ((t : ℚ) / 2) (div_nonneg t.2 (by norm_num)) F n ≤
        Real.exp (-m * (t : ℝ)) *
          P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s 0 le_rfl F n

/-- Finite noncollapse input: one literal positive-time-smoothed centered Wilson cylinder has an
eventual strictly positive lower floor at zero subsequent separation. -/
def FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) : Prop :=
  ∃ v : ℝ, 0 < v ∧
    ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
      ∃ s : NNRat, ∃ hs : 0 < s,
        ∃ F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier,
          ∀ᶠ n : ℕ in atTop,
            v ≤ P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s 0 le_rfl F n

/-- At rational time, the exact excitation correlation is the ambient completed-direct-limit
rational translation pairing. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_nnrat_eq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)
    (q : NNRat) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x
        (MGAP4D.nnratToNNReal q) =
      inner ℝ
        (((x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace) :
          P.fixedSlotHilbertDirectLimitCompletion)
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM q
          (((x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
            P.fixedSlotHilbertDirectLimitRegularSubspace) :
            P.fixedSlotHilbertDirectLimitCompletion)) := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
  change
    inner ℝ
        (((x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace) :
          P.fixedSlotHilbertDirectLimitCompletion)
        (((P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism
            (MGAP4D.nnratToNNReal q)
            ((x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
              P.fixedSlotHilbertDirectLimitRegularSubspace) :
          P.fixedSlotHilbertDirectLimitRegularSubspace) :
          P.fixedSlotHilbertDirectLimitCompletion) = _
  rw [P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_nnrat]

/-- The finite common decay estimate passes through the selected Wilson limits to each explicit
positive-time-smoothed literal excitation. -/
theorem fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitation_correlation_nnrat_le_exp
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {m : ℝ}
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (s : NNRat) (hs : 0 < s)
    (F : (P.fixedSlotDataOfIndex J).FixedSlotCarrier)
    (t : NNRat) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
        (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitation J s hs F)
        (MGAP4D.nnratToNNReal t) ≤
      Real.exp (-m * (t : ℝ)) *
        ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitation J s hs F‖ ^ 2 := by
  let h : ℚ := (t : ℚ) / 2
  have hh : 0 ≤ h := div_nonneg t.2 (by norm_num)
  have hdouble : h + h = (t : ℚ) := by
    dsimp [h]
    ring
  let c : ℝ := Real.exp (-m * (t : ℝ))
  have hleft :=
    P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_tendsto_correlation
      J s h hh F
  have hzero :=
    P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_tendsto_norm_sq
      J s F
  have hright :
      Tendsto
        (fun n => c *
          P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm J s 0 le_rfl F n)
        atTop
        (nhds
          (c * ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2)) :=
    tendsto_const_nhds.mul hzero
  have hdiff := hleft.sub hright
  have hevent := hdec J s hs F t
  have hlimle :
      inner ℝ
          (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)
          (P.fixedSlotHilbertDirectLimitTimeTranslateCLM
            (h + h) (add_nonneg hh hh)
            (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)) -
        c * ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2 ≤ 0 := by
    apply le_of_tendsto hdiff
    filter_upwards [hevent] with n hn
    exact sub_nonpos.mpr hn
  have hambient :
      inner ℝ
          (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)
          (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
            (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)) ≤
        c * ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2 := by
    have hraw := sub_nonpos.mp hlimle
    simpa [fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM, hdouble, c] using hraw
  rw [P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_nnrat_eq]
  change
    inner ℝ
        (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)
        (P.fixedSlotHilbertDirectLimitNNRatTimeTranslateCLM t
          (P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F)) ≤
      Real.exp (-m * (t : ℝ)) *
        ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2
  simpa [c] using hambient

/-- Density upgrades the common rational-time decay estimate from explicit literal excitations to
every exact same-root vacuum-orthogonal vector. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_nnrat_le_exp
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {m : ℝ}
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m)
    (t : NNRat)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x
        (MGAP4D.nnratToNNReal t) ≤
      Real.exp (-m * (t : ℝ)) * ‖x‖ ^ 2 := by
  let tau : NNReal := MGAP4D.nnratToNNReal t
  let c : ℝ := Real.exp (-m * (t : ℝ))
  let S : Set P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
    {y | P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation y tau ≤
      c * ‖y‖ ^ 2}
  have hclosed : IsClosed S := by
    dsimp [S]
    unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
    change IsClosed
      {y : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert |
        inner ℝ
            (y : P.fixedSlotHilbertDirectLimitRegularSubspace)
            (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism tau
              (y : P.fixedSlotHilbertDirectLimitRegularSubspace)) ≤
          c * ‖y‖ ^ 2}
    exact isClosed_le
      (continuous_subtype_val.inner
        ((P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism tau).continuous.comp
          continuous_subtype_val))
      (continuous_const.mul (continuous_norm.pow 2))
  have hcore : P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet ⊆ S := by
    rintro y ⟨s, hs, J, F, rfl⟩
    dsimp [S, tau, c]
    exact
      P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitation_correlation_nnrat_le_exp
        hdec J s hs F t
  have hclosure :
      closure P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet ⊆ S :=
    closure_minimal hcore hclosed
  have hxcl :
      x ∈ closure P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet := by
    rw [P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitationSet_closure_eq_univ]
    trivial
  have hxS := hclosure hxcl
  simpa [S, tau, c] using hxS

/-- Continuity in Euclidean time upgrades rational-time decay to the full nonnegative real
half-line. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_le_exp
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {m : ℝ}
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m)
    (t : NNReal)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x t ≤
      Real.exp (-m * (t : ℝ)) * ‖x‖ ^ 2 := by
  let S : Set NNReal :=
    {u | P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x u ≤
      Real.exp (-m * (u : ℝ)) * ‖x‖ ^ 2}
  have hright : Continuous (fun u : NNReal =>
      Real.exp (-m * (u : ℝ)) * ‖x‖ ^ 2) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_subtype_val)).mul continuous_const
  have hclosed : IsClosed S := by
    exact isClosed_le
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_continuous x)
      hright
  have hrange : Set.range MGAP4D.nnratToNNReal ⊆ S := by
    intro u hu
    rcases hu with ⟨q, rfl⟩
    change
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x
          (MGAP4D.nnratToNNReal q) ≤
        Real.exp (-m * ((MGAP4D.nnratToNNReal q : NNReal) : ℝ)) * ‖x‖ ^ 2
    simpa using
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_nnrat_le_exp hdec q x
  have hclosure : closure (Set.range MGAP4D.nnratToNNReal) ⊆ S :=
    closure_minimal hrange hclosed
  apply hclosure
  rw [MGAP4D.nnratToNNReal_denseRange.closure_eq]
  trivial

/-- The full real-time exponential correlation envelope passes monotonically through the exact
same-root logarithm for every nonzero excitation. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog_le_decayEnvelope
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {m : ℝ}
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m)
    (t : NNReal)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x (t : ℝ) ≤
      Real.log (‖x‖ ^ 2 * Real.exp (-m * (t : ℝ))) := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
  rw [P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_coe]
  exact Real.log_le_log
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_pos_of_ne_zero t hx)
    (by
      simpa only [mul_comm] using
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_le_exp hdec t x)

/-- The logarithmic loss of the exponential envelope, divided by positive Euclidean time, is
exactly the candidate common mass `m`. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_log_decayEnvelope_div_time_eq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (m : ℝ)
    (t : NNReal)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) (ht : 0 < t) :
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x 0 -
        Real.log (‖x‖ ^ 2 * Real.exp (-m * (t : ℝ)))) /
        (t : ℝ) = m := by
  have hnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm_ne : ‖x‖ ≠ 0 := ne_of_gt hnorm_pos
  have hnormsq_ne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm_ne
  have ht_ne : (t : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ht)
  have hzero :
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x 0 =
        2 * Real.log ‖x‖ := by
    unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
    have hclamp :
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x 0 =
          ‖x‖ ^ 2 := by
      simpa using
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_coe x (0 : NNReal)
    rw [hclamp, Real.log_pow]
    norm_num
  have henvelope :
      Real.log (‖x‖ ^ 2 * Real.exp (-m * (t : ℝ))) =
        2 * Real.log ‖x‖ + (-m * (t : ℝ)) := by
    rw [Real.log_mul hnormsq_ne (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    norm_num
  rw [hzero, henvelope]
  field_simp [ht_ne]
  ring

/-- Every positive-time zero-based effective mass of every nonzero exact excitation is bounded below
by the common finite Wilson decay rate. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mass_le_effectiveMass_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {m : ℝ}
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m)
    (t : NNReal)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) (ht : 0 < t) :
    m ≤ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass x 0 (t : ℝ) := by
  have hmass :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_log_decayEnvelope_div_time_eq
      m t hx ht
  have hlog :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog_le_decayEnvelope
      hdec t hx
  have hnum :=
    sub_le_sub_left hlog
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x 0)
  have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
  rw [← hmass]
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
  unfold MGAP4D.secantDecayRate
  simp only [sub_zero, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr htReal.le)

/-- Hence every nonzero statewise same-root infrared effective mass is at least the common finite
Wilson decay rate. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mass_le_infraredEffectiveMass
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {m : ℝ}
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    m ≤ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass x := by
  have hlim :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_shift_tendsto_infrared hx
  apply ge_of_tendsto hlim
  filter_upwards with u
  exact
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mass_le_effectiveMass_zero
      hdec (u + 1) hx (by positivity)

/-- A positive finite centered floor survives the selected Wilson limit and gives a genuinely
nonzero explicit same-root excitation. -/
theorem fixedSlotHilbertDirectLimit_exists_nonzero_smoothedCenteredCarrierExcitation_of_finiteFloor
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hfloor : P.FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor) :
    ∃ x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert, x ≠ 0 := by
  rcases hfloor with ⟨v, hv, J, s, hs, F, hfinite⟩
  let x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
    P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierExcitation J s hs F
  have hlim :=
    P.fixedSlotCarrierFiniteSmoothedCenteredReflectionForm_tendsto_norm_sq J s F
  have hvsq :
      v ≤ ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2 := by
    apply ge_of_tendsto hlim
    exact hfinite
  have hxvsq : v ≤ ‖x‖ ^ 2 := by
    change v ≤ ‖P.fixedSlotHilbertDirectLimitSmoothedCenteredCarrierState J s F‖ ^ 2
    exact hvsq
  refine ⟨x, ?_⟩
  intro hxzero
  have hnormzero : ‖x‖ ^ 2 = 0 := by rw [hxzero]; simp
  nlinarith

/-- Consequently the statewise infrared-mass set is nonempty whenever the finite model supplies one
positive centered floor. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassSet_nonempty_of_finiteFloor
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hfloor : P.FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassSet.Nonempty := by
  rcases
    P.fixedSlotHilbertDirectLimit_exists_nonzero_smoothedCenteredCarrierExcitation_of_finiteFloor
      hfloor with ⟨x, hx⟩
  exact
    ⟨P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass x,
      ⟨x, hx, rfl⟩⟩

/-- Common finite decay plus one finite noncollapse floor place the same rate below the canonical
state-independent same-root OS infrared mass. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mass_le_OSInfraredMass_of_finite
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {m : ℝ}
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m)
    (hfloor : P.FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor) :
    m ≤ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass
  apply le_csInf
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassSet_nonempty_of_finiteFloor
      hfloor)
  intro r hr
  rcases hr with ⟨x, hx, rfl⟩
  exact
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mass_le_infraredEffectiveMass hdec hx

/-- If the common finite rate is strictly positive and the finite model is noncollapsed, the
canonical same-root OS infrared lower edge is strictly positive. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_OSInfraredMassPositive_of_finite
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {m : ℝ}
    (hm : 0 < m)
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m)
    (hfloor : P.FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor) :
    P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassPositive := by
  unfold FixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassPositive
  exact lt_of_lt_of_le hm
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_mass_le_OSInfraredMass_of_finite
      hdec hfloor)

/-- Final conditional reduction: the two literal finite Wilson quantitative inputs produce a
strictly positive coercivity certificate for the exact same-root graph-closed Hamiltonian. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_finite
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {m : ℝ}
    (hm : 0 < m)
    (hdec : P.FixedSlotCarrierFiniteSmoothedCenteredUniformDecayAt m)
    (hfloor : P.FixedSlotCarrierFiniteSmoothedCenteredPositiveFloor) :
    ∃ μ : ℝ, 0 < μ ∧
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt μ := by
  exact
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_OSInfraredMassPositive
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_OSInfraredMassPositive_of_finite
        hm hdec hfloor)

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
