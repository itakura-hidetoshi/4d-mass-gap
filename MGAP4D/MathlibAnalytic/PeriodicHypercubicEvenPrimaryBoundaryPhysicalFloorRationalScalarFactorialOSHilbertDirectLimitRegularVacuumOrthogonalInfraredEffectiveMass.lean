import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonalLogCorrelation
import MGAP4D.MathlibAnalytic.ConvexSecantDecayRate
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
# Unregularized effective mass and infrared lower edge on the same-root excitation carrier

For every nonzero exact same-root excitation, the preceding file gives a strictly positive,
continuous, antitone autocorrelation with convex logarithm.  We therefore define the ordinary
unregularized secant effective mass and construct its long-time zero-based infrared limit as a
conditional infimum.

Finally we define a state-independent same-root OS infrared lower edge as the infimum of these
statewise infrared masses over all nonzero vectors of the exact vacuum-orthogonal Hilbert carrier.
This is a canonical quantity of the new carrier; no old `physicalYangMillsMass` is imported or
identified with it.
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

/-- Unregularized finite-difference effective mass of a same-root excitation. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)
    (s t : ℝ) : ℝ :=
  MGAP4D.secantDecayRate
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x) s t

/-- Convexity makes adjacent same-root effective-mass secants antitone. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_anti_adjacent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0)
    {a b c : ℝ}
    (ha : a ∈ Ici (0 : ℝ)) (hc : c ∈ Ici (0 : ℝ))
    (hab : a < b) (hbc : b < c) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass x b c ≤
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass x a b := by
  exact MGAP4D.ConvexOn.secantDecayRate_anti_adjacent
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog_convexOn_Ici hx)
    ha hc hab hbc

/-- Every ordered unregularized same-root effective-mass secant is nonnegative. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0)
    {s t : ℝ} (hst : s ≤ t) :
    0 ≤ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass x s t := by
  have hlog :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog_antitone hx hst
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
  unfold MGAP4D.secantDecayRate
  exact div_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr hst)

/-- With left endpoint zero, the same-root effective mass is antitone in positive right time. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_zero_antitone
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0)
    {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass x 0 t ≤
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass x 0 s := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hsec :=
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog_convexOn_Ici hx).secant_mono
      (show (0 : ℝ) ∈ Ici 0 by simp)
      (show s ∈ Ici (0 : ℝ) by exact hs.le)
      (show t ∈ Ici (0 : ℝ) by exact ht.le)
      hs.ne' ht.ne' hst
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
  unfold MGAP4D.secantDecayRate
  calc
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x 0 -
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x t) /
        (t - 0) =
      -((P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x t -
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x 0) /
        (t - 0)) := by ring
    _ ≤ -((P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x s -
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x 0) /
        (s - 0)) := neg_le_neg hsec
    _ = (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x 0 -
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x s) /
        (s - 0) := by ring

/-- Statewise same-root infrared effective mass: the infimum of the positive zero-based tail. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) : ℝ :=
  ⨅ u : NNReal,
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
      x 0 (((u + 1 : NNReal) : ℝ))

/-- The shifted positive-time tail is antitone. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_shift_antitone
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    Antitone (fun u : NNReal =>
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
        x 0 (((u + 1 : NNReal) : ℝ))) := by
  intro u v huv
  apply P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_zero_antitone hx
  · have hu : (0 : NNReal) < u + 1 := by positivity
    exact_mod_cast hu
  · have huv' : u + 1 ≤ v + 1 := by
      simpa only [add_comm] using (add_le_add_right huv 1)
    exact_mod_cast huv'

/-- The shifted same-root effective-mass tail is bounded below by zero. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_shift_bddBelow
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    BddBelow (Set.range (fun u : NNReal =>
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
        x 0 (((u + 1 : NNReal) : ℝ)))) := by
  refine ⟨0, ?_⟩
  rintro y ⟨u, rfl⟩
  apply P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_nonneg hx
  positivity

/-- The statewise same-root infrared effective mass is the actual long-time limit. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_shift_tendsto_infrared
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    Tendsto
      (fun u : NNReal =>
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
          x 0 (((u + 1 : NNReal) : ℝ)))
      atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass x)) := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass
  exact tendsto_atTop_ciInf
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_shift_antitone hx)
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_shift_bddBelow hx)

/-- Every nonzero statewise same-root infrared effective mass is nonnegative. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    0 ≤ P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass x := by
  have hlim :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_shift_tendsto_infrared hx
  apply ge_of_tendsto hlim
  filter_upwards with u
  apply P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_nonneg hx
  positivity

/-- The infrared limit lies below every positive zero-based finite-time effective mass. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass_le_effectiveMass_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass x ≤
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass x 0 (t : ℝ) := by
  have hlim :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_shift_tendsto_infrared hx
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop t] with u hu
  apply P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_zero_antitone hx
  · exact_mod_cast ht
  · have hut : t ≤ u + 1 := le_trans hu (le_add_right (le_refl u))
    exact_mod_cast hut

/-- Set of all statewise infrared masses of nonzero exact same-root excitations. -/
def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassSet
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    Set ℝ :=
  {m | ∃ x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert,
    x ≠ 0 ∧
    m = P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass x}

/-- Canonical state-independent same-root OS infrared lower edge. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) : ℝ :=
  sInf P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassSet

/-- The statewise infrared-mass set is bounded below by zero. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassSet_bddBelow
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    BddBelow P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassSet := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass_nonneg hx

/-- The state-independent same-root infrared lower edge lies below every nonzero statewise rate. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass_le_state
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass ≤
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass x := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass
  exact csInf_le
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassSet_bddBelow
    ⟨x, hx, rfl⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
