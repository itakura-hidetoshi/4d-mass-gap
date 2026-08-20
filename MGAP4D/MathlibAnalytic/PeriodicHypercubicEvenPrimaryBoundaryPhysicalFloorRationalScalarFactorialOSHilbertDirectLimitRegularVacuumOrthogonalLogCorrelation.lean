import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonalCorrelation
import MGAP4D.MathlibAnalytic.NNRealContinuousRealClampLogMidpointExtension
import MGAP4D.MathlibAnalytic.PositiveContinuousLogMidpointConvexRealHalfLine
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Strictly positive logarithmic correlation on the same-root excitation carrier

This file stays entirely on the factorial-Wilson / primary-scalar Prokhorov OS direct-limit
carrier.  Starting from the exact vacuum-orthogonal semigroup and correlation, it proves finite-time
injectivity directly from the same-root C₀, symmetry, and semigroup laws.  Hence every nonzero
excitation has strictly positive finite-time autocorrelation.

The correlation is then clamped canonically from `NNReal` to `ℝ`, its logarithm is defined without
an additive regularizer, and the already-generic Mathlib midpoint bridge upgrades the same-root
multiplicative midpoint inequality to `ConvexOn ℝ (Set.Ici 0)` for the logarithm.

No positive asymptotic rate, coercive constant, old `PhysicalHilbert` carrier, spectral theorem, or
numerical mass is used.
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

/-- Strong continuity at zero descends to the exact vacuum-orthogonal subtype. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_tendsto_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    Tendsto
      (fun t : NNReal =>
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x)
      (𝓝 0) (𝓝 x) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  have h :=
    P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_tendsto_zero
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace)
  rw [Metric.tendsto_nhds_nhds] at h
  obtain ⟨δ, hδ, hclose⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  exact hclose ht

/-- A nonzero same-root excitation remains nonzero at every finite nonnegative Euclidean time.

If `T_t x = 0`, symmetry gives `T_{t/2}x = 0`; iterating at dyadic times and using strong
continuity at zero forces `x = 0`. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_ne_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector t x ≠ 0 := by
  intro htx
  let tau : ℕ → NNReal := fun n => t * (1 / 2 : NNReal) ^ n
  have htauZero : ∀ n : ℕ,
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector (tau n) x = 0 := by
    intro n
    induction n with
    | zero =>
        simpa [tau] using htx
    | succ n ihn =>
        have hdouble : tau (n + 1) + tau (n + 1) = tau n := by
          dsimp [tau]
          rw [pow_succ]
          calc
            t * ((1 / 2 : NNReal) ^ n * (1 / 2)) +
                t * ((1 / 2 : NNReal) ^ n * (1 / 2)) =
              (t * (1 / 2 : NNReal) ^ n) *
                ((1 / 2 : NNReal) + (1 / 2 : NNReal)) := by ring
            _ = t * (1 / 2 : NNReal) ^ n := by norm_num
        have hsq :
            ‖P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                (tau (n + 1)) x‖ ^ 2 = 0 := by
          calc
            ‖P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                (tau (n + 1)) x‖ ^ 2 =
              inner ℝ
                (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                  (tau (n + 1)) x)
                (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                  (tau (n + 1)) x) :=
              (real_inner_self_eq_norm_sq _).symm
            _ = inner ℝ x
                (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                  (tau (n + 1))
                  (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                    (tau (n + 1)) x)) :=
              P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_inner_symmetric
                (tau (n + 1)) x
                (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                  (tau (n + 1)) x)
            _ = inner ℝ x
                (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                  (tau (n + 1) + tau (n + 1)) x) := by
              rw [P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_add]
            _ = inner ℝ x
                (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                  (tau n) x) := by rw [hdouble]
            _ = 0 := by simp [ihn]
        have hnorm :
            ‖P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
                (tau (n + 1)) x‖ = 0 := by
          nlinarith [norm_nonneg
            (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector
              (tau (n + 1)) x)]
        exact norm_eq_zero.mp hnorm
  have hratio : (1 / 2 : NNReal) < 1 := by norm_num
  have hpow :
      Tendsto (fun n : ℕ => (1 / 2 : NNReal) ^ n) atTop (nhds 0) :=
    NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio
  have htau : Tendsto tau atTop (nhds 0) := by
    dsimp [tau]
    simpa using (tendsto_const_nhds.mul hpow :
      Tendsto (fun n : ℕ => t * (1 / 2 : NNReal) ^ n)
        atTop (nhds (t * 0)))
  have hseq :
      Tendsto
        (fun n : ℕ =>
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector (tau n) x)
        atTop (nhds x) :=
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_tendsto_zero x).comp htau
  have hfun :
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector (tau n) x) =
      fun _ : ℕ =>
        (0 : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :=
    funext htauZero
  rw [hfun] at hseq
  exact hx (tendsto_nhds_unique hseq tendsto_const_nhds)

/-- Every nonzero same-root excitation autocorrelation is strictly positive at finite time. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_pos_of_ne_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    0 < P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x t := by
  have hhalf : t / 2 + t / 2 = t := by
    apply NNReal.eq
    norm_num
  rw [← hhalf,
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_add_self_eq_norm_sq]
  have hne :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalRealTimeVector_ne_zero
      (t / 2) hx
  exact pow_pos (norm_pos_iff.mpr hne) 2

/-- The same-root excitation autocorrelation is continuous in nonnegative Euclidean time. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_continuous
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    Continuous (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x) := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
  change Continuous (fun t : NNReal =>
    inner ℝ
      (((x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
        P.fixedSlotHilbertDirectLimitRegularSubspace) :
        P.fixedSlotHilbertDirectLimitCompletion)
      (P.fixedSlotHilbertDirectLimitRegularRealOrbit
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace) t))
  exact continuous_const.inner
    (P.fixedSlotHilbertDirectLimitRegularRealOrbit_uniformContinuous
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace)).continuous

/-- Canonical real clamp of the same-root excitation correlation. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)
    (t : ℝ) : ℝ :=
  MGAP4D.nnrealRealClampExtension
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x) t

@[simp]
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)
    (t : NNReal) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x (t : ℝ) =
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x t := by
  simp [fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp]

/-- The real-clamped same-root excitation correlation is continuous on `ℝ`. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_continuous
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    Continuous
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x) := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp
  exact MGAP4D.nnrealRealClampExtension_continuous
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x)
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_continuous x)

/-- The real-clamped correlation remains antitone. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_antitone
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
    Antitone
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x) := by
  intro s t hst
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp
  exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_antitone x
    (Real.toNNReal_mono hst)

/-- For a nonzero excitation, the real clamp is strictly positive on all of `ℝ`. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_pos_of_ne_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0)
    (t : ℝ) :
    0 < P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x t := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp
  exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_pos_of_ne_zero
    t.toNNReal hx

/-- Multiplicative midpoint control transfers to the nonnegative real half-line. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_midpoint_sq_le_mul
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x ((s + t) / 2) ^ 2 ≤
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x s *
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x t := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp
  exact MGAP4D.nnrealRealClampExtension_midpoint_sq_le_mul
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation x)
    (fun a b =>
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_midpoint_sq_le_mul a b x)
    hs ht

/-- Unregularized logarithm of the same-root excitation correlation. -/
noncomputable def fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)
    (t : ℝ) : ℝ :=
  Real.log
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x t)

/-- For nonzero excitations, the unregularized logarithm is continuous. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog_continuous
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    Continuous
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x) := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
  exact
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_continuous x).log
      (fun t =>
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_pos_of_ne_zero
          hx t).ne')

/-- The unregularized logarithm is convex on nonnegative real Euclidean time. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog_convexOn_Ici
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    ConvexOn ℝ (Ici (0 : ℝ))
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x) := by
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
  exact MGAP4D.convexOn_log_Ici_of_continuous_pos_midpoint_sq_le_mul
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp x)
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_continuous x)
    (fun t =>
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_pos_of_ne_zero hx t)
    (fun hs ht =>
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_midpoint_sq_le_mul
        x hs ht)

/-- The logarithm is antitone because the strictly positive correlation is antitone. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog_antitone
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    {x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert}
    (hx : x ≠ 0) :
    Antitone
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog x) := by
  intro s t hst
  unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
  exact Real.log_le_log
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_pos_of_ne_zero hx t)
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_antitone x hst)

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
