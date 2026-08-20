import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularClosedGeneratorIdentification
import Mathlib.Tactic

/-!
# Same-root infrared effective mass and exact closed-Hamiltonian Rayleigh lower edge

This file closes the infinitesimal bridge on the exact factorial-Wilson / primary-scalar Prokhorov
OS excitation carrier.

For a vector in the exact vacuum-orthogonal graph-closed Hamiltonian domain, the defining right
semigroup derivative gives

`(Cₓ(0) - Cₓ(t))/t -> ⟪x, H̄x⟫`.

Strict positivity of the same-root correlation then lets the elementary logarithmic tangent
sandwich identify the initial unregularized effective-mass limit with the Rayleigh quotient.
Convexity makes every positive-time effective mass, hence the statewise infrared mass, no larger
than that quotient.

Taking the infimum over all nonzero exact excitations produces a canonical state-independent
same-root OS infrared lower edge `m_OS`.  Without assuming `m_OS > 0`, we prove the exact uniform
quadratic lower bound

`m_OS * ‖x‖² ≤ ⟪x, H̄x⟫`

on the already-defined vacuum-orthogonal closed domain.  Thus the remaining positive mass-gap
frontier is sharpened to the model-derived statement `0 < m_OS`; no positive constant is inserted
as an assumption and no old `PhysicalHilbert` mass is transported.
-/

namespace MGAP4D

open Filter Set Topology

/-- Elementary logarithmic tangent sandwich used by the same-root initial-slope argument. -/
theorem sameRoot_log_sub_log_sandwich_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x - y) / x ≤ Real.log x - Real.log y ∧
      Real.log x - Real.log y ≤ (x - y) / y := by
  have hxy : Real.log (x / y) ≤ x / y - 1 := by
    by_cases hratio : x / y = 1
    · rw [hratio, Real.log_one]
      norm_num
    · exact (Real.log_lt_sub_one_of_pos (div_pos hx hy) hratio).le
  have hyx : Real.log (y / x) ≤ y / x - 1 := by
    by_cases hratio : y / x = 1
    · rw [hratio, Real.log_one]
      norm_num
    · exact (Real.log_lt_sub_one_of_pos (div_pos hy hx) hratio).le
  have hlogxy : Real.log (x / y) = Real.log x - Real.log y :=
    Real.log_div hx.ne' hy.ne'
  have hlogyx : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div hy.ne' hx.ne'
  have hdivxy : x / y - 1 = (x - y) / y := by
    rw [sub_div, div_self hy.ne']
  have hdivyx : y / x - 1 = (y - x) / x := by
    rw [sub_div, div_self hx.ne']
  rw [hlogxy, hdivxy] at hxy
  rw [hlogyx, hdivyx] at hyx
  constructor
  · have hneg := neg_le_neg hyx
    calc
      (x - y) / x = -((y - x) / x) := by ring
      _ ≤ -(Real.log y - Real.log x) := hneg
      _ = Real.log x - Real.log y := by ring
  · exact hxy

namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace LinearPMap

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- The raw same-root autocorrelation loss has initial slope equal to the exact graph-closed
Hamiltonian quadratic form on the vacuum-orthogonal domain. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_rightSlope_tendsto_closedHamiltonian_inner
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
              (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) 0 -
            P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
              (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) t))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (inner ℝ
          (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
            P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
            P.fixedSlotHilbertDirectLimitRegularSubspace)
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
            (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x)))) := by
  let phi : P.fixedSlotHilbertDirectLimitRegularSubspace :=
    (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
      P.fixedSlotHilbertDirectLimitRegularSubspace)
  let z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x
  have hgenerator := P.fixedSlotHilbertDirectLimitRegularClosedDomain_hasRightGeneratorValue z
  unfold FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue at hgenerator
  have hneg := hgenerator.neg
  have hham :
      Tendsto
        (fun t : NNReal =>
          -P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient phi t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z)) := by
    simpa [phi, z] using hneg
  have hconst : Tendsto (fun _ : NNReal => phi)
      (nhdsWithin 0 (Ioi 0)) (nhds phi) := tendsto_const_nhds
  have hinner :
      Tendsto
        (fun t : NNReal =>
          inner ℝ phi
            (-P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient phi t))
        (nhdsWithin 0 (Ioi 0))
        (nhds (inner ℝ phi
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z))) :=
    Filter.Tendsto.inner (𝕜 := ℝ) hconst hham
  have hpoint : ∀ t : NNReal,
      (t : ℝ)⁻¹ *
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
              (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) 0 -
            P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
              (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) t) =
        inner ℝ phi
          (-P.fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient phi t) := by
    intro t
    rw [P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_zero]
    unfold fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
    unfold fixedSlotHilbertDirectLimitRegularRightDifferenceQuotient
    change
      (t : ℝ)⁻¹ *
          (‖phi‖ ^ 2 -
            inner ℝ phi
              (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t phi)) =
        inner ℝ phi
          (-((t : ℝ)⁻¹ •
            (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t phi - phi)))
    calc
      (t : ℝ)⁻¹ *
          (‖phi‖ ^ 2 -
            inner ℝ phi
              (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t phi)) =
        -((t : ℝ)⁻¹ *
          (inner ℝ phi
              (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t phi) -
            inner ℝ phi phi)) := by
          rw [real_inner_self_eq_norm_sq]
          ring
      _ = -inner ℝ phi
          ((t : ℝ)⁻¹ •
            (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t phi - phi)) := by
          simpa only [real_inner_smul_right, inner_sub_right]
      _ = inner ℝ phi
          (-((t : ℝ)⁻¹ •
            (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t phi - phi))) := by
          rw [inner_neg_right]
  simpa only [hpoint, phi, z] using hinner

/-- Initial unregularized logarithmic decay converges to the exact closed-Hamiltonian Rayleigh
quotient numerator divided by the zero-time correlation. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationLog_rightSlope_tendsto_closedHamiltonian_overCorrelationZero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain)
    (hx : ((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) ≠ 0) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
              (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) 0 -
            P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
              (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) (t : ℝ)))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        ((inner ℝ
          (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
            P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
            P.fixedSlotHilbertDirectLimitRegularSubspace)
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
            (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x))) /
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation
            (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) 0)) := by
  let phi : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert :=
    (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)
  let c0 : ℝ :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi 0
  let energy : ℝ :=
    inner ℝ
      ((phi : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
        P.fixedSlotHilbertDirectLimitRegularSubspace)
      (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x))
  change Tendsto
    (fun t : NNReal =>
      (t : ℝ)⁻¹ *
        (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog phi 0 -
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog phi (t : ℝ)))
    (nhdsWithin 0 (Ioi 0)) (nhds (energy / c0))
  have hc0pos : 0 < c0 := by
    dsimp [c0, phi]
    exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_pos_of_ne_zero 0 hx
  have hraw :
      Tendsto
        (fun t : NNReal =>
          (t : ℝ)⁻¹ *
            (c0 - P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t))
        (nhdsWithin 0 (Ioi 0)) (nhds energy) := by
    simpa [c0, energy, phi] using
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_rightSlope_tendsto_closedHamiltonian_inner x
  have hcorr :
      Tendsto
        (fun t : NNReal =>
          P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t)
        (nhdsWithin 0 (Ioi 0)) (nhds c0) := by
    exact
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_continuous phi).continuousAt.mono_left
        inf_le_left
  have hlower :
      Tendsto
        (fun t : NNReal =>
          ((t : ℝ)⁻¹ *
            (c0 - P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t)) / c0)
        (nhdsWithin 0 (Ioi 0)) (nhds (energy / c0)) :=
    hraw.div tendsto_const_nhds hc0pos.ne'
  have hupper :
      Tendsto
        (fun t : NNReal =>
          ((t : ℝ)⁻¹ *
            (c0 - P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t)) /
              P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t)
        (nhdsWithin 0 (Ioi 0)) (nhds (energy / c0)) :=
    hraw.div hcorr hc0pos.ne'
  have hposTime :
      ∀ᶠ t : NNReal in nhdsWithin (0 : NNReal) (Ioi 0), 0 < t :=
    self_mem_nhdsWithin
  have hlower_le :
      ∀ᶠ t : NNReal in nhdsWithin (0 : NNReal) (Ioi 0),
        ((t : ℝ)⁻¹ *
          (c0 - P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t)) / c0 ≤
          (t : ℝ)⁻¹ *
            (Real.log c0 -
              Real.log (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t)) := by
    refine hposTime.mono (fun (t : NNReal) ht => ?_)
    have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
    have hctpos :
        0 < P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t :=
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_pos_of_ne_zero t hx
    have hsand := MGAP4D.sameRoot_log_sub_log_sandwich_of_pos hc0pos hctpos
    have hmul := mul_le_mul_of_nonneg_left hsand.1 (inv_nonneg.mpr htReal.le)
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  have hle_upper :
      ∀ᶠ t : NNReal in nhdsWithin (0 : NNReal) (Ioi 0),
        (t : ℝ)⁻¹ *
            (Real.log c0 -
              Real.log (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t)) ≤
          ((t : ℝ)⁻¹ *
            (c0 - P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t)) /
              P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t := by
    refine hposTime.mono (fun (t : NNReal) ht => ?_)
    have htReal : 0 < (t : ℝ) := by exact_mod_cast ht
    have hctpos :
        0 < P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t :=
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_pos_of_ne_zero t hx
    have hsand := MGAP4D.sameRoot_log_sub_log_sandwich_of_pos hc0pos hctpos
    have hmul := mul_le_mul_of_nonneg_left hsand.2 (inv_nonneg.mpr htReal.le)
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  have hlogRaw :
      Tendsto
        (fun t : NNReal =>
          (t : ℝ)⁻¹ *
            (Real.log c0 -
              Real.log (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation phi t)))
        (nhdsWithin 0 (Ioi 0)) (nhds (energy / c0)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlower hupper hlower_le hle_upper
  have hclampZero :
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp phi 0 = c0 := by
    simpa only [c0] using
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_coe phi (0 : NNReal)
  simpa only [fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog,
    hclampZero,
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClamp_coe] using hlogRaw

/-- Rayleigh-quotient form of the initial logarithmic decay theorem. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationLog_rightSlope_tendsto_closedHamiltonian_rayleigh
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain)
    (hx : ((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) ≠ 0) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
              (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) 0 -
            P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationRealClampLog
              (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) (t : ℝ)))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        ((inner ℝ
          (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
            P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
            P.fixedSlotHilbertDirectLimitRegularSubspace)
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
            (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x))) /
          ‖((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
            P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)‖ ^ 2)) := by
  simpa only [P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelation_zero] using
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationLog_rightSlope_tendsto_closedHamiltonian_overCorrelationZero
      x hx

/-- Zero-based same-root effective mass converges at the initial endpoint to the exact closed
Hamiltonian Rayleigh quotient. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_zero_tendsto_closedHamiltonian_rayleigh
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain)
    (hx : ((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) ≠ 0) :
    Tendsto
      (fun t : NNReal =>
        P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
          (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) 0 (t : ℝ))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        ((inner ℝ
          (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
            P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
            P.fixedSlotHilbertDirectLimitRegularSubspace)
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
            (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x))) /
          ‖((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
            P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)‖ ^ 2)) := by
  simpa [fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass,
    MGAP4D.secantDecayRate, div_eq_mul_inv, mul_comm] using
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalCorrelationLog_rightSlope_tendsto_closedHamiltonian_rayleigh
      x hx

/-- Every positive zero-based same-root effective mass lies below the exact closed-Hamiltonian
Rayleigh quotient. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_zero_le_closedHamiltonian_rayleigh
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain)
    (hx : ((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) ≠ 0)
    (t : NNReal) (ht : 0 < t) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass
        (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) 0 (t : ℝ) ≤
      (inner ℝ
        (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x))) /
        ‖((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)‖ ^ 2 := by
  have hlim :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_zero_tendsto_closedHamiltonian_rayleigh
      x hx
  have hpos :
      ∀ᶠ s : NNReal in nhdsWithin (0 : NNReal) (Ioi 0), 0 < s :=
    self_mem_nhdsWithin
  have hsmall :
      ∀ᶠ s : NNReal in nhdsWithin (0 : NNReal) (Ioi 0), s ≤ t := by
    have hid :
        Tendsto (fun s : NNReal => s)
          (nhdsWithin (0 : NNReal) (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    exact hid.eventually_le_const ht
  apply ge_of_tendsto hlim
  filter_upwards [hpos, hsmall] with s hs hst
  exact P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_zero_antitone
    hx (by exact_mod_cast hs) (by exact_mod_cast hst)

/-- The statewise infrared mass of every nonzero exact closed-domain excitation is bounded above by
its graph-closed Hamiltonian Rayleigh quotient. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass_le_closedHamiltonian_rayleigh
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain)
    (hx : ((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) ≠ 0) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass
        (x : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) ≤
      (inner ℝ
        (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x))) /
        ‖((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)‖ ^ 2 := by
  have hIR :=
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass_le_effectiveMass_zero
      hx (1 : NNReal) (by norm_num)
  exact hIR.trans
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalEffectiveMass_zero_le_closedHamiltonian_rayleigh
      x hx (1 : NNReal) (by norm_num))

/-- The canonical state-independent same-root OS infrared lower edge lies below every nonzero exact
closed-domain Hamiltonian Rayleigh quotient. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass_le_closedHamiltonian_rayleigh
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain)
    (hx : ((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) ≠ 0) :
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass ≤
      (inner ℝ
        (((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) :
          P.fixedSlotHilbertDirectLimitRegularSubspace)
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalAmbientDomainPoint x))) /
        ‖((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)‖ ^ 2 := by
  exact
    (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass_le_state hx).trans
      (P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalInfraredEffectiveMass_le_closedHamiltonian_rayleigh
        x hx)

/-- The canonical same-root state-independent infrared lower edge is already a uniform quadratic
lower bound for the exact graph-closed Hamiltonian on `Ω⊥`.  Positivity of this canonical number is
the remaining quantitative mass-gap statement. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass_coercive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass := by
  unfold FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt
  intro x
  by_cases hx :
      ((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
        P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert) = 0
  · have hx0 : x = 0 := by
      apply Subtype.ext
      exact hx
    subst x
    simp
  · have hrayleigh :=
      P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass_le_closedHamiltonian_rayleigh
        x hx
    have hnorm :
        0 < ‖((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
          P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)‖ ^ 2 := by
      have hnorm' :
          0 < ‖((x : P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalClosedDomain) :
            P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalHilbert)‖ :=
        norm_pos_iff.mpr hx
      positivity
    exact (le_div_iff₀ hnorm).mp hrayleigh

/-- Exact formulation of the remaining same-root positive mass-gap frontier. -/
def FixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassPositive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) : Prop :=
  0 < P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass

/-- Once the canonical same-root infrared lower edge is proved positive from the Wilson model, the
requested positive coercivity certificate follows with no carrier change and no inserted mass. -/
theorem fixedSlotHilbertDirectLimitRegularVacuumOrthogonal_positiveCoercivity_of_OSInfraredMassPositive
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (hpos : P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMassPositive) :
    ∃ m : ℝ, 0 < m ∧
      P.FixedSlotHilbertDirectLimitRegularVacuumOrthogonalCoerciveAt m := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass,
    hpos,
    P.fixedSlotHilbertDirectLimitRegularVacuumOrthogonalOSInfraredMass_coercive⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D