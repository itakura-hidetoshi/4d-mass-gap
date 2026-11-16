import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizablePeriodicWraparound
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRealizableOneStepExact3320Gap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCenteredCarrierVacuumOrthogonalDenseIsometry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2RawActualAnalysisPhysicalExcitation
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMN — periodic Wilson translation versus strict physical OS gap

The genuine finite periodic Wilson integer-time configuration translation is an
action of finite order L=2(H+1), and its Lth iterate has zero OS carrier norm
defect. Therefore it is not the Markov/Haar-averaging one-slab transfer kernel.

A STRICT exponential contraction postulated for precisely this finite-order
configuration-translation action would force every vacuum-centered carrier
to have zero OS norm, and by proved dense-range completion would collapse the
entire physical vacuum-orthogonal Hilbert sector.

This is a real mathematical no-go for an otherwise tempting wrong glue from
literal finite periodic integer-time translations to physical OS semigroup.
The no-go does NOT apply to the genuine one-slab positive Wilson integral
operator, which is not such a finite-order deterministic shift.

All statements are actual Lean implications within fixed Wilson/OS structure.
The final SU2 consequence uses separately named, explicit existing hypotheses
about a nonzero normalized-trace Wilson positive-half range witness. It does
not assert existence of this witness without those hypotheses.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set Topology Function
open scoped InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The exact proposed normalized 33/20 one-step factor is STRICTLY below one
at every physical lattice scale, because mass and lattice spacing are positive. -/
theorem p4Q2PZ37AMN_exact3320OneStepNormFactor_lt_one
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit) (n : ℕ) :
    physicalYangMillsExact3320OneStepNormFactor S n < 1 := by
  unfold physicalYangMillsExact3320OneStepNormFactor
  rw [Real.exp_lt_one_iff]
  have hpos : 0 < physicalYangMillsExact3320Mass * S.latticeSpacing n :=
    mul_pos physicalYangMillsExact3320Mass_pos (S.latticeSpacing_pos n)
  linarith

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}

/-- For a strict 33/20 one-step decay certificate assigned to the L-periodic
ACTUAL configuration-translation action, every centered carrier OS norm
must vanish. Its genuine periodicity is proved by the physical Haar-supported
interpolation, not assumed. This is a no-go, not a gap construction. -/
theorem p4Q2PZ37AMN_everyVacuumCenteredCarrier_norm_eq_zero
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ‖Pn.vacuumCenteredCarrier F‖ = 0 := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let L := PeriodicHypercubicEvenSideLength (halfExtent n)
  let q := physicalYangMillsExact3320OneStepNormFactor S n
  have hL : 0 < L := by
    dsimp [L, PeriodicHypercubicEvenSideLength]
    omega
  have hq0 : 0 ≤ q :=
    (physicalYangMillsExact3320OneStepNormFactor_pos S n).le
  have hq1 : q < 1 :=
    p4Q2PZ37AMN_exact3320OneStepNormFactor_lt_one S n
  have hqpow : q ^ L < 1 := pow_lt_one₀ hq0 hq1 (Nat.ne_of_gt hL)
  have hperiod :
      ‖R.realizableCarrierTranslation hInvariant n L
          (Pn.vacuumCenteredCarrier F)‖ =
        ‖Pn.vacuumCenteredCarrier F‖ := by
    simpa [L, Pn] using
      R.realizableCarrierTranslation_period_norm_eq
        hInvariant n (Pn.vacuumCenteredCarrier F)
  have hbound :
      ‖R.realizableCarrierTranslation hInvariant n L
          (Pn.vacuumCenteredCarrier F)‖ ≤
        q ^ L * ‖Pn.vacuumCenteredCarrier F‖ := by
    simpa [L, Pn, q] using G.centered_norm_le_pow n L F
  rw [hperiod] at hbound
  by_contra hne
  have hpos : 0 < ‖Pn.vacuumCenteredCarrier F‖ := by
    have hnonneg : 0 ≤ ‖Pn.vacuumCenteredCarrier F‖ := norm_nonneg _
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hcontr : 0 < (1 - q ^ L) * ‖Pn.vacuumCenteredCarrier F‖ :=
    mul_pos (sub_pos.mpr hqpow) hpos
  nlinarith

/-- By the already-certified dense isometric core of the physical
vacuum-orthogonal Hilbert space, collapse of all centered real Wilson OS
carrier norms forces that completed excitation sector to be the zero space.

This keeps the distinction between finite periodic configuration translation
and positive kernel transfer: only the former is subject to this no-go. -/
theorem p4Q2PZ37AMN_everyVacuumOrthogonalPhysicalState_eq_zero
    (G : PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (psi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert) :
    psi = 0 := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hPn : Pn.IsNormalized :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData_isNormalized
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  have hFzero (F : Pn.CenteredCarrier) :
      Pn.centeredPhysicalStateLinearMap hPn F = 0 := by
    have hmean : Pn.omega (F : Pn.Carrier).toGaugeInvariant = 0 :=
      F.property
    have hcenter : Pn.vacuumCenteredCarrier (F : Pn.Carrier) =
        (F : Pn.Carrier) := by
      unfold PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.vacuumCenteredCarrier
      rw [hmean]
      simp
    have hnorm :
        ‖(F : Pn.Carrier)‖ = 0 := by
      rw [← hcenter]
      exact G.p4Q2PZ37AMN_everyVacuumCenteredCarrier_norm_eq_zero n (F : Pn.Carrier)
    have hstateNorm : ‖Pn.centeredPhysicalStateLinearMap hPn F‖ = 0 := by
      rw [Pn.norm_centeredPhysicalStateLinearMap]
      exact hnorm
    exact norm_eq_zero.mp hstateNorm
  have hRange :
      Set.range (Pn.centeredPhysicalStateLinearMap hPn) ⊆
        ({0} : Set Pn.VacuumOrthogonalHilbert) := by
    rintro psi' ⟨F, rfl⟩
    exact Set.mem_singleton_iff.mpr (hFzero F)
  have hDense : DenseRange (Pn.centeredPhysicalStateLinearMap hPn) :=
    Pn.centeredPhysicalStateLinearMap_denseRange hPn
  have hmem : psi ∈ closure (Set.range (Pn.centeredPhysicalStateLinearMap hPn)) :=
    hDense psi
  have hclosed : IsClosed ({0} : Set Pn.VacuumOrthogonalHilbert) :=
    isClosed_singleton
  have hzero : psi ∈ ({0} : Set Pn.VacuumOrthogonalHilbert) := by
    have h := closure_mono hRange hmem
    simpa [hclosed.closure_eq] using h
  exact Set.mem_singleton_iff.mp hzero

/-- Any certified nonzero vacuum-orthogonal OS physical excitation at a cutoff
precludes the claimed strict 33/20 exponential contraction of the finite-order
PERIODIC configuration-translation action at that same cutoff. -/
theorem p4Q2PZ37AMN_noExact3320Certificate_of_nonzeroPhysicalExcitation
    (n : ℕ)
    (psi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert)
    (hpsi : psi ≠ 0) :
    ¬ PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent N hN beta hbeta Q E R hInvariant := by
  intro G
  exact hpsi (G.p4Q2PZ37AMN_everyVacuumOrthogonalPhysicalState_eq_zero n psi)

end PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate

private theorem p4Q2PZ37AMN_rankPos : 0 < (2 : ℕ) := by norm_num

local instance p4Q2PZ37AMN_sideNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  change 2 * (H + 1) ≠ 0
  omega⟩
local instance p4Q2PZ37AMN_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AMN_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AMN_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AMN_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AMN_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AMN_su2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Concrete SU2 Wilson-analysis nonzero vacuum-orthogonal OS excitation
witness forces rejection of a strict gap assigned to the periodic deterministic
configuration-translation action, at the identical finite physical cutoff.

The witness premises are exactly those of the existing actual Wilson positive
half analysis theorem and are *not* claimed to be unconditional. -/
theorem p4Q2PZ37AMN_su2RawActualAnalysisWitness_excludes_realizableExact3320Gap
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 p4Q2PZ37AMN_rankPos beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent 2 p4Q2PZ37AMN_rankPos beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (U : PhysicalYangMillsEvenPeriodicWilsonOSPositiveHalfVacuumUnitCompatibility
      Q hInvariant)
    (n k : ℕ)
    (c : Fin (k + 1) → ℝ)
    (hH : 1 < halfExtent n)
    (hbetaPos : 0 < beta n)
    (hc : c ≠ 0)
    (hzero : inner ℝ
      (periodicHypercubicEvenBoundaryMarginalVacuumL2
        (halfExtent n) (beta n) (hbeta n))
      (periodicHypercubicEvenBoundaryMarginalNormalizedTracePolynomialL2
        (halfExtent n) (beta n) (hbeta n) k c) = 0)
    (hRawRange :
      periodicHypercubicEvenBoundaryNormalizedTracePolynomialRawActualAnalysisHaarL2
        (halfExtent n) (beta n) (hbeta n) k c ∈
        (Q.positiveHalfL2LinearMap hInvariant n).range) :
    ¬ PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate
      S D halfExtent 2 p4Q2PZ37AMN_rankPos beta hbeta Q E R hInvariant := by
  intro G
  obtain ⟨psi, hpsi⟩ :=
    Q.normalizedTracePolynomial_exists_nonzero_vacuumOrthogonalPhysicalState_of_rawActualAnalysis_range
      hInvariant U n k c hH hbetaPos hc hzero hRawRange
  exact hpsi (G.p4Q2PZ37AMN_everyVacuumOrthogonalPhysicalState_eq_zero n psi)

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AMN_exact3320OneStepNormFactor_lt_one
#print axioms MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate.p4Q2PZ37AMN_everyVacuumCenteredCarrier_norm_eq_zero
#print axioms MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate.p4Q2PZ37AMN_everyVacuumOrthogonalPhysicalState_eq_zero
#print axioms MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSRealizableOneStepExact3320GapCertificate.p4Q2PZ37AMN_noExact3320Certificate_of_nonzeroPhysicalExcitation
#print axioms MGAP4D.MathlibAnalytic.PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback.p4Q2PZ37AMN_su2RawActualAnalysisWitness_excludes_realizableExact3320Gap
