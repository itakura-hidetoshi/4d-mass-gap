import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonCenteredApproximateSlowVectors
import MGAP4D.MathlibAnalytic.PhysicalYangMillsCommonCarrierVacuumOrthogonalEmbedding
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverageExcitationGraphRegularization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

/-- Operator-norm approximate maximizers may always be chosen with unit norm.

This is the normalized form of the generic slow-vector theorem.  It uses only
real normed-space linearity and does not assume finite dimensionality or norm
attainment. -/
theorem continuousLinearMap_exists_unit_apply_norm_gt_of_lt_opNorm
    {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_lt : r < ‖T‖) :
    ∃ x : E, ‖x‖ = 1 ∧ r < ‖T x‖ := by
  rcases continuousLinearMap_exists_nonzero_apply_norm_gt_mul_norm_of_lt_opNorm
      T hr_nonneg hr_lt with ⟨x, hx, hslow⟩
  have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : E := ‖x‖⁻¹ • x
  have hy_norm : ‖y‖ = 1 := by
    dsimp [y]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxnorm_pos)]
    simp [hxnorm_pos.ne']
  have hTy_norm : ‖T y‖ = ‖x‖⁻¹ * ‖T x‖ := by
    dsimp [y]
    rw [map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxnorm_pos)]
  have hr_div : r < ‖T x‖ / ‖x‖ :=
    (lt_div_iff₀ hxnorm_pos).2 hslow
  have hr_y : r < ‖T y‖ := by
    rw [hTy_norm]
    simpa [div_eq_mul_inv, mul_comm] using hr_div
  exact ⟨y, hy_norm, hr_y⟩

namespace PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
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

/-- The completed finite Wilson excitation operator admits unit slow vectors
beating every strict fraction of its exact intrinsic transfer norm.

No eigenvector, finite-dimensional spectral realization, logarithmic rate, or
continuum mass is used. -/
theorem exists_unit_physicalExcitationApproximateSlowVector
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (n : ℕ)
    (hfactor : 0 < A.centeredTransferFactor n)
    {theta : ℝ} (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ∃ psi : Pn.VacuumOrthogonalHilbert,
      ‖psi‖ = 1 ∧
      A.centeredTransferFactor n * theta <
        ‖A.physicalExcitationOneStepOperator n psi‖ := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
  let Tn : Pn.VacuumOrthogonalHilbert →L[ℝ] Pn.VacuumOrthogonalHilbert :=
    A.physicalExcitationOneStepOperator n
  let r : ℝ := A.centeredTransferFactor n * theta
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr_lt_factor : r < A.centeredTransferFactor n := by
    dsimp [r]
    nlinarith
  have hr_lt : r < ‖Tn‖ := by
    dsimp [Tn]
    rw [A.physicalExcitationOneStepOperator_opNorm_eq_centeredTransferFactor]
    exact hr_lt_factor
  rcases continuousLinearMap_exists_unit_apply_norm_gt_of_lt_opNorm
      Tn hr_nonneg hr_lt with ⟨psi, hpsi_norm, hslow⟩
  exact ⟨psi, hpsi_norm, hslow⟩

end PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A unit vector in any finite carrier, embedded isometrically into the
continuum excitation Hilbert space, remains uniformly nonvanishing after all
sufficiently small positive graph-domain time averages.

The quantitative lower bound `1/2` is purely a convenient open neighborhood of
unit norm; it is not the finite coercivity constant and carries no mass input. -/
theorem eventually_timeAverageClosedRightHamiltonianDomain_norm_gt_half_of_isometricExcitationEmbed
    (T : P.StronglyContinuousPhysicalSemigroup)
    {Efin : Type*} [NormedAddCommGroup Efin] [NormedSpace ℝ Efin]
    (embed : Efin →L[ℝ] P.VacuumOrthogonalHilbert)
    (hembed_norm : ∀ x, ‖embed x‖ = ‖x‖)
    {phi : Efin} (hphi_norm : ‖phi‖ = 1) :
    ∀ᶠ h : NNReal in nhdsWithin 0 (Ioi 0),
      (1 : ℝ) / 2 <
        ‖(T.timeAverageClosedRightHamiltonianDomain h
          ((embed phi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) :
            P.PhysicalHilbert)‖ := by
  let psi : P.PhysicalHilbert :=
    ((embed phi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
  have hpsi_norm : ‖psi‖ = 1 := by
    change ‖embed phi‖ = 1
    rw [hembed_norm, hphi_norm]
  have htend :
      Tendsto
        (fun h : NNReal =>
          ‖(T.timeAverageClosedRightHamiltonianDomain h psi :
            P.PhysicalHilbert)‖)
        (nhdsWithin 0 (Ioi 0)) (nhds (1 : ℝ)) := by
    have hnorm := (T.timeAverageClosedRightHamiltonianDomain_tendsto_zero psi).norm
    simpa only [hpsi_norm] using hnorm
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  exact htend.eventually (eventually_gt_nhds hhalf)

/-- The same small-time graph-domain regularizations remain in the continuum
vacuum-orthogonal sector whenever symmetry of the physical semigroup is
supplied by the actual OS route. -/
theorem timeAverageClosedRightHamiltonianDomain_isometricExcitationEmbed_orthogonal
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {Efin : Type*} [NormedAddCommGroup Efin] [NormedSpace ℝ Efin]
    (embed : Efin →L[ℝ] P.VacuumOrthogonalHilbert)
    (h : NNReal) (phi : Efin) :
    inner ℝ
      (T.timeAverageClosedRightHamiltonianDomain h
        ((embed phi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) :
          P.PhysicalHilbert)
      P.vacuum = 0 := by
  exact T.inner_timeAverageClosedRightHamiltonianDomain_vacuum_eq_zero_of_innerSymmetric
    hSymmetric h (embed phi).property

/-- A unit finite excitation therefore yields an eventually nonzero family of
actual graph-closed, vacuum-orthogonal continuum candidates. -/
theorem eventually_isometricExcitationEmbed_graphCandidate
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {Efin : Type*} [NormedAddCommGroup Efin] [NormedSpace ℝ Efin]
    (embed : Efin →L[ℝ] P.VacuumOrthogonalHilbert)
    (hembed_norm : ∀ x, ‖embed x‖ = ‖x‖)
    {phi : Efin} (hphi_norm : ‖phi‖ = 1) :
    ∀ᶠ h : NNReal in nhdsWithin 0 (Ioi 0),
      (T.timeAverageClosedRightHamiltonianDomain h
          ((embed phi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) :
        P.PhysicalHilbert) ≠ 0 ∧
      inner ℝ
        (T.timeAverageClosedRightHamiltonianDomain h
            ((embed phi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) :
          P.PhysicalHilbert)
        P.vacuum = 0 := by
  filter_upwards
    [T.eventually_timeAverageClosedRightHamiltonianDomain_norm_gt_half_of_isometricExcitationEmbed
      embed hembed_norm hphi_norm] with h hnorm
  constructor
  · exact norm_pos_iff.mp (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hnorm)
  · exact T.timeAverageClosedRightHamiltonianDomain_isometricExcitationEmbed_orthogonal
      hSymmetric embed h phi

end StronglyContinuousPhysicalSemigroup

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility

set_option maxHeartbeats 800000

variable
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
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
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant}
    {Qgap : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant C}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant P T C Qgap}

/-- The actual completed finite-excitation common-carrier embedding from #1564
turns every unit finite excitation into an eventually nonzero graph-domain
continuum excitation family. -/
theorem eventually_excitationEmbed_graphCandidate
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (n : ℕ)
    {phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).VacuumOrthogonalHilbert}
    (hphi_norm : ‖phi‖ = 1) :
    ∀ᶠ h : NNReal in nhdsWithin 0 (Ioi 0),
      (T.timeAverageClosedRightHamiltonianDomain h
          (((V.excitationEmbed n phi : P.VacuumOrthogonalHilbert) :
            P.PhysicalHilbert)) : P.PhysicalHilbert) ≠ 0 ∧
      inner ℝ
        (T.timeAverageClosedRightHamiltonianDomain h
            (((V.excitationEmbed n phi : P.VacuumOrthogonalHilbert) :
              P.PhysicalHilbert)) : P.PhysicalHilbert)
        P.vacuum = 0 := by
  exact T.eventually_isometricExcitationEmbed_graphCandidate
    hSymmetric (V.excitationEmbed n) (V.excitationEmbed_norm n) hphi_norm

/-- Full normalized reverse-spine candidate construction at a fixed finite
scale: choose a unit slow state from the actual completed finite Wilson
excitation operator, embed it isometrically in the continuum excitation sector,
and obtain actual graph-closed nonzero vacuum-orthogonal states for all
sufficiently small positive averaging widths.

The only remaining input after this theorem is quantitative moving-state
control of the graph-closed Hamiltonian/Rayleigh value. -/
theorem exists_unit_slowVector_with_eventual_graphCandidates
    (A : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveHalfBoundedOneStepAnalysis
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility G)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (n : ℕ)
    (hfactor : 0 < A.centeredTransferFactor n)
    {theta : ℝ} (htheta_pos : 0 < theta) (htheta_lt_one : theta < 1) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    ∃ phi : Pn.VacuumOrthogonalHilbert,
      ‖phi‖ = 1 ∧
      A.centeredTransferFactor n * theta <
        ‖A.physicalExcitationOneStepOperator n phi‖ ∧
      ‖V.excitationEmbed n phi‖ = 1 ∧
      (∀ᶠ h : NNReal in nhdsWithin 0 (Ioi 0),
        (T.timeAverageClosedRightHamiltonianDomain h
            (((V.excitationEmbed n phi : P.VacuumOrthogonalHilbert) :
              P.PhysicalHilbert)) : P.PhysicalHilbert) ≠ 0 ∧
        inner ℝ
          (T.timeAverageClosedRightHamiltonianDomain h
              (((V.excitationEmbed n phi : P.VacuumOrthogonalHilbert) :
                P.PhysicalHilbert)) : P.PhysicalHilbert)
          P.vacuum = 0) := by
  dsimp only
  rcases A.exists_unit_physicalExcitationApproximateSlowVector
      n hfactor htheta_pos htheta_lt_one with ⟨phi, hphi_norm, hslow⟩
  refine ⟨phi, hphi_norm, hslow, ?_, ?_⟩
  · exact V.excitationEmbed_norm n phi |>.trans hphi_norm
  · exact V.eventually_excitationEmbed_graphCandidate
      hSymmetric n hphi_norm

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
