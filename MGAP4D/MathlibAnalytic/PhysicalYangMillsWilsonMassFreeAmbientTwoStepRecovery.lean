import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonTwoStepVectorRecovery
import MGAP4D.MathlibAnalytic.ContinuousLinearMapIsometricSubmoduleRange
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A mass-free finite-to-continuum common carrier for the actual completed
finite Wilson OS Hilbert spaces.

Only the ambient isometric embeddings and vacuum preservation are stored.  In
particular, the owner type contains no vacuum-gap certificate, no mass, no
decay factor, no continuum semigroup, and no spectral data. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (P : D.OSPreHilbertData) where
  embed :
    (n : ℕ) →
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n →L[ℝ]
        P.PhysicalHilbert
  embed_norm :
    ∀ n
      (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n),
      ‖embed n phi‖ = ‖phi‖
  embed_vacuum :
    ∀ n,
      embed n
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta B hInvariant n) =
        P.vacuum

namespace PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {P : D.OSPreHilbertData}

/-- Restrict the ambient carrier map to the complete finite vacuum-orthogonal
Hilbert space, still with ambient continuum codomain. -/
noncomputable def ambientExcitationEmbed
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := B) (hInvariant := hInvariant) P)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    Pn.VacuumOrthogonalHilbert →L[ℝ] P.PhysicalHilbert := by
  dsimp only
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  exact (A.embed n).comp Pn.vacuumOrthogonal.subtypeL

/-- Vacuum preservation and isometry put every embedded finite excitation in
the continuum vacuum-orthogonal subspace. -/
theorem ambientExcitationEmbed_mem_vacuumOrthogonal
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := B) (hInvariant := hInvariant) P)
    (n : ℕ)
    (phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    A.ambientExcitationEmbed n phi ∈ P.vacuumOrthogonal := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  rw [P.mem_vacuumOrthogonal_iff]
  calc
    inner ℝ P.vacuum (A.ambientExcitationEmbed n phi) =
        inner ℝ
          (A.embed n
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
              S D halfExtent N hN beta hbeta B hInvariant n))
          (A.embed n (phi : Pn.PhysicalHilbert)) := by
      rw [A.embed_vacuum n]
      rfl
    _ = inner ℝ
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta B hInvariant n)
        (phi : Pn.PhysicalHilbert) := by
      exact ContinuousLinearMap.inner_map_map_of_norm_map
        (A.embed n) (A.embed_norm n)
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta B hInvariant n)
        (phi : Pn.PhysicalHilbert)
    _ = 0 := by
      exact (Pn.mem_vacuumOrthogonal_iff (phi : Pn.PhysicalHilbert)).mp phi.property

/-- The ambient finite-excitation restriction together with exact isometry and
continuum excitation-range membership. -/
noncomputable def excitationRangeData
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := B) (hInvariant := hInvariant) P)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    ContinuousLinearMap.IsometricSubmoduleRangeData
      (A.ambientExcitationEmbed n) P.vacuumOrthogonal := by
  dsimp only
  refine {
    map_mem := A.ambientExcitationEmbed_mem_vacuumOrthogonal n
    norm_map := ?_ }
  intro phi
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  calc
    ‖A.ambientExcitationEmbed n phi‖ =
        ‖A.embed n (phi : Pn.PhysicalHilbert)‖ := rfl
    _ = ‖(phi : Pn.PhysicalHilbert)‖ := A.embed_norm n _
    _ = ‖phi‖ := rfl

/-- Canonical isometric embedding of the full completed finite Wilson
vacuum-orthogonal Hilbert space into the continuum excitation Hilbert space. -/
noncomputable def excitationEmbed
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := B) (hInvariant := hInvariant) P)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    Pn.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert := by
  dsimp only
  exact (A.excitationRangeData n).toSubmodule

@[simp] theorem coe_excitationEmbed
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := B) (hInvariant := hInvariant) P)
    (n : ℕ)
    (phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    ((A.excitationEmbed n phi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) =
      A.embed n
        (phi :
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
            S D halfExtent N hN beta hbeta B hInvariant n).PhysicalHilbert) :=
  rfl

/-- The mass-free full finite-excitation embedding preserves every norm exactly. -/
theorem excitationEmbed_norm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := B) (hInvariant := hInvariant) P)
    (n : ℕ)
    (phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    ‖A.excitationEmbed n phi‖ = ‖phi‖ :=
  (A.excitationRangeData n).norm_toSubmodule phi

end PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier

/-- The remaining dynamical reverse input after the ambient common carrier has
been separated completely from any gap certificate.

The only scale-dependent analytic residual is the same rate-scaled two-step
vector defect used by the vector recovery theorem.  The excitation embedding
itself is theorem-generated from the mass-free ambient carrier. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientTwoStepRecovery
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
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.toWeakStarBridge) (hInvariant := hInvariant) P) where
  vectorDefectExcess : ℕ → ℝ
  vectorDefectExcess_tendsto_zero : Tendsto vectorDefectExcess atTop (nhds 0)
  twoStepVectorDefect_le :
    ∀ n phi, ‖phi‖ = 1 →
      let K := C.boundedAnalysis.physicalExcitationOneStepOperator n
      let eta := A.excitationEmbed n ((K ∘L K) phi)
      let psi := A.excitationEmbed n phi
      ‖(eta : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator
            (physicalYangMillsLatticeSpacingNNReal S n +
              physicalYangMillsLatticeSpacingNNReal S n)
            (psi : P.PhysicalHilbert)‖ ≤
        2 * S.latticeSpacing n * vectorDefectExcess n

namespace PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientTwoStepRecovery

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
    {C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := Q.toWeakStarBridge) (hInvariant := hInvariant) P}

/-- Forget the ambient presentation after theorem-generating the exact
vacuum-orthogonal isometric embedding. -/
noncomputable def toTwoStepVectorRecoveryTransfer
    (V : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientTwoStepRecovery
      C P T A) :
    PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateTwoStepVectorRecoveryTransfer
      C P T where
  excitationEmbed := A.excitationEmbed
  excitationEmbed_norm := A.excitationEmbed_norm
  vectorDefectExcess := V.vectorDefectExcess
  vectorDefectExcess_tendsto_zero := V.vectorDefectExcess_tendsto_zero
  twoStepVectorDefect_le := V.twoStepVectorDefect_le

/-- The mass-free ambient carrier plus its rate-scaled two-step vector defect
already imply the reverse physical variational inequality. -/
theorem physicalYangMillsMass_le_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientTwoStepRecovery
      C P T A)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    T.physicalYangMillsMass ≤ C.limit :=
  V.toTwoStepVectorRecoveryTransfer.physicalYangMillsMass_le_limit hSymmetric

/-- The same data theorem-generate a genuine nonzero continuum excitation
witness, so no separate physical excitation hypothesis is needed downstream. -/
theorem excitationDomainWitness_nonempty
    (V : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientTwoStepRecovery
      C P T A)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    Nonempty T.PhysicalYangMillsExcitationDomainWitness :=
  V.toTwoStepVectorRecoveryTransfer.excitationDomainWitness_nonempty hSymmetric

/-- Combine the theorem-generated reverse inequality with the existing
mass-free continuum-to-finite common-carrier direction to identify the
intrinsic Wilson rate limit with the physical Yang--Mills variational mass.

The reverse owner type contains no legacy vacuum-gap certificate. -/
theorem limit_eq_physicalYangMillsMass
    (V : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientTwoStepRecovery
      C P T A)
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    C.limit = T.physicalYangMillsMass :=
  V.toTwoStepVectorRecoveryTransfer.limit_eq_physicalYangMillsMass
    G hP hSymmetric

end PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientTwoStepRecovery

end MathlibAnalytic
end MGAP4D

end