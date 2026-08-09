import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonTwoStepVectorRecovery
import MGAP4D.MathlibAnalytic.ContinuousLinearMapIsometricSubmoduleRange
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance massFreeCarrierSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance massFreeCarrierSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance massFreeCarrierSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance massFreeCarrierSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance massFreeCarrierSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance massFreeCarrierSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Mass-free common-carrier data needed to embed the actual completed finite
Wilson OS Hilbert spaces into one continuum OS Hilbert space.

Unlike the historical `CommonCarrierGapTransfer`, this owner contains no finite
vacuum-gap certificate, mass, decay factor, or spectral datum.  It records only
an isometric finite-to-continuum Hilbert embedding and exact vacuum
compatibility. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (P : D.OSPreHilbertData) where
  embed :
    (n : ℕ) →
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n →L[ℝ]
        P.PhysicalHilbert
  embed_norm :
    ∀ n phi, ‖embed n phi‖ = ‖phi‖
  embed_vacuum :
    ∀ n,
      embed n
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta B hInvariant n) =
        P.vacuum

namespace PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding

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

/-- Restrict the ambient mass-free common-carrier embedding to the full
completed finite vacuum-orthogonal Hilbert space. -/
noncomputable def ambientExcitationEmbed
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding
      S D halfExtent N hN beta hbeta B hInvariant P)
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

/-- Vacuum preservation and finite vacuum orthogonality place the image of the
ambient excitation embedding in the continuum vacuum-orthogonal subspace. -/
theorem ambientExcitationEmbed_mem_vacuumOrthogonal
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding
      S D halfExtent N hN beta hbeta B hInvariant P)
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
    _ = 0 :=
      (Pn.mem_vacuumOrthogonal_iff (phi : Pn.PhysicalHilbert)).mp phi.property

/-- Isometric range data for the completed finite excitation embedding. -/
noncomputable def excitationRangeData
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding
      S D halfExtent N hN beta hbeta B hInvariant P)
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
excitation Hilbert space into the continuum excitation Hilbert space. -/
noncomputable def excitationEmbed
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding
      S D halfExtent N hN beta hbeta B hInvariant P)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    Pn.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert := by
  dsimp only
  exact (A.excitationRangeData n).toSubmodule

@[simp] theorem coe_excitationEmbed
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding
      S D halfExtent N hN beta hbeta B hInvariant P)
    (n : ℕ)
    (phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    ((A.excitationEmbed n phi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) =
      A.embed n (phi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).PhysicalHilbert) :=
  rfl

@[simp] theorem excitationEmbed_norm
    (A : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding
      S D halfExtent N hN beta hbeta B hInvariant P)
    (n : ℕ)
    (phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    ‖A.excitationEmbed n phi‖ = ‖phi‖ :=
  (A.excitationRangeData n).norm_toSubmodule phi

end PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding

/-- The genuinely dynamical remainder after the mass-free Hilbert embedding has
been constructed: a rate-scaled two-step residual on the actual completed
finite Wilson excitation Hilbert spaces.

The carrier itself supplies the excitation embedding, so this structure stores
only the `o(a_n)` dynamical error. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierTwoStepRecovery
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    (C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant)
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup) where
  carrier :
    PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierEmbedding
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant P
  vectorDefectExcess : ℕ → ℝ
  vectorDefectExcess_tendsto_zero : Tendsto vectorDefectExcess atTop (nhds 0)
  twoStepVectorDefect_le :
    ∀ n phi, ‖phi‖ = 1 →
      let K := C.boundedAnalysis.physicalExcitationOneStepOperator n
      let eta := carrier.excitationEmbed n ((K ∘L K) phi)
      let psi := carrier.excitationEmbed n phi
      ‖(eta : P.PhysicalHilbert) -
          T.toPhysicalSemigroup.operator
            (physicalYangMillsLatticeSpacingNNReal S n +
              physicalYangMillsLatticeSpacingNNReal S n)
            (psi : P.PhysicalHilbert)‖ ≤
        2 * S.latticeSpacing n * vectorDefectExcess n

namespace PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierTwoStepRecovery

set_option maxHeartbeats 800000

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ} {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta}
    {E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S}
    {R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E}
    {hInvariant : ∀ n, D.WeakStarReflectionInvariant
      (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicCenteredRateConvergence
      S D halfExtent N hN beta hbeta Q E R hInvariant}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}

/-- Forget the mass-free ambient carrier construction while retaining the
vector recovery interface consumed by #1576. -/
noncomputable def toTwoStepVectorRecoveryTransfer
    (V : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierTwoStepRecovery C P T) :
    PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateTwoStepVectorRecoveryTransfer C P T where
  excitationEmbed := V.carrier.excitationEmbed
  excitationEmbed_norm := V.carrier.excitationEmbed_norm
  vectorDefectExcess := V.vectorDefectExcess
  vectorDefectExcess_tendsto_zero := V.vectorDefectExcess_tendsto_zero
  twoStepVectorDefect_le := V.twoStepVectorDefect_le

/-- The mass-free common-carrier two-step residual already implies the reverse
physical Yang--Mills mass inequality. -/
theorem physicalYangMillsMass_le_limit
    (V : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierTwoStepRecovery C P T)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    T.physicalYangMillsMass ≤ C.limit :=
  V.toTwoStepVectorRecoveryTransfer.physicalYangMillsMass_le_limit hSymmetric

/-- The same mass-free common-carrier data produce a genuine continuum
excitation-domain witness. -/
theorem excitationDomainWitness_nonempty
    (V : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierTwoStepRecovery C P T)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    Nonempty T.PhysicalYangMillsExcitationDomainWitness :=
  V.toTwoStepVectorRecoveryTransfer.excitationDomainWitness_nonempty hSymmetric

/-- Combining the mass-free finite-to-continuum two-step recovery with the
independent continuum-to-finite intrinsic-rate transfer identifies the
intrinsic Wilson rate limit with the physical variational Yang--Mills mass. -/
theorem limit_eq_physicalYangMillsMass
    (V : PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierTwoStepRecovery C P T)
    (G : PhysicalYangMillsEvenPeriodicWilsonOSIntrinsicRateCommonCarrierTransfer
      S D halfExtent N hN beta hbeta Q E R hInvariant C P T)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    C.limit = T.physicalYangMillsMass :=
  V.toTwoStepVectorRecoveryTransfer.limit_eq_physicalYangMillsMass
    G hP hSymmetric

end PhysicalYangMillsEvenPeriodicWilsonOSMassFreeCommonCarrierTwoStepRecovery

end MathlibAnalytic
end MGAP4D

end