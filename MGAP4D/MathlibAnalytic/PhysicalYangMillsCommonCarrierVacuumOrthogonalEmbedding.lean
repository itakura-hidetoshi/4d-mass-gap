import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCommonCarrierFiniteWilsonExcitationStrongLimit
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

/-- Vacuum compatibility for the already constructed common-carrier finite-to-
continuum embedding.

This is the only extra compatibility needed to restrict the full finite OS
vacuum-orthogonal Hilbert space to the continuum vacuum-orthogonal Hilbert
space.  No spectral vector, mass value, or numerical gap enters this package. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility
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
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q) where
  embed_vacuum :
    ∀ n,
      A.embed n
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta B hInvariant n) =
        P.vacuum

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility

variable
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
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}
    {A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C Q}

/-- The ambient common-carrier map restricted to the complete finite OS
vacuum-orthogonal Hilbert space. -/
noncomputable def ambientExcitationEmbed
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility A)
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

/-- Vacuum preservation and finite vacuum orthogonality put every finite OS
excitation in the continuum vacuum-orthogonal subspace. -/
theorem ambientExcitationEmbed_mem_vacuumOrthogonal
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility A)
    (n : ℕ)
    (phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    V.ambientExcitationEmbed n phi ∈ P.vacuumOrthogonal := by
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  rw [P.mem_vacuumOrthogonal_iff]
  calc
    inner ℝ P.vacuum (V.ambientExcitationEmbed n phi) =
        inner ℝ
          (A.embed n
            (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
              S D halfExtent N hN beta hbeta B hInvariant n))
          (A.embed n (phi : Pn.PhysicalHilbert)) := by
      rw [V.embed_vacuum n]
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

/-- The restricted ambient map is isometric and has image in the continuum
excitation submodule. -/
noncomputable def excitationRangeData
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility A)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    ContinuousLinearMap.IsometricSubmoduleRangeData
      (V.ambientExcitationEmbed n) P.vacuumOrthogonal := by
  dsimp only
  refine {
    map_mem := V.ambientExcitationEmbed_mem_vacuumOrthogonal n
    norm_map := ?_ }
  intro phi
  let Pn :=
    physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta B hInvariant n
  calc
    ‖V.ambientExcitationEmbed n phi‖ =
        ‖A.embed n (phi : Pn.PhysicalHilbert)‖ := rfl
    _ = ‖(phi : Pn.PhysicalHilbert)‖ := A.embed_norm n _
    _ = ‖phi‖ := rfl

/-- Canonical isometric embedding of the **full completed finite physical
excitation Hilbert space** into the continuum physical excitation Hilbert
space. -/
noncomputable def excitationEmbed
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility A)
    (n : ℕ) :
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    Pn.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert := by
  dsimp only
  exact (V.excitationRangeData n).toSubmodule

@[simp] theorem coe_excitationEmbed
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility A)
    (n : ℕ)
    (phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    ((V.excitationEmbed n phi : P.VacuumOrthogonalHilbert) : P.PhysicalHilbert) =
      A.embed n (phi :
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
          S D halfExtent N hN beta hbeta B hInvariant n).PhysicalHilbert) :=
  rfl

/-- The full finite-excitation common-carrier embedding preserves norm. -/
theorem excitationEmbed_norm
    (V : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility A)
    (n : ℕ)
    (phi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    ‖V.excitationEmbed n phi‖ = ‖phi‖ :=
  (V.excitationRangeData n).norm_toSubmodule phi

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierVacuumCompatibility

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D