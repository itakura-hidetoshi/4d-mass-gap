import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonMassFreeAmbientTwoStepRecovery
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveLimitL2CylinderIsometricSystem
import MGAP4D.MathlibAnalytic.RealHilbertLinearIsometricOperatorTransport
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

/-- Proof-relevant compact-Wilson/projective-`L²` carrier identification.

The finite completed Wilson OS Hilbert space is **not** identified with a raw
finite probability `L²` space.  Instead, each finite OS carrier is identified
isometrically with a selected Hilbert subspace of one finite projective
marginal.  Canonical projective pullback then places that subspace in the
continuum `L²` carrier, and only a selected continuum OS subspace is identified
with the physical Hilbert space.

This separation keeps the reflection-positive quotient/completion visible and
prevents an unjustified raw-`L²` identification. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
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
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (P : D.OSPreHilbertData) where
  marginalIndex : ℕ → Finset EuclideanFourSpace
  marginalSubspace :
    (n : ℕ) →
      Submodule ℝ (Lp ℝ 2 (F.finiteMarginal (marginalIndex n)))
  finiteIdentification :
    (n : ℕ) →
      RealHilbertLinearIsometricIdentification
        (PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n)
        (marginalSubspace n)
  continuumOSSubspace :
    Submodule ℝ (Lp ℝ 2 L.continuumMeasure)
  finiteImage_mem_continuumOS :
    ∀ n
      (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n),
      L.finiteMarginalL2Pullback (marginalIndex n)
          ((marginalSubspace n).subtypeL
            ((finiteIdentification n).forward phi)) ∈
        continuumOSSubspace
  physicalIdentification :
    RealHilbertLinearIsometricIdentification
      continuumOSSubspace P.PhysicalHilbert

namespace PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification

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
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {P : D.OSPreHilbertData}

/-- Embed the actual completed finite Wilson OS Hilbert space into the selected
finite projective marginal `L²` subspace and then forget only the subspace
wrapper.  Surjectivity onto the full marginal is neither assumed nor needed. -/
noncomputable def marginalEmbed
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n →L[ℝ]
      Lp ℝ 2 (F.finiteMarginal (I.marginalIndex n)) :=
  (I.marginalSubspace n).subtypeL.comp
    (I.finiteIdentification n).forward.toContinuousLinearMap

@[simp] theorem marginalEmbed_apply
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    I.marginalEmbed n phi =
      ((I.finiteIdentification n).forward phi :
        Lp ℝ 2 (F.finiteMarginal (I.marginalIndex n))) :=
  rfl

/-- The finite OS-to-marginal embedding is exactly isometric. -/
@[simp] theorem marginalEmbed_norm
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    ‖I.marginalEmbed n phi‖ = ‖phi‖ := by
  rw [I.marginalEmbed_apply]
  exact (I.finiteIdentification n).forward.norm_map phi

/-- Canonical common-carrier embedding into the projective-limit continuum
`L²` space. -/
noncomputable def projectiveL2Embed
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n →L[ℝ]
      Lp ℝ 2 L.continuumMeasure :=
  (L.finiteMarginalL2Pullback
      (I.marginalIndex n)).toContinuousLinearMap.comp
    (I.marginalEmbed n)

@[simp] theorem projectiveL2Embed_apply
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    I.projectiveL2Embed n phi =
      L.finiteMarginalL2Pullback (I.marginalIndex n)
        (I.marginalEmbed n phi) :=
  rfl

/-- Canonical projective pullback preserves the actual finite OS norm exactly. -/
@[simp] theorem projectiveL2Embed_norm
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    ‖I.projectiveL2Embed n phi‖ = ‖phi‖ := by
  rw [I.projectiveL2Embed_apply,
    L.finiteMarginalL2Pullback_norm,
    I.marginalEmbed_norm]

/-- The projective finite image, together with exact isometry and the explicit
continuum OS range condition. -/
noncomputable def continuumOSRangeData
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ) :
    ContinuousLinearMap.IsometricSubmoduleRangeData
      (I.projectiveL2Embed n) I.continuumOSSubspace where
  map_mem := by
    intro phi
    simpa [projectiveL2Embed, marginalEmbed] using
      I.finiteImage_mem_continuumOS n phi
  norm_map := I.projectiveL2Embed_norm n

/-- Restrict the canonical projective embedding to the selected continuum OS
Hilbert subspace. -/
noncomputable def continuumOSEmbed
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n →L[ℝ]
      I.continuumOSSubspace :=
  (I.continuumOSRangeData n).toSubmodule

@[simp] theorem coe_continuumOSEmbed
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    ((I.continuumOSEmbed n phi : I.continuumOSSubspace) :
        Lp ℝ 2 L.continuumMeasure) =
      I.projectiveL2Embed n phi :=
  rfl

/-- The selected continuum OS embedding remains exactly isometric. -/
@[simp] theorem continuumOSEmbed_norm
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    ‖I.continuumOSEmbed n phi‖ = ‖phi‖ :=
  (I.continuumOSRangeData n).norm_toSubmodule phi

/-- Final finite-to-physical embedding obtained by composing only genuine
isometric identifications. -/
noncomputable def physicalEmbed
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n →L[ℝ]
      P.PhysicalHilbert :=
  I.physicalIdentification.forward.toContinuousLinearMap.comp
    (I.continuumOSEmbed n)

@[simp] theorem physicalEmbed_norm
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ)
    (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    ‖I.physicalEmbed n phi‖ = ‖phi‖ := by
  change ‖I.physicalIdentification.forward (I.continuumOSEmbed n phi)‖ = ‖phi‖
  rw [I.physicalIdentification.forward.norm_map,
    I.continuumOSEmbed_norm]

/-- The theorem-generated finite-to-physical map preserves the real inner
product exactly. -/
@[simp] theorem physicalEmbed_inner
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P)
    (n : ℕ)
    (phi psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    inner ℝ (I.physicalEmbed n phi) (I.physicalEmbed n psi) =
      inner ℝ phi psi :=
  ContinuousLinearMap.inner_map_map_of_norm_map
    (I.physicalEmbed n) (I.physicalEmbed_norm n) phi psi

end PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification

/-- Model-facing vacuum compatibility on top of the proof-relevant projective
carrier identification.  This is the only additional datum needed to generate
#1578's mass-free ambient carrier. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMassFreeCarrierInput
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
    (F : EuclideanYangMillsProjectiveCylinderFamily)
    (L : EuclideanYangMillsProjectiveLimitMeasure F)
    (P : D.OSPreHilbertData) where
  identification :
    PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMarginalL2Identification
      (B := B) (hInvariant := hInvariant) F L P
  vacuumCompatibility :
    ∀ n,
      identification.physicalEmbed n
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta B hInvariant n) =
        P.vacuum

namespace PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMassFreeCarrierInput

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
    {F : EuclideanYangMillsProjectiveCylinderFamily}
    {L : EuclideanYangMillsProjectiveLimitMeasure F}
    {P : D.OSPreHilbertData}

/-- The projective-marginal identification theorem-generates exactly the
mass-free ambient carrier required by the reverse two-step recovery lane. -/
noncomputable def toMassFreeAmbientCarrier
    (I : PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMassFreeCarrierInput
      (B := B) (hInvariant := hInvariant) F L P) :
    PhysicalYangMillsEvenPeriodicWilsonOSMassFreeAmbientCarrier
      (B := B) (hInvariant := hInvariant) P where
  embed := I.identification.physicalEmbed
  embed_norm := I.identification.physicalEmbed_norm
  embed_vacuum := I.vacuumCompatibility

end PhysicalYangMillsEvenPeriodicWilsonOSProjectiveMassFreeCarrierInput

end

end MathlibAnalytic
end MGAP4D
