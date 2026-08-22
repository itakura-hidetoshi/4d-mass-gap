import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalBoundaryVacuumOrthogonalTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingVacuumOrthogonalSemigroup
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

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
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- On the physical excitation image, the canonical boundary transfer has
exactly the same norm as the finite Wilson OS transfer at half the boundary
time.  This is the quantitative form of the exact intertwining from the
vacuum-orthogonal carrier construction. -/
theorem canonicalBoundaryVacuumOrthogonalTransfer_image_norm
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal)
    (psi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    ‖L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t
        (L.completedVacuumOrthogonalLinearIsometry n psi)‖ =
      ‖C.finiteOperator n (t / 2)
        (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n)‖ := by
  change
    ‖((L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t
          (L.completedVacuumOrthogonalLinearIsometry n psi) :
        L.CanonicalBoundaryVacuumOrthogonalHilbert n) :
      PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)‖ = _
  rw [L.canonicalBoundaryVacuumOrthogonalTransfer_intertwining
    C hExchange n t psi]
  exact
    (L.completedLinearIsometry n).norm_map
      (C.finiteOperator n (t / 2)
        (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n))

/-- The squared norm defect on the physical excitation image is therefore
identical on the finite OS Hilbert side and the canonical boundary side. -/
theorem canonicalBoundaryVacuumOrthogonalTransfer_image_defect
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (hExchange : ∀ n,
      PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
        (C.toPositiveTimeObservableContractionSemigroup n))
    (n : ℕ) (t : NNReal)
    (psi :
      (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n).VacuumOrthogonalHilbert) :
    ‖(psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n)‖ ^ 2 -
        ‖C.finiteOperator n (t / 2)
          (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
            S D halfExtent N hN beta hbeta B hInvariant n)‖ ^ 2 =
      ‖L.completedVacuumOrthogonalLinearIsometry n psi‖ ^ 2 -
        ‖L.canonicalBoundaryVacuumOrthogonalTransfer C hExchange n t
          (L.completedVacuumOrthogonalLinearIsometry n psi)‖ ^ 2 := by
  rw [(L.completedVacuumOrthogonalLinearIsometry n).norm_map]
  rw [L.canonicalBoundaryVacuumOrthogonalTransfer_image_norm
    C hExchange n t psi]

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

/-- The remaining model-specific strict estimate, stated on the correct
canonical shared-boundary excitation carrier.

The boundary time is `2 * t` because the canonical boundary transfer is
`J T_(t/2) J†`.  Thus this field measures precisely the finite physical OS
transfer at time `t`, rather than the full boundary operator which necessarily
has norm one because it fixes the vacuum. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryVacuumGapCertificate
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
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant) where
  mass : ℝ
  mass_pos : 0 < mass
  decayFactor : NNReal → ℝ
  slope_tendsto :
    Tendsto
      (fun t : NNReal => (t : ℝ)⁻¹ * (1 - decayFactor t))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  exchange : ∀ n,
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange
      (C.toPositiveTimeObservableContractionSemigroup n)
  boundary_decay :
    ∀ (n : ℕ) (t : NNReal)
      (v : L.CanonicalBoundaryVacuumOrthogonalHilbert n),
      ‖L.canonicalBoundaryVacuumOrthogonalTransfer C exchange n (2 * t) v‖ ≤
        decayFactor t * ‖v‖

namespace PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryVacuumGapCertificate

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
    {L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}

/-- A strict decay estimate on the canonical boundary excitation carrier
supplies exactly the existing finite Wilson OS vacuum-gap certificate.  All
existing common-carrier and continuum gap-transfer theorems can therefore be
reused without changing their interfaces. -/
noncomputable def toApproximatingVacuumGapCertificate
    (G : PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant L C) :
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C where
  mass := G.mass
  mass_pos := G.mass_pos
  decayFactor := G.decayFactor
  slope_tendsto := G.slope_tendsto
  exchange := G.exchange
  finite_decay := by
    intro n t phi hphi
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    have hphiMem : phi ∈ Pn.vacuumOrthogonal := by
      rw [Pn.mem_vacuumOrthogonal_iff]
      have hphi0 : inner ℝ phi Pn.vacuum = 0 := by
        simpa [Pn] using hphi
      calc
        inner ℝ Pn.vacuum phi = inner ℝ phi Pn.vacuum := real_inner_comm _ _
        _ = 0 := hphi0
    let psi : Pn.VacuumOrthogonalHilbert := ⟨phi, hphiMem⟩
    have htime : (2 * t) / 2 = t := by
      ext
      norm_num
    have hnorm :
        ‖L.canonicalBoundaryVacuumOrthogonalTransfer C G.exchange n (2 * t)
            (L.completedVacuumOrthogonalLinearIsometry n psi)‖ =
          ‖C.finiteOperator n t phi‖ := by
      have h :=
        L.canonicalBoundaryVacuumOrthogonalTransfer_image_norm
          C G.exchange n (2 * t) psi
      simpa only [htime] using h
    calc
      ‖C.finiteOperator n t phi‖ =
          ‖L.canonicalBoundaryVacuumOrthogonalTransfer C G.exchange n (2 * t)
            (L.completedVacuumOrthogonalLinearIsometry n psi)‖ := hnorm.symm
      _ ≤ G.decayFactor t *
          ‖L.completedVacuumOrthogonalLinearIsometry n psi‖ :=
        G.boundary_decay n t (L.completedVacuumOrthogonalLinearIsometry n psi)
      _ = G.decayFactor t * ‖phi‖ := by
        rw [(L.completedVacuumOrthogonalLinearIsometry n).norm_map]
        rfl

end PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryVacuumGapCertificate

end MathlibAnalytic
end MGAP4D

end
