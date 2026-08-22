import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalBoundaryVacuumGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingReflectedQuadraticGap
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace InnerProduct

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

/-- The adjoint of the completed physical-to-boundary isometry is a contraction.
This is the quantitative fact needed to transfer finite physical excitation
decay back to the whole canonical boundary excitation sector. -/
theorem completedLinearIsometry_adjoint_norm_le
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (n : ℕ)
    (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) :
    ‖(((L.completedLinearIsometry n).toContinuousLinearMap)†) v‖ ≤ ‖v‖ := by
  let J := L.completedLinearIsometry n
  let x := (J.toContinuousLinearMap)† v
  have hsq : ‖x‖ ^ 2 ≤ ‖v‖ * ‖x‖ := by
    calc
      ‖x‖ ^ 2 = inner ℝ x x := by
        simpa using (real_inner_self_eq_norm_sq x).symm
      _ = inner ℝ v (J x) := by
        dsimp [x]
        exact ContinuousLinearMap.adjoint_inner_left J.toContinuousLinearMap _ _
      _ ≤ ‖v‖ * ‖J x‖ := real_inner_le_norm _ _
      _ = ‖v‖ * ‖x‖ := by rw [J.norm_map]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  nlinarith

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate

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

/-- A finite physical vacuum-gap certificate with nonnegative decay factor
induces the corrected canonical boundary excitation certificate.

The nonnegativity is exactly what is needed to pass from `‖J†v‖ ≤ ‖v‖` to the
same multiplicative decay bound on all boundary excitation vectors, including
the component orthogonal to the physical boundary image. -/
noncomputable def toCanonicalBoundaryVacuumGapCertificate
    (G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant)
    (hDecayNonneg : ∀ t, 0 ≤ G.decayFactor t) :
    PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant L C where
  mass := G.mass
  mass_pos := G.mass_pos
  decayFactor := G.decayFactor
  slope_tendsto := G.slope_tendsto
  exchange := G.exchange
  boundary_decay := by
    intro n t v
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    let J := L.completedLinearIsometry n
    let Jadj :
        PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N →L[ℝ]
          PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
            S D halfExtent N hN beta hbeta B hInvariant n :=
      (J.toContinuousLinearMap)†
    have hAdjMem :
        Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N) ∈
          Pn.vacuumOrthogonal := by
      dsimp [Jadj, J]
      exact
        L.completedLinearIsometry_adjoint_mem_vacuumOrthogonal
          n
          (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
          v.property
    have hAdjInner :
        inner ℝ
            (Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N))
            Pn.vacuum = 0 := by
      have h0 :=
        (Pn.mem_vacuumOrthogonal_iff
          (Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
            (halfExtent n) N))).mp hAdjMem
      rw [real_inner_comm]
      exact h0
    have hDecay :
        ‖C.finiteOperator n t
            (Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
              (halfExtent n) N))‖ ≤
          G.decayFactor t *
            ‖Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
              (halfExtent n) N)‖ := by
      exact G.finite_decay n t _ (by simpa [Pn] using hAdjInner)
    have hAdjNorm :
        ‖Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
          (halfExtent n) N)‖ ≤
          ‖(v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
            (halfExtent n) N)‖ := by
      dsimp [Jadj, J]
      exact
        L.completedLinearIsometry_adjoint_norm_le n
          (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)
    have htime : (2 * t) / 2 = t := by
      ext
      norm_num
    change
      ‖L.canonicalBoundaryTransfer C n (2 * t)
          (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2 (halfExtent n) N)‖ ≤
        G.decayFactor t *
          ‖(v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
            (halfExtent n) N)‖
    change
      ‖J (C.finiteOperator n ((2 * t) / 2)
          (Jadj (v : PeriodicHypercubicEvenSpecialUnitaryBoundaryL2
            (halfExtent n) N)))‖ ≤ _
    rw [htime, J.norm_map]
    exact hDecay.trans
      (mul_le_mul_of_nonneg_left hAdjNorm (hDecayNonneg t))

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate

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

/-- The quadratic finite Wilson OS gap certificate canonically produces the
corrected shared-boundary excitation certificate.  Its norm-decay factor is a
square root and hence automatically nonnegative. -/
noncomputable def toCanonicalBoundaryVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant L C :=
  Q.toApproximatingVacuumGapCertificate.toCanonicalBoundaryVacuumGapCertificate
    L
    (fun t => Real.sqrt_nonneg _)

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingQuadraticGapCertificate

namespace PhysicalYangMillsEvenPeriodicWilsonOSApproximatingReflectedQuadraticGapCertificate

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

/-- The centered reflected Wilson integral inequality, which is the closest
current interface to the concrete even-periodic Wilson Gibbs factorization,
therefore generates the corrected canonical boundary excitation gap
certificate without any all-boundary strict-contraction hypothesis. -/
noncomputable def toCanonicalBoundaryVacuumGapCertificate
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingReflectedQuadraticGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (L : PhysicalYangMillsEvenPeriodicWilsonOSBoundaryMomentLinearCoherence
      S D halfExtent N hN beta hbeta B hInvariant) :
    PhysicalYangMillsEvenPeriodicWilsonOSCanonicalBoundaryVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant L C :=
  Q.toApproximatingObservableQuadraticGapCertificate
    |>.toApproximatingQuadraticGapCertificate
    |>.toCanonicalBoundaryVacuumGapCertificate L

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingReflectedQuadraticGapCertificate

end MathlibAnalytic
end MGAP4D

end
