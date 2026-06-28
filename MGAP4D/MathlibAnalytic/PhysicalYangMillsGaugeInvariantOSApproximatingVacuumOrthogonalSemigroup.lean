import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingHilbertSemigroup
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace PhysicalSemigroup

/-- A symmetric physical semigroup which fixes the vacuum preserves the scalar
vacuum coefficient. -/
theorem operator_inner_vacuum_eq
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert) :
    inner ℝ (T.operator t psi) P.vacuum = inner ℝ psi P.vacuum := by
  calc
    inner ℝ (T.operator t psi) P.vacuum =
        inner ℝ psi (T.operator t P.vacuum) :=
      hSymmetric t psi P.vacuum
    _ = inner ℝ psi P.vacuum := by rw [T.fixes_vacuum]

/-- Every symmetric vacuum-fixing physical semigroup preserves the complete
vacuum-orthogonal excitation sector. -/
theorem operator_mem_vacuumOrthogonal
    (T : P.PhysicalSemigroup)
    (hSymmetric : T.IsInnerSymmetric)
    (t : NNReal) (psi : P.PhysicalHilbert)
    (hpsi : psi ∈ P.vacuumOrthogonal) :
    T.operator t psi ∈ P.vacuumOrthogonal := by
  rw [P.mem_vacuumOrthogonal_iff] at hpsi ⊢
  calc
    inner ℝ P.vacuum (T.operator t psi) =
        inner ℝ (T.operator t psi) P.vacuum := real_inner_comm _ _
    _ = inner ℝ psi P.vacuum :=
      T.operator_inner_vacuum_eq hSymmetric t psi
    _ = inner ℝ P.vacuum psi := real_inner_comm _ _
    _ = 0 := hpsi

end PhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

/-- Quantitative finite-volume vacuum-gap data on the actual approximating
Wilson OS Hilbert spaces.

The exchange field gives symmetry of every completed transfer operator.  The
finite decay field is the remaining model-specific estimate on vectors
orthogonal to the normalized finite-volume vacuum.  The common scalar slope is
the quantity which survives the continuum transfer argument. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
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
  finite_decay :
    ∀ (n : ℕ) (t : NNReal)
      (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n),
      inner ℝ phi
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta B hInvariant n) = 0 →
        ‖C.finiteOperator n t phi‖ ≤ decayFactor t * ‖phi‖

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

/-- The OS exchange identity makes the completed transfer operator symmetric on
every finite-volume Wilson OS Hilbert space. -/
theorem finitePhysicalSemigroup_isInnerSymmetric
    (G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) :
    (C.finitePhysicalSemigroup n).IsInnerSymmetric := by
  exact
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PositiveTimeObservableContractionSemigroup.ReflectionTimeTranslationExchange.toPhysicalSemigroup_isInnerSymmetric
      (G.exchange n)

/-- Symmetry transfers Euclidean time between the two entries of the finite
Wilson OS Hilbert inner product. -/
theorem finiteOperator_inner_eq
    (G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (psi phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    inner ℝ (C.finiteOperator n t psi) phi =
      inner ℝ psi (C.finiteOperator n t phi) := by
  exact G.finitePhysicalSemigroup_isInnerSymmetric n t psi phi

/-- The scalar component along the normalized finite-volume vacuum is invariant
under the completed transfer operator. -/
theorem finiteOperator_inner_vacuum_eq
    (G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal)
    (psi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n) :
    inner ℝ (C.finiteOperator n t psi)
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta B hInvariant n) =
      inner ℝ psi
        (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
          S D halfExtent N hN beta hbeta B hInvariant n) := by
  exact
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PhysicalSemigroup.operator_inner_vacuum_eq
      (C.finitePhysicalSemigroup n)
      (G.finitePhysicalSemigroup_isInnerSymmetric n) t psi

/-- The actual completed finite-volume Wilson transfer operator preserves the
vacuum-orthogonal excitation subspace. -/
theorem finiteOperator_mem_vacuumOrthogonal
    (G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C)
    (n : ℕ) (t : NNReal) :
    let P :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta B hInvariant n
    ∀ psi : P.PhysicalHilbert,
      psi ∈ P.vacuumOrthogonal →
        C.finiteOperator n t psi ∈ P.vacuumOrthogonal := by
  dsimp only
  intro psi hpsi
  exact
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.PhysicalSemigroup.operator_mem_vacuumOrthogonal
      (C.finitePhysicalSemigroup n)
      (G.finitePhysicalSemigroup_isInnerSymmetric n) t psi hpsi

end PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate

end MathlibAnalytic
end MGAP4D

end
