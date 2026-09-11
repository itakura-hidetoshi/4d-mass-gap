import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonBoundaryPoincareOptimalMass
import Mathlib.Tactic

noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

local instance wilsonFiniteOptimalSideLengthNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance wilsonFiniteOptimalSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonFiniteOptimalSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonFiniteOptimalSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonFiniteOptimalSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonFiniteOptimalSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Literal compact-Haar Wilson boundary Poincare coercivity at one fixed
lattice scale `n`.

This is the finite problem whose optimal coefficient is intended to be
computed from the actual Wilson action.  It contains no continuum limit and no
preselected exact mass value. -/
def physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAtScale
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) (m : ℝ) : Prop :=
  ∀ F : (physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
      S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n).Carrier,
    let Pn :=
      physical_yang_mills_evenPeriodicWilsonOS_approximating_preHilbertData
        S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n
    let Fc := Pn.vacuumCenteredCarrier F
    (2 * m * S.latticeSpacing n) *
        (∫ b,
          ‖physicalYangMillsEvenPeriodicWilsonOSBoundaryMoment
            S D halfExtent N hN beta hbeta Q.toWeakStarBridge hInvariant n Fc b‖ ^ 2
          ∂(periodicHypercubicEvenBoundaryHaarMeasure (halfExtent n) N)) ≤
      physicalYangMillsEvenPeriodicWilsonOSRealizableCenteredBoundaryDirichletEnergyMassFree
        S D halfExtent N hN beta hbeta Q E R hInvariant n F

/-- The nonnegative admissible masses for the literal Wilson boundary problem at
one fixed lattice scale. -/
def physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteAdmissibleMassSet
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) : Set ℝ :=
  {m | 0 ≤ m ∧
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAtScale
      S D halfExtent N hN beta hbeta Q E R hInvariant n m}

/-- The intrinsic finite-scale Wilson boundary Poincare mass is the supremum of
all coefficients valid for every actual finite Wilson carrier at that scale.

The sequence of these finite optimal masses is the natural numerical object to
analyze before taking the continuum limit. -/
noncomputable def physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteOptimalMass
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent N hN beta hbeta)
    (E : PhysicalFourDimensionalYangMillsContinuumEuclideanTimeTranslation S)
    (R : PhysicalYangMillsEvenPeriodicWilsonOSRealizablePositiveTemporalCovariance
      S D halfExtent N hN beta hbeta Q E)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (n : ℕ) : ℝ :=
  sSup (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteAdmissibleMassSet
    S D halfExtent N hN beta hbeta Q E R hInvariant n)

namespace PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteOptimalMass

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

/-- The continuum-scale admissibility predicate is definitionally exactly
nonnegativity plus eventual validity of the finite-scale Wilson problem. -/
theorem admissibleMass_iff_nonneg_eventually_atScale
    (m : ℝ) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
        S D halfExtent N hN beta hbeta Q E R hInvariant m ↔
      0 ≤ m ∧
        ∀ᶠ n in atTop,
          physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAtScale
            S D halfExtent N hN beta hbeta Q E R hInvariant n m := by
  rfl

/-- A globally admissible Wilson mass belongs to the finite admissible set at
all sufficiently fine scales. -/
theorem admissibleMass_eventually_mem_finiteAdmissibleMassSet
    {m : ℝ}
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m) :
    ∀ᶠ n in atTop,
      m ∈ physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant n := by
  filter_upwards [hm.2] with n hn
  exact ⟨hm.1, hn⟩

/-- Conversely, eventual finite-scale membership together with explicit
nonnegativity reconstructs the intrinsic global admissibility predicate. -/
theorem admissibleMass_of_nonneg_eventually_mem_finiteAdmissibleMassSet
    {m : ℝ}
    (hm0 : 0 ≤ m)
    (hm : ∀ᶠ n in atTop,
      m ∈ physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant n) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m := by
  exact ⟨hm0, hm.mono fun _ hn => hn.2⟩

/-- If the finite admissible sets are eventually bounded above, every globally
admissible Wilson mass is eventually below the corresponding intrinsic
finite-scale optimum. -/
theorem admissibleMass_eventually_le_finiteOptimalMass
    {m : ℝ}
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m)
    (hBdd : ∀ᶠ n in atTop,
      BddAbove
        (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteAdmissibleMassSet
          S D halfExtent N hN beta hbeta Q E R hInvariant n)) :
    ∀ᶠ n in atTop,
      m ≤ physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteOptimalMass
        S D halfExtent N hN beta hbeta Q E R hInvariant n := by
  filter_upwards [admissibleMass_eventually_mem_finiteAdmissibleMassSet hm, hBdd]
    with n hmem hbdd
  exact le_csSup hbdd hmem

/-- Therefore any limit of the intrinsic finite-scale optimal masses is an
upper bound for every globally admissible Wilson mass. -/
theorem admissibleMass_le_of_finiteOptimalMass_tendsto
    {m q : ℝ}
    (hm : physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMass
      S D halfExtent N hN beta hbeta Q E R hInvariant m)
    (hBdd : ∀ᶠ n in atTop,
      BddAbove
        (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteAdmissibleMassSet
          S D halfExtent N hN beta hbeta Q E R hInvariant n))
    (hq : Tendsto
      (fun n =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteOptimalMass
          S D halfExtent N hN beta hbeta Q E R hInvariant n)
      atTop (nhds q)) :
    m ≤ q := by
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hq
  exact admissibleMass_eventually_le_finiteOptimalMass hm hBdd

/-- A convergent finite-scale optimal-mass sequence therefore upper-bounds the
intrinsic global Wilson optimum.  This is one half of the finite-to-continuum
sharpness theorem required for a future exact numerical evaluation. -/
theorem optimalMass_le_of_finiteOptimalMass_tendsto
    {q : ℝ}
    (hNonempty :
      (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareAdmissibleMassSet
        S D halfExtent N hN beta hbeta Q E R hInvariant).Nonempty)
    (hBdd : ∀ᶠ n in atTop,
      BddAbove
        (physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteAdmissibleMassSet
          S D halfExtent N hN beta hbeta Q E R hInvariant n))
    (hq : Tendsto
      (fun n =>
        physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteOptimalMass
          S D halfExtent N hN beta hbeta Q E R hInvariant n)
      atTop (nhds q)) :
    physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
        S D halfExtent N hN beta hbeta Q E R hInvariant ≤ q := by
  unfold physicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareOptimalMass
  exact csSup_le hNonempty fun m hm =>
    admissibleMass_le_of_finiteOptimalMass_tendsto hm hBdd hq

end PhysicalYangMillsEvenPeriodicWilsonOSBoundaryPoincareFiniteOptimalMass

end MathlibAnalytic
end MGAP4D

end