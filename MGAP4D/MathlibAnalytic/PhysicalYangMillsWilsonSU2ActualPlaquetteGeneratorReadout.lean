import MGAP4D.MathlibAnalytic.ContinuousMapBoundedOfCompactAlgebra
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryActualPlaquetteAlgebraGramClosure
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadableSubalgebra
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set

noncomputable section

private theorem actualPlaquetteGeneratorReadoutTwoRankPositive : 0 < (2 : ℕ) := by
  norm_num

local instance actualPlaquetteGeneratorReadoutNeZero (H : ℕ) :
    NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
  simp [PeriodicHypercubicEvenSideLength]⟩

local instance actualPlaquetteGeneratorReadoutTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2

local instance actualPlaquetteGeneratorReadoutCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2

local instance actualPlaquetteGeneratorReadoutSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2

local instance actualPlaquetteGeneratorReadoutMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2

local instance actualPlaquetteGeneratorReadoutBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

local instance actualPlaquetteGeneratorReadoutSU2Nontrivial :
    Nontrivial (Matrix.specialUnitaryGroup (Fin 2) ℂ) := by
  refine ⟨⟨1, specialUnitaryTwoRotation Real.pi, ?_⟩⟩
  intro h
  have h00 := congrArg
    (fun U : Matrix.specialUnitaryGroup (Fin 2) ℂ =>
      (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num [specialUnitaryTwoRotation, specialUnitaryTwoRotationMatrix] at h00

/-- The bounded-continuous representative of one concrete boundary-fibered
actual `SU(2)` plaquette-energy generator on the positive open half.

The conversion from `C(X, ℝ)` to `C_b(X, ℝ)` is the canonical compact-domain
algebra homomorphism.  Hence all polynomial operations are fixed at the actual
finite cylinder level before entering the merely-linear coherent OS pullback. -/
noncomputable def periodicHypercubicEvenBoundaryPlaquetteEnergyBoundedContinuousFunction
    (H : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (p : PeriodicHypercubicEvenPlaquette H) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) ℝ :=
  continuousMapAlgHomBoundedOfCompact
      (PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2)
    (periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap
      H 2 actualPlaquetteGeneratorReadoutTwoRankPositive b p)

@[simp] theorem periodicHypercubicEvenBoundaryPlaquetteEnergyBoundedContinuousFunction_apply
    (H : ℕ)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H 2)
    (p : PeriodicHypercubicEvenPlaquette H)
    (x : PeriodicHypercubicEvenSpecialUnitaryOpenHalfConfiguration H 2) :
    periodicHypercubicEvenBoundaryPlaquetteEnergyBoundedContinuousFunction H b p x =
      periodicHypercubicEvenBoundaryPlaquetteEnergyContinuousMap
        H 2 actualPlaquetteGeneratorReadoutTwoRankPositive b p x :=
  rfl

namespace PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}

/-- Generator-level actual positive-time realization datum.

For every shared boundary configuration and every actual finite plaquette, this
structure supplies one genuine observable in the already-existing physical
positive-time subalgebra and requires only the literal same-root pointwise
readout on `Q.interpolate n A`.

It does not assert that the coherent positive-half pullback is surjective or
multiplicative, and it does not choose a lift of the whole plaquette algebra.
Those algebraic consequences are theorem-generated from these elementary
readouts. -/
structure PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout
    (Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquetteGeneratorReadoutTwoRankPositive beta hbeta)
    (n : ℕ) where
  observable :
    PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration (halfExtent n) 2 →
      PeriodicHypercubicEvenPlaquette (halfExtent n) →
        D.positiveTimeSubalgebra
  positive : ∀ b p A,
    (((observable b p : D.positiveTimeSubalgebra) :
        physicalYangMillsGaugeInvariantObservableSubalgebra S) :
        BoundedContinuousFunction S.Configuration ℝ)
        (Q.interpolate n A) =
      periodicHypercubicEvenBoundaryPlaquetteEnergyBoundedContinuousFunction
        (halfExtent n) b p
        ((periodicHypercubicEvenEdgeOrbitPartition
          (halfExtent n)).positiveRestriction A)

namespace PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout

variable
    {Q : PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback
      S D halfExtent 2 actualPlaquetteGeneratorReadoutTwoRankPositive beta hbeta}
    {n : ℕ}

/-- Each concrete actual plaquette generator readout is, by definition, an
arbitrary-target positive-half cylinder readout of the type established in
#1670. -/
noncomputable def toPositiveHalfCylinderReadout
    (R : PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout Q n)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) 2)
    (p : PeriodicHypercubicEvenPlaquette (halfExtent n)) :
    PhysicalYangMillsWilsonSU2PositiveHalfCylinderReadout Q n
      (periodicHypercubicEvenBoundaryPlaquetteEnergyBoundedContinuousFunction
        (halfExtent n) b p) where
  observable := R.observable b p
  positive := R.positive b p

/-- Therefore every actual plaquette generator belongs to the readable physical
positive-half cylinder algebra. -/
theorem boundedGenerator_mem_positiveHalfCylinderReadableSubalgebra
    (R : PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout Q n)
    (b : PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration
      (halfExtent n) 2)
    (p : PeriodicHypercubicEvenPlaquette (halfExtent n)) :
    periodicHypercubicEvenBoundaryPlaquetteEnergyBoundedContinuousFunction
        (halfExtent n) b p ∈
      positiveHalfCylinderReadableSubalgebra Q n := by
  exact ⟨R.toPositiveHalfCylinderReadout b p⟩

end PhysicalYangMillsWilsonSU2ActualPlaquetteGeneratorReadout

end PhysicalYangMillsEvenPeriodicWilsonOSCoherentPositiveTimePullback

end

end MathlibAnalytic
end MGAP4D
