import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Typed positive-time observable data from which the physical Yang--Mills
Hilbert space is reconstructed.

The observable carrier is allowed to be only seminormed: OS reflection
positivity can give nonzero null vectors.  The physical space is therefore not
this carrier itself, but its separation quotient followed by Hilbert
completion.  The inner product is explicitly identified with the Euclidean
measure integral. -/
structure EuclideanYangMillsOSPositiveTimeObservableConstruction
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  PositiveTimeObservable : Type
  [observableSeminormedAddCommGroup :
    SeminormedAddCommGroup PositiveTimeObservable]
  [observableNormedSpace : NormedSpace ℝ PositiveTimeObservable]
  [observableInnerProductSpace : InnerProductSpace ℝ PositiveTimeObservable]
  realization : PositiveTimeObservable →ₗ[ℝ]
    (S.measurePackage.configurationSpace → ℝ)
  timeReflection :
    S.measurePackage.configurationSpace →
      S.measurePackage.configurationSpace
  positiveTimeSupported : PositiveTimeObservable → Prop
  positiveTimeSupported_proof : ∀ F, positiveTimeSupported F
  gaugeInvariant : PositiveTimeObservable → Prop
  gaugeInvariant_proof : ∀ F, gaugeInvariant F
  osProductIntegrable :
    ∀ F G,
      Integrable
        (fun ω => realization F (timeReflection ω) * realization G ω)
        S.measurePackage.euclideanMeasure
  osInner_eq_integral :
    ∀ F G,
      inner ℝ F G =
        ∫ ω,
          realization F (timeReflection ω) * realization G ω
          ∂S.measurePackage.euclideanMeasure
  vacuumObservable : PositiveTimeObservable
  vacuumRealization : ∀ ω, realization vacuumObservable ω = 1
  vacuumNorm : ‖vacuumObservable‖ = 1
  nontrivialObservable :
    ∃ F : PositiveTimeObservable, ‖F‖ ≠ 0

attribute [instance]
  EuclideanYangMillsOSPositiveTimeObservableConstruction.observableSeminormedAddCommGroup
  EuclideanYangMillsOSPositiveTimeObservableConstruction.observableNormedSpace
  EuclideanYangMillsOSPositiveTimeObservableConstruction.observableInnerProductSpace

/-- The OS null quotient.  Two positive-time observables are identified exactly
when the OS seminorm cannot separate them. -/
abbrev EuclideanYangMillsOSPositiveTimeObservableConstruction.OSSeparatedPreHilbert
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) : Type :=
  SeparationQuotient P.PositiveTimeObservable

/-- The physical real Yang--Mills Hilbert carrier.  It is kept opaque so the
low-level additive and module instances on `UniformSpace.Completion` cannot
compete with the single public Hilbert hierarchy installed below. -/
def EuclideanYangMillsOSPositiveTimeObservableConstruction.PhysicalHilbert
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) : Type :=
  UniformSpace.Completion P.OSSeparatedPreHilbert

/-- The exact canonical normed additive structure of the underlying Mathlib
completion, transported to the opaque physical carrier. -/
noncomputable instance os_physical_hilbert_normedAddCommGroup
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    NormedAddCommGroup P.PhysicalHilbert := by
  change NormedAddCommGroup
    (UniformSpace.Completion P.OSSeparatedPreHilbert)
  exact UniformSpace.Completion.instNormedAddCommGroup
    P.OSSeparatedPreHilbert

/-- The exact canonical real inner-product structure of the underlying Mathlib
completion, transported without invoking a second typeclass search. -/
noncomputable instance os_physical_hilbert_innerProductSpace
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    InnerProductSpace ℝ P.PhysicalHilbert := by
  change InnerProductSpace ℝ
    (UniformSpace.Completion P.OSSeparatedPreHilbert)
  exact UniformSpace.Completion.innerProductSpace

/-- The exact canonical completeness witness of the underlying Mathlib
completion, transported to the same public uniform structure. -/
noncomputable instance os_physical_hilbert_completeSpace
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    CompleteSpace P.PhysicalHilbert := by
  change CompleteSpace
    (UniformSpace.Completion P.OSSeparatedPreHilbert)
  exact UniformSpace.Completion.completeSpace P.OSSeparatedPreHilbert

/-- Canonical embedding of the separated OS quotient into the opaque physical
Hilbert carrier. -/
@[reducible] noncomputable instance os_preHilbert_coe_physical
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    Coe P.OSSeparatedPreHilbert P.PhysicalHilbert where
  coe x := by
    change UniformSpace.Completion P.OSSeparatedPreHilbert
    exact (x : UniformSpace.Completion P.OSSeparatedPreHilbert)

/-- Quotient class of a positive-time observable before completion. -/
def EuclideanYangMillsOSPositiveTimeObservableConstruction.osClass
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F : P.PositiveTimeObservable) : P.OSSeparatedPreHilbert :=
  SeparationQuotient.mk F

/-- Dense physical state represented by a positive-time Euclidean observable. -/
def EuclideanYangMillsOSPositiveTimeObservableConstruction.physicalState
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F : P.PositiveTimeObservable) : P.PhysicalHilbert :=
  (P.osClass F : P.PhysicalHilbert)

/-- The physical vacuum is the completed OS class of the constant observable. -/
def EuclideanYangMillsOSPositiveTimeObservableConstruction.vacuum
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    P.PhysicalHilbert :=
  P.physicalState P.vacuumObservable

/-- The separated quotient carries its canonical real inner-product structure. -/
@[implicit_reducible] noncomputable def os_separated_preHilbert_innerProductSpace
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    InnerProductSpace ℝ P.OSSeparatedPreHilbert := by
  infer_instance

/-- The completed OS physical carrier is complete. -/
theorem os_physical_hilbert_complete
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    CompleteSpace P.PhysicalHilbert := by
  infer_instance

/-- The OS pre-Hilbert quotient sits densely in the completed physical Hilbert
space. -/
theorem os_preHilbert_dense_in_physical
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    DenseRange
      (fun x : P.OSSeparatedPreHilbert => (x : P.PhysicalHilbert)) := by
  change DenseRange
    (fun x : P.OSSeparatedPreHilbert =>
      (x : UniformSpace.Completion P.OSSeparatedPreHilbert))
  exact UniformSpace.Completion.denseRange_coe

/-- The displayed inner product on positive-time observables is genuinely the
Osterwalder--Schrader reflected Euclidean expectation. -/
theorem os_positive_time_inner_eq_euclidean_integral
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    (F G : P.PositiveTimeObservable) :
    inner ℝ F G =
      ∫ ω,
        P.realization F (P.timeReflection ω) * P.realization G ω
        ∂S.measurePackage.euclideanMeasure :=
  P.osInner_eq_integral F G

/-- Observables inseparable in the OS seminorm define the same physical state. -/
theorem os_inseparable_observables_same_physical_state
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S)
    {F G : P.PositiveTimeObservable}
    (hFG : Inseparable F G) :
    P.physicalState F = P.physicalState G := by
  have hQuotient : P.osClass F = P.osClass G :=
    SeparationQuotient.mk_eq_mk.mpr hFG
  exact congrArg (fun x : P.OSSeparatedPreHilbert =>
    (x : P.PhysicalHilbert)) hQuotient

/-- The construction records the intended physical chain in one theorem-level
package: measure-defined OS inner product, null quotient, dense embedding and
Hilbert completion. -/
structure EuclideanYangMillsOSPhysicalHilbertCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) where
  preHilbertInner : InnerProductSpace ℝ P.OSSeparatedPreHilbert
  physicalInner : InnerProductSpace ℝ P.PhysicalHilbert
  physicalComplete : CompleteSpace P.PhysicalHilbert
  preHilbertDense : DenseRange
    (fun x : P.OSSeparatedPreHilbert => (x : P.PhysicalHilbert))
  vacuumState : P.PhysicalHilbert
  vacuumState_eq : vacuumState = P.vacuum

/-- Construct the physical-Hilbert certificate directly from the OS observable
construction. -/
def euclideanYangMillsOSPhysicalHilbertCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (P : EuclideanYangMillsOSPositiveTimeObservableConstruction S) :
    EuclideanYangMillsOSPhysicalHilbertCertificate P :=
  { preHilbertInner := os_separated_preHilbert_innerProductSpace P
    physicalInner := inferInstance
    physicalComplete := os_physical_hilbert_complete P
    preHilbertDense := os_preHilbert_dense_in_physical P
    vacuumState := P.vacuum
    vacuumState_eq := rfl }

end

end MathlibAnalytic
end MGAP4D
