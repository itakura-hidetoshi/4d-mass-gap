import MGAP4D.MathlibAnalytic.NormalizedCompactHaarInversion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import Mathlib.MeasureTheory.Constructions.Pi

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Edge reflection as a finite index equivalence. -/
def periodicHypercubicEvenEdgeReflectionEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenEdge H ≃ PeriodicHypercubicEvenEdge H :=
  (periodicHypercubicEvenEdgeReflection_involutive H).toPerm

@[simp]
theorem periodicHypercubicEvenEdgeReflectionEquiv_apply
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenEdgeReflectionEquiv H e =
      periodicHypercubicEvenEdgeReflection H e :=
  rfl

/-- Measurable reindexing of configurations by reflected physical links. -/
noncomputable def periodicHypercubicEvenConfigurationReindexMeasurableEquiv
    (H : ℕ) (Value : Type) [MeasurableSpace Value] :
    (PeriodicHypercubicEvenEdge H → Value) ≃ᵐ
      (PeriodicHypercubicEvenEdge H → Value) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : PeriodicHypercubicEvenEdge H => Value)
    (periodicHypercubicEvenEdgeReflectionEquiv H)

/-- Pointwise orientation correction after reflected-edge reindexing. -/
def periodicHypercubicEvenConfigurationOrientationCorrection
    {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    PeriodicHypercubicEvenEdge H → Gauge :=
  fun e => if e.2 = 0 then (A e)⁻¹ else A e

end

end MathlibAnalytic
end MGAP4D
