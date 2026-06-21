import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeReflection

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Site reflection of a physical positive-link configuration.

Spatial links remain positively oriented after reflection.  A positive time
link is reflected to a negatively traversed positive-link representative, so
its group value is inverted. -/
def periodicHypercubicEvenConfigurationReflection
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    PeriodicHypercubicEvenEdge H → Gauge :=
  fun e =>
    if e.2 = 0 then
      (A (periodicHypercubicEvenEdgeReflection H e))⁻¹
    else
      A (periodicHypercubicEvenEdgeReflection H e)

/-- Reflection of a positive time link reverses its traversal. -/
@[simp]
theorem periodicHypercubicEvenConfigurationReflection_time
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenConfigurationReflection H A (v, 0) =
      (A (periodicHypercubicEvenEdgeReflection H (v, 0)))⁻¹ := by
  simp [periodicHypercubicEvenConfigurationReflection]

/-- Reflection of a spatial positive link preserves its traversal direction. -/
@[simp]
theorem periodicHypercubicEvenConfigurationReflection_spatial
    {Gauge : Type*} [Group Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0) :
    periodicHypercubicEvenConfigurationReflection H A e =
      A (periodicHypercubicEvenEdgeReflection H e) := by
  simp [periodicHypercubicEvenConfigurationReflection, hspace]

/-- The reflected physical-link configuration operation is involutive. -/
theorem periodicHypercubicEvenConfigurationReflection_involutive
    {Gauge : Type*} [Group Gauge]
    (H : ℕ) :
    Function.Involutive
      (periodicHypercubicEvenConfigurationReflection (Gauge := Gauge) H) := by
  intro A
  funext e
  simp only [periodicHypercubicEvenConfigurationReflection]
  by_cases htime : e.2 = 0
  · have htime' : (periodicHypercubicEvenEdgeReflection H e).2 = 0 := by
      simpa using htime
    rw [if_pos htime, if_pos htime', inv_inv,
      periodicHypercubicEvenEdgeReflection_involutive H e]
  · have htime' : (periodicHypercubicEvenEdgeReflection H e).2 ≠ 0 := by
      simpa using htime
    rw [if_neg htime, if_neg htime',
      periodicHypercubicEvenEdgeReflection_involutive H e]

end

end MathlibAnalytic
end MGAP4D
