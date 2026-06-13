import MGAP4D.MathlibAnalytic.Z2FiniteFourDimensionalHypercubicPlaquetteGeometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Negation of every Euclidean-time coordinate in a finite support. -/
def negateTimeSupport (times : List ℤ) : List ℤ :=
  times.map (fun t : ℤ => -t)

/-- Positivity of the reflected support is negativity of the original support. -/
theorem all_positive_negateTimeSupport_iff_all_negative
    (times : List ℤ) :
    (∀ t ∈ negateTimeSupport times, 0 < t) ↔
      ∀ t ∈ times, t < 0 := by
  simp [negateTimeSupport]

/-- Negativity of the reflected support is positivity of the original support. -/
theorem all_negative_negateTimeSupport_iff_all_positive
    (times : List ℤ) :
    (∀ t ∈ negateTimeSupport times, t < 0) ↔
      ∀ t ∈ times, 0 < t := by
  simp [negateTimeSupport]

/-- Time reflection exchanges the positive and negative sectors of every
nonempty support and preserves the crossing sector.  Nonemptiness is essential:
for the empty support both universal sign conditions hold vacuously. -/
@[simp]
theorem reflectionTimeSupportSide_negate
    (times : List ℤ) (hne : times ≠ []) :
    reflectionTimeSupportSide (negateTimeSupport times) =
      match reflectionTimeSupportSide times with
      | .positive => .negative
      | .crossing => .crossing
      | .negative => .positive := by
  classical
  have hPosRef := all_positive_negateTimeSupport_iff_all_negative times
  have hNegRef := all_negative_negateTimeSupport_iff_all_positive times
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil hne
  by_cases hp : ∀ t ∈ times, 0 < t
  · have hn : ¬ ∀ t ∈ times, t < 0 := by
      intro h
      exact (not_lt_of_ge (le_of_lt (hp a ha))) (h a ha)
    have hpRef : ¬ ∀ t ∈ negateTimeSupport times, 0 < t := by
      intro h
      exact hn (hPosRef.mp h)
    have hnRef : ∀ t ∈ negateTimeSupport times, t < 0 :=
      hNegRef.mpr hp
    simp [reflectionTimeSupportSide, hp, hn, hpRef, hnRef]
  · by_cases hn : ∀ t ∈ times, t < 0
    · have hpRef : ∀ t ∈ negateTimeSupport times, 0 < t :=
        hPosRef.mpr hn
      have hnRef : ¬ ∀ t ∈ negateTimeSupport times, t < 0 := by
        intro h
        exact hp (hNegRef.mp h)
      simp [reflectionTimeSupportSide, hp, hn, hpRef, hnRef]
    · have hpRef : ¬ ∀ t ∈ negateTimeSupport times, 0 < t := by
        intro h
        exact hn (hPosRef.mp h)
      have hnRef : ¬ ∀ t ∈ negateTimeSupport times, t < 0 := by
        intro h
        exact hp (hNegRef.mp h)
      simp [reflectionTimeSupportSide, hp, hn, hpRef, hnRef]

/-- The four-corner hypercubic time support is always nonempty. -/
@[simp]
theorem hypercubicPlaquetteTimes_ne_nil
    (t : ℤ) (μ ν : Fin 4) :
    hypercubicPlaquetteTimes t μ ν ≠ [] := by
  simp [hypercubicPlaquetteTimes]

/-- Reflection exchanges the side of any hypercubic plaquette once its reflected
corner-time list is identified with pointwise negation. -/
theorem hypercubicPlaquetteSide_of_reflected_times
    (t t' : ℤ) (μ ν : Fin 4)
    (hreflect :
      hypercubicPlaquetteTimes t' μ ν =
        negateTimeSupport (hypercubicPlaquetteTimes t μ ν)) :
    hypercubicPlaquetteSide t' μ ν =
      match hypercubicPlaquetteSide t μ ν with
      | .positive => .negative
      | .crossing => .crossing
      | .negative => .positive := by
  rw [hypercubicPlaquetteSide, hypercubicPlaquetteSide, hreflect]
  exact reflectionTimeSupportSide_negate
    (hypercubicPlaquetteTimes t μ ν)
    (hypercubicPlaquetteTimes_ne_nil t μ ν)

end

end MathlibAnalytic
end MGAP4D
