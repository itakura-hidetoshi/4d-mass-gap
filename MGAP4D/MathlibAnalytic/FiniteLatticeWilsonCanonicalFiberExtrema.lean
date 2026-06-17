import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonDobrushinVariationProfile
import Mathlib.Data.Finset.Max

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite set of observable values on the single-link fiber through `A`
at the link `e`. -/
noncomputable def FiniteLatticeWilsonSystem.fiberObservableValues
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : Finset ℝ :=
  Finset.univ.image (fun g : L.Gauge => f (L.replaceLink A e g))

/-- Every single-link fiber value set is nonempty because the finite gauge
group is inhabited. -/
theorem finite_lattice_fiberObservableValues_nonempty
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    (L.fiberObservableValues f A e).Nonempty := by
  classical
  refine ⟨f (L.replaceLink A e default), ?_⟩
  simp [FiniteLatticeWilsonSystem.fiberObservableValues]

/-- Maximum observable value on a finite single-link fiber. -/
noncomputable def FiniteLatticeWilsonSystem.fiberObservableMax
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableValues f A e).max'
    (finite_lattice_fiberObservableValues_nonempty L f A e)

/-- Minimum observable value on a finite single-link fiber. -/
noncomputable def FiniteLatticeWilsonSystem.fiberObservableMin
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableValues f A e).min'
    (finite_lattice_fiberObservableValues_nonempty L f A e)

/-- Every fiber value lies below the canonical fiber maximum. -/
theorem finite_lattice_fiberObservableValue_le_max
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    f (L.replaceLink A e g) ≤ L.fiberObservableMax f A e := by
  classical
  unfold FiniteLatticeWilsonSystem.fiberObservableMax
  apply Finset.le_max'
  simp [FiniteLatticeWilsonSystem.fiberObservableValues]

/-- The canonical fiber minimum lies below every fiber value. -/
theorem finite_lattice_fiberObservableMin_le_value
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    L.fiberObservableMin f A e ≤ f (L.replaceLink A e g) := by
  classical
  unfold FiniteLatticeWilsonSystem.fiberObservableMin
  apply Finset.min'_le
  simp [FiniteLatticeWilsonSystem.fiberObservableValues]

/-- The exact range of the observable on one finite single-link fiber. -/
noncomputable def FiniteLatticeWilsonSystem.fiberObservableRange
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  L.fiberObservableMax f A e - L.fiberObservableMin f A e

/-- The finite fiber range is nonnegative. -/
theorem finite_lattice_fiberObservableRange_nonneg
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    0 ≤ L.fiberObservableRange f A e := by
  classical
  unfold FiniteLatticeWilsonSystem.fiberObservableRange
  unfold FiniteLatticeWilsonSystem.fiberObservableMax
  unfold FiniteLatticeWilsonSystem.fiberObservableMin
  exact sub_nonneg.mpr
    (Finset.min'_le_max'
      (L.fiberObservableValues f A e)
      (finite_lattice_fiberObservableValues_nonempty L f A e))

/-- The midpoint of the minimum and maximum observable values on a fiber. -/
noncomputable def FiniteLatticeWilsonSystem.fiberObservableCenter
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableMin f A e + L.fiberObservableMax f A e) / 2

/-- Every fiber value lies within half the exact fiber range of the canonical
midpoint. -/
theorem finite_lattice_fiberObservable_abs_sub_center_le_half_range
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
      L.fiberObservableRange f A e / 2 := by
  have hMin := finite_lattice_fiberObservableMin_le_value L f A e g
  have hMax := finite_lattice_fiberObservableValue_le_max L f A e g
  rw [abs_le]
  unfold FiniteLatticeWilsonSystem.fiberObservableCenter
  unfold FiniteLatticeWilsonSystem.fiberObservableRange
  constructor <;> linarith

/-- The difference of any two values on the same fiber is bounded by the exact
fiber range. -/
theorem finite_lattice_fiberObservable_difference_abs_le_range
    (L : FiniteLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g h : L.Gauge) :
    |f (L.replaceLink A e g) - f (L.replaceLink A e h)| ≤
      L.fiberObservableRange f A e := by
  have hgMin := finite_lattice_fiberObservableMin_le_value L f A e g
  have hgMax := finite_lattice_fiberObservableValue_le_max L f A e g
  have hhMin := finite_lattice_fiberObservableMin_le_value L f A e h
  have hhMax := finite_lattice_fiberObservableValue_le_max L f A e h
  rw [abs_le]
  unfold FiniteLatticeWilsonSystem.fiberObservableRange
  constructor <;> linarith

end

end MathlibAnalytic
end MGAP4D
