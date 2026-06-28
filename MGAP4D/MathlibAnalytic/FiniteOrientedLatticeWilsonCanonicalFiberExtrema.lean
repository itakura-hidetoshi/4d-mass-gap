import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinVariationProfile
import Mathlib.Data.Finset.Max

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableValues
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : Finset ℝ :=
  Finset.univ.image (fun g : L.Gauge => f (L.replaceLink A e g))

theorem finite_oriented_fiberObservableValues_nonempty
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    (L.fiberObservableValues f A e).Nonempty := by
  classical
  refine ⟨f (L.replaceLink A e default), ?_⟩
  simp [FiniteOrientedLatticeWilsonSystem.fiberObservableValues]

noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableMax
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableValues f A e).max'
    (finite_oriented_fiberObservableValues_nonempty L f A e)

noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableMin
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableValues f A e).min'
    (finite_oriented_fiberObservableValues_nonempty L f A e)

theorem finite_oriented_fiberObservableValue_le_max
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    f (L.replaceLink A e g) ≤ L.fiberObservableMax f A e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMax
  apply Finset.le_max'
  simp [FiniteOrientedLatticeWilsonSystem.fiberObservableValues]

theorem finite_oriented_fiberObservableMin_le_value
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    L.fiberObservableMin f A e ≤ f (L.replaceLink A e g) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMin
  apply Finset.min'_le
  simp [FiniteOrientedLatticeWilsonSystem.fiberObservableValues]

noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableRange
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  L.fiberObservableMax f A e - L.fiberObservableMin f A e

theorem finite_oriented_fiberObservableRange_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) :
    0 ≤ L.fiberObservableRange f A e := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableRange
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMax
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableMin
  exact sub_nonneg.mpr
    (Finset.min'_le_max'
      (L.fiberObservableValues f A e)
      (finite_oriented_fiberObservableValues_nonempty L f A e))

noncomputable def FiniteOrientedLatticeWilsonSystem.fiberObservableCenter
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge) : ℝ :=
  (L.fiberObservableMin f A e + L.fiberObservableMax f A e) / 2

theorem finite_oriented_fiberObservable_abs_sub_center_le_half_range
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    |f (L.replaceLink A e g) - L.fiberObservableCenter f A e| ≤
      L.fiberObservableRange f A e / 2 := by
  have hMin := finite_oriented_fiberObservableMin_le_value L f A e g
  have hMax := finite_oriented_fiberObservableValue_le_max L f A e g
  rw [abs_le]
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableCenter
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableRange
  constructor <;> linarith

theorem finite_oriented_fiberObservable_difference_abs_le_range
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g h : L.Gauge) :
    |f (L.replaceLink A e g) - f (L.replaceLink A e h)| ≤
      L.fiberObservableRange f A e := by
  have hgMin := finite_oriented_fiberObservableMin_le_value L f A e g
  have hgMax := finite_oriented_fiberObservableValue_le_max L f A e g
  have hhMin := finite_oriented_fiberObservableMin_le_value L f A e h
  have hhMax := finite_oriented_fiberObservableValue_le_max L f A e h
  rw [abs_le]
  unfold FiniteOrientedLatticeWilsonSystem.fiberObservableRange
  constructor <;> linarith

end
end MathlibAnalytic
end MGAP4D
