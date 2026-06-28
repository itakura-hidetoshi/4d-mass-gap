import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Replace one physical positive-link variable in a compact oriented Wilson
configuration. -/
def CompactOrientedGaugeWilsonSystem.replaceLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g : L.Gauge) : L.Configuration := by
  classical
  exact fun e => if e = target then g else A e

@[simp] theorem compact_oriented_replaceLink_same
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g : L.Gauge) :
    L.replaceLink A target g target = g := by
  simp [CompactOrientedGaugeWilsonSystem.replaceLink]

@[simp] theorem compact_oriented_replaceLink_other
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target e : L.geometry.Edge)
    (g : L.Gauge)
    (h : e ≠ target) :
    L.replaceLink A target g e = A e := by
  simp [CompactOrientedGaugeWilsonSystem.replaceLink, h]

@[simp] theorem compact_oriented_replaceLink_current
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge) :
    L.replaceLink A target (A target) = A := by
  funext e
  by_cases h : e = target
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, h]

@[simp] theorem compact_oriented_replaceLink_replaceLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration)
    (target : L.geometry.Edge)
    (g h : L.Gauge) :
    L.replaceLink (L.replaceLink A target g) target h =
      L.replaceLink A target h := by
  funext e
  by_cases he : e = target
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, he]

/-- Two compact oriented configurations agree away from one physical link. -/
def CompactOrientedGaugeWilsonSystem.AgreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target : L.geometry.Edge) : Prop :=
  ∀ e, e ≠ target → A e = B e

/-- Link replacement depends only on the off-link fiber and the inserted
value. -/
theorem compact_oriented_replaceLink_eq_of_agreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target : L.geometry.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B target) :
    L.replaceLink A target g = L.replaceLink B target g := by
  funext e
  by_cases h : e = target
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, h,
      hAgree e h]

/-- Replacing the missing link of an off-link fiber by the second
configuration's value recovers that configuration. -/
theorem compact_oriented_replaceLink_right_of_agreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target : L.geometry.Edge)
    (hAgree : L.AgreeOffLink A B target) :
    L.replaceLink A target (B target) = B := by
  calc
    L.replaceLink A target (B target) =
        L.replaceLink B target (B target) :=
      compact_oriented_replaceLink_eq_of_agreeOffLink
        L A B target (B target) hAgree
    _ = B := compact_oriented_replaceLink_current L B target

end

end MathlibAnalytic
end MGAP4D
