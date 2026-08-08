import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkConditional

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem compact_oriented_replaceLink_right_of_agreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (source : L.geometry.Edge)
    (hAgree : L.AgreeOffLink A B source) :
    L.replaceLink A source (B source) = B := by
  funext e
  by_cases h : e = source
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, h, hAgree e h]

end
end MathlibAnalytic
end MGAP4D
