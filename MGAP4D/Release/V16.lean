import MGAP4D.Audit
import MGAP4D.Constructive.FinalTheorem

namespace MGAP4D
namespace Release

/-- Lean-side release packet for the MGAP4D v1.6 migration mirror. -/
structure V16ReleasePacket where
  version : String
  packageSha256 : String
  counts : Audit.ReleaseCounts
  noForbiddenTokens : Audit.NoForbiddenTokens
  finalPacket : Constructive.FinalTheoremPacket

/-- The v1.6 release packet recorded in the GitHub mirror. -/
def v16ReleasePacket : V16ReleasePacket :=
  { version := "v1.6",
    packageSha256 := "afc2c81f3f9b20a2bf92e93fb9417ab53f0a7e46a6769eb68be8d14407c69ab0",
    counts := Audit.v16ReleaseCounts,
    noForbiddenTokens := Audit.v16NoForbiddenTokens,
    finalPacket := Constructive.finalTheoremPacket3320 }

theorem v16_release_gap3320 : v16ReleasePacket.finalPacket.massGap.value = 33 / 20 := by
  rfl

theorem v16_release_no_sorry : v16ReleasePacket.counts.sorryCount = 0 := by
  rfl

end Release
end MGAP4D
