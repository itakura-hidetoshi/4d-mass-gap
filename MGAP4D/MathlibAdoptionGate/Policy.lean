namespace MGAP4D
namespace MathlibAdoptionGate

structure MathlibAdoptionPolicy where
  pass2ClosedRequired : Bool
  ciGreenRequired : Bool
  auditGreenRequired : Bool
  requesterMustBeRecorded : Bool
  importsMustBeScoped : Bool
  statusSurfacesPreserved : Bool
  publicBoundaryHeld : Bool
  deriving Repr, DecidableEq

def defaultPolicy : MathlibAdoptionPolicy := {
  pass2ClosedRequired := true,
  ciGreenRequired := true,
  auditGreenRequired := true,
  requesterMustBeRecorded := true,
  importsMustBeScoped := true,
  statusSurfacesPreserved := true,
  publicBoundaryHeld := true
}

theorem default_policy_pass2_required : defaultPolicy.pass2ClosedRequired = true := by
  rfl

end MathlibAdoptionGate
end MGAP4D
