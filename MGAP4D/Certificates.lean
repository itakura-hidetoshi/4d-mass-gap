namespace MGAP4D

/-!
# MGAP4D Certificates

Certificate objects record which proof obligations are external, imported,
formalized, or still pending. They are intentionally lightweight at the start of
migration and can be tightened additively.
-/

inductive CertStatus where
  | formalized
  | imported
  | external
  | pending
  deriving Repr, DecidableEq

structure Certificate where
  id : String
  status : CertStatus
  statement : String
  deriving Repr

end MGAP4D
