namespace MGAP4D
namespace Certificates

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

end Certificates
end MGAP4D
