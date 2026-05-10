import MGAP4D.Certificates.Core

namespace MGAP4D
namespace Certificates

structure EmpiricalIDCert where
  cert : Certificate
  deriving Repr

def empiricalIDCertPending : EmpiricalIDCert :=
  { cert := { id := "EmpiricalIDCert", status := CertStatus.pending, statement := "Empirical identification certificate placeholder" } }

end Certificates
end MGAP4D
