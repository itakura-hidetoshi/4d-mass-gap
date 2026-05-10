import MGAP4D.Certificates.Core

namespace MGAP4D
namespace Certificates

structure BornCert where
  cert : Certificate
  deriving Repr

def bornCertPending : BornCert :=
  { cert := { id := "BornCert", status := CertStatus.pending, statement := "Born rule bridge certificate placeholder" } }

end Certificates
end MGAP4D
