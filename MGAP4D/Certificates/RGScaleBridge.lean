import MGAP4D.Certificates.Core

namespace MGAP4D
namespace Certificates

structure RGScaleBridgeCert where
  cert : Certificate
  deriving Repr

def rgScaleBridgeCertPending : RGScaleBridgeCert :=
  { cert := { id := "RGScaleBridgeCert", status := CertStatus.pending, statement := "RG scale bridge certificate placeholder" } }

end Certificates
end MGAP4D
