import MGAP4D.Certificates.Born
import MGAP4D.Certificates.ClassicalLimit
import MGAP4D.Certificates.RGScaleBridge
import MGAP4D.Certificates.EmpiricalID

namespace MGAP4D
namespace Certificates

structure CertificatePacket where
  born : BornCert
  classicalLimit : ClassicalLimitCert
  rgScaleBridge : RGScaleBridgeCert
  empiricalID : EmpiricalIDCert
  deriving Repr

def pendingCertificatePacket : CertificatePacket :=
  { born := bornCertPending,
    classicalLimit := classicalLimitCertPending,
    rgScaleBridge := rgScaleBridgeCertPending,
    empiricalID := empiricalIDCertPending }

end Certificates
end MGAP4D
