import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonianClosable

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Two strongly convergent graph sequences for the right generator with the
same base-space limit have the same operator-value limit.

This is the one-valuedness statement needed before defining the operator whose
graph is the closure of the canonical generator graph. -/
theorem rightGenerator_graph_limit_unique
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi phi : ℕ → T.rightGeneratorDomain}
    {x eta zeta : P.PhysicalHilbert}
    (hpsi : Tendsto (fun n => (psi n : P.PhysicalHilbert)) atTop (nhds x))
    (hphi : Tendsto (fun n => (phi n : P.PhysicalHilbert)) atTop (nhds x))
    (hgeneratorPsi :
      Tendsto (fun n => T.rightGenerator (psi n)) atTop (nhds eta))
    (hgeneratorPhi :
      Tendsto (fun n => T.rightGenerator (phi n)) atTop (nhds zeta)) :
    eta = zeta := by
  have hbaseDifference :
      Tendsto
        (fun n =>
          (((psi n - phi n : T.rightGeneratorDomain) :
            P.PhysicalHilbert)))
        atTop
        (nhds 0) := by
    simpa using hpsi.sub hphi
  have hvalueDifference :
      Tendsto
        (fun n => T.rightGenerator (psi n - phi n))
        atTop
        (nhds (eta - zeta)) := by
    simpa using hgeneratorPsi.sub hgeneratorPhi
  have hzero : eta - zeta = 0 :=
    T.rightGenerator_sequentially_closable
      hbaseDifference hvalueDifference
  exact sub_eq_zero.mp hzero

/-- Two strongly convergent graph sequences for the right Hamiltonian with the
same base-space limit have the same Hamiltonian-value limit. -/
theorem rightHamiltonian_graph_limit_unique
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi phi : ℕ → T.rightGeneratorDomain}
    {x eta zeta : P.PhysicalHilbert}
    (hpsi : Tendsto (fun n => (psi n : P.PhysicalHilbert)) atTop (nhds x))
    (hphi : Tendsto (fun n => (phi n : P.PhysicalHilbert)) atTop (nhds x))
    (hHamiltonianPsi :
      Tendsto (fun n => T.rightHamiltonian (psi n)) atTop (nhds eta))
    (hHamiltonianPhi :
      Tendsto (fun n => T.rightHamiltonian (phi n)) atTop (nhds zeta)) :
    eta = zeta := by
  have hbaseDifference :
      Tendsto
        (fun n =>
          (((psi n - phi n : T.rightGeneratorDomain) :
            P.PhysicalHilbert)))
        atTop
        (nhds 0) := by
    simpa using hpsi.sub hphi
  have hvalueDifference :
      Tendsto
        (fun n => T.rightHamiltonian (psi n - phi n))
        atTop
        (nhds (eta - zeta)) := by
    simpa using hHamiltonianPsi.sub hHamiltonianPhi
  have hzero : eta - zeta = 0 :=
    T.rightHamiltonian_sequentially_closable
      hbaseDifference hvalueDifference
  exact sub_eq_zero.mp hzero

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
