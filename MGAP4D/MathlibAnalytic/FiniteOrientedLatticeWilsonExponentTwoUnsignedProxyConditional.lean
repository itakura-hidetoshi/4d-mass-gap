import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonExponentTwoUnsignedProxyAction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Legacy and oriented one-link replacement agree on the shared carrier. -/
theorem finite_oriented_unsignedProxy_replaceLink_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    L.unsignedProxy.replaceLink A e g = L.replaceLink A e g := by
  classical
  funext e'
  change Function.update A e g e' =
    (if e' = e then g else A e')
  by_cases h : e' = e <;> simp [h]

/-- Proxy and oriented off-link agreement predicates coincide. -/
theorem finite_oriented_unsignedProxy_agreeOffLink_iff
    (L : FiniteOrientedLatticeWilsonSystem)
    (A B : L.Configuration)
    (e : L.Edge) :
    L.unsignedProxy.AgreeOffLink A B e ↔
      L.AgreeOffLink A B e := by
  rfl

/-- For exponent-two groups, proxy and oriented one-link Boltzmann weights
coincide. -/
theorem finite_oriented_unsignedProxy_singleLinkBoltzmannWeight_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (A : L.Configuration)
    (e : L.Edge)
    (g : L.Gauge) :
    L.unsignedProxy.singleLinkBoltzmannWeight A e g =
      L.singleLinkBoltzmannWeight A e g := by
  change ENNReal.ofReal
      (Real.exp (-L.beta *
        L.unsignedProxy.wilsonAction
          (L.unsignedProxy.replaceLink A e g))) =
    ENNReal.ofReal
      (Real.exp (-L.beta *
        L.wilsonAction (L.replaceLink A e g)))
  rw [finite_oriented_unsignedProxy_replaceLink_eq,
    finite_oriented_unsignedProxy_wilsonAction_eq L hInv]

/-- Proxy and oriented one-link partition functions coincide. -/
theorem finite_oriented_unsignedProxy_singleLinkPartitionFunction_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (A : L.Configuration)
    (e : L.Edge) :
    L.unsignedProxy.singleLinkPartitionFunction A e =
      L.singleLinkPartitionFunction A e := by
  unfold FiniteLatticeWilsonSystem.singleLinkPartitionFunction
    FiniteOrientedLatticeWilsonSystem.singleLinkPartitionFunction
  apply tsum_congr
  intro g
  exact finite_oriented_unsignedProxy_singleLinkBoltzmannWeight_eq
    L hInv A e g

/-- Proxy and oriented one-link conditional probability laws coincide. -/
theorem finite_oriented_unsignedProxy_singleLinkConditionalPMF_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (A : L.Configuration)
    (e : L.Edge) :
    L.unsignedProxy.singleLinkConditionalPMF A e =
      L.singleLinkConditionalPMF A e := by
  ext g
  change
    L.unsignedProxy.singleLinkBoltzmannWeight A e g *
        (L.unsignedProxy.singleLinkPartitionFunction A e)⁻¹ =
      L.singleLinkBoltzmannWeight A e g *
        (L.singleLinkPartitionFunction A e)⁻¹
  rw [finite_oriented_unsignedProxy_singleLinkBoltzmannWeight_eq
      L hInv A e g,
    finite_oriented_unsignedProxy_singleLinkPartitionFunction_eq
      L hInv A e]

/-- Proxy and oriented conditional total variation coincide. -/
theorem finite_oriented_unsignedProxy_singleLinkConditionalTotalVariation_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hInv : ∀ g : L.Gauge, g⁻¹ = g)
    (A B : L.Configuration)
    (e : L.Edge) :
    L.unsignedProxy.singleLinkConditionalTotalVariation A B e =
      L.singleLinkConditionalTotalVariation A B e := by
  classical
  have hA :=
    finite_oriented_unsignedProxy_singleLinkConditionalPMF_eq
      L hInv A e
  have hB :=
    finite_oriented_unsignedProxy_singleLinkConditionalPMF_eq
      L hInv B e
  change
    (2 : ℝ)⁻¹ *
        ∑ g : L.Gauge,
          |(L.unsignedProxy.singleLinkConditionalPMF A e g).toReal -
            (L.unsignedProxy.singleLinkConditionalPMF B e g).toReal| =
      (2 : ℝ)⁻¹ *
        ∑ g : L.Gauge,
          |(L.singleLinkConditionalPMF A e g).toReal -
            (L.singleLinkConditionalPMF B e g).toReal|
  rw [hA, hB]

end

end MathlibAnalytic
end MGAP4D