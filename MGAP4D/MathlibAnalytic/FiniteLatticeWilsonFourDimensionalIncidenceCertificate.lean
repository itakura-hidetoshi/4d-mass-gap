import MGAP4D.MathlibAnalytic.FiniteLatticeWilsonSharedPlaquetteEnergyGap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A pointwise upper bound on all active plaquette-neighborhood cardinalities
bounds the exact canonical active degree by the same number. -/
theorem finite_lattice_canonicalActivePlaquetteDegree_le_of_forall_card_le
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (degreeBound : ℕ)
    (hCard : ∀ target : L.Edge,
      (L.activePlaquetteNeighbors target).card ≤ degreeBound) :
    L.canonicalActivePlaquetteDegree hEdge ≤ degreeBound := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActivePlaquetteDegree
  apply Finset.max'_le
  intro n hn
  unfold FiniteLatticeWilsonSystem.activePlaquetteNeighborCardValues at hn
  rcases Finset.mem_image.mp hn with ⟨target, _hTarget, rfl⟩
  exact hCard target

/-- A pointwise upper bound on the number of plaquettes shared by every active
edge pair bounds the exact canonical active shared multiplicity. -/
theorem
    finite_lattice_canonicalActiveSharedPlaquetteMultiplicity_le_of_forall_card_le
    (L : FiniteLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (multiplicityBound : ℕ)
    (hShared : ∀ (target source : L.Edge),
      source ∈ L.activePlaquetteNeighbors target →
        (L.sharedPlaquettes target source).card ≤ multiplicityBound) :
    L.canonicalActiveSharedPlaquetteMultiplicity hEdge ≤ multiplicityBound := by
  classical
  unfold FiniteLatticeWilsonSystem.canonicalActiveSharedPlaquetteMultiplicity
  apply Finset.max'_le
  intro n hn
  unfold FiniteLatticeWilsonSystem.activeSharedPlaquetteCardValues at hn
  rcases Finset.mem_image.mp hn with ⟨pair, _hPair, rfl⟩
  by_cases hActive : pair.2 ∈ L.activePlaquetteNeighbors pair.1
  · simp only [if_pos hActive]
    exact hShared pair.1 pair.2 hActive
  · simp [hActive]

/-- Incidence certificate for the standard four-dimensional hypercubic Wilson
geometry: at most eighteen active links around a target link and at most one
oriented plaquette shared by an active ordered edge pair.

The certificate separates the finite combinatorial geometry from the analytic
Wilson/Dobrushin/Hamiltonian spine. A concrete periodic torus construction only
has to provide these two incidence facts. -/
structure FiniteLatticeWilsonFourDimensionalIncidenceCertificate
    (L : FiniteLatticeWilsonSystem) where
  edgeCard_pos : 0 < Fintype.card L.Edge
  activeDegree_pos :
    0 < L.canonicalActivePlaquetteDegree edgeCard_pos
  activeNeighborCard_le_eighteen : ∀ target : L.Edge,
    (L.activePlaquetteNeighbors target).card ≤ 18
  activeSharedPlaquetteCard_le_one : ∀ (target source : L.Edge),
    source ∈ L.activePlaquetteNeighbors target →
      (L.sharedPlaquettes target source).card ≤ 1

/-- The exact active degree of a certified four-dimensional incidence geometry
is at most eighteen. -/
theorem
    FiniteLatticeWilsonFourDimensionalIncidenceCertificate.canonicalActivePlaquetteDegree_le_eighteen
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonFourDimensionalIncidenceCertificate L) :
    L.canonicalActivePlaquetteDegree D.edgeCard_pos ≤ 18 :=
  finite_lattice_canonicalActivePlaquetteDegree_le_of_forall_card_le
    L D.edgeCard_pos 18 D.activeNeighborCard_le_eighteen

/-- The exact active shared-plaquette multiplicity of a certified
four-dimensional incidence geometry is at most one. -/
theorem
    FiniteLatticeWilsonFourDimensionalIncidenceCertificate.canonicalActiveSharedPlaquetteMultiplicity_le_one
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonFourDimensionalIncidenceCertificate L) :
    L.canonicalActiveSharedPlaquetteMultiplicity D.edgeCard_pos ≤ 1 :=
  finite_lattice_canonicalActiveSharedPlaquetteMultiplicity_le_of_forall_card_le
    L D.edgeCard_pos 1 D.activeSharedPlaquetteCard_le_one

/-- In a certified four-dimensional incidence geometry, every active source
perturbation changes the target-local action by at most one plaquette-energy
maximum in absolute value. -/
theorem
    FiniteLatticeWilsonFourDimensionalIncidenceCertificate.activeLocalActionDifference_abs_le_energyMax
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonFourDimensionalIncidenceCertificate L)
    (target source : L.Edge)
    (A : L.Configuration)
    (g u : L.Gauge)
    (hActive : source ∈ L.activePlaquetteNeighbors target) :
    |L.targetLocalPlaquetteAction (L.replaceLink A target u) target -
        L.targetLocalPlaquetteAction
          (L.replaceLink (L.replaceLink A source g) target u) target| ≤
      L.plaquetteEnergyMax := by
  have hRaw :=
    finite_lattice_targetLocalAction_sub_sourceReplace_abs_le_sharedCard_mul_energyMax
      L A target source u g
  have hCardNat := D.activeSharedPlaquetteCard_le_one target source hActive
  have hCard :
      ((L.sharedPlaquettes target source).card : ℝ) ≤ 1 := by
    exact_mod_cast hCardNat
  have hScaleRaw :=
    mul_le_mul_of_nonneg_right hCard
      (finite_lattice_plaquetteEnergyMax_nonneg L)
  have hScale :
      ((L.sharedPlaquettes target source).card : ℝ) *
          L.plaquetteEnergyMax ≤
        L.plaquetteEnergyMax := by
    simpa using hScaleRaw
  exact le_trans hRaw hScale

/-- The local action-difference oscillation radius of a certified
four-dimensional incidence geometry is at most `2 * E_max`. -/
theorem
    FiniteLatticeWilsonFourDimensionalIncidenceCertificate.activeLocalActionDifferenceOscillationBound_two_mul_energyMax
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonFourDimensionalIncidenceCertificate L) :
    L.ActiveLocalActionDifferenceOscillationBound
      (2 * L.plaquetteEnergyMax) := by
  intro target source A g hActive u v
  have hu := abs_le.mp
    (D.activeLocalActionDifference_abs_le_energyMax
      target source A g u hActive)
  have hv := abs_le.mp
    (D.activeLocalActionDifference_abs_le_energyMax
      target source A g v hActive)
  linarith

/-- The certified four-dimensional incidence geometry gives the explicit
single-link conditional likelihood-ratio radius `beta * (2 * E_max)`. -/
theorem
    FiniteLatticeWilsonFourDimensionalIncidenceCertificate.activeConditionalExpRatioBound_two_mul_energyMax
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonFourDimensionalIncidenceCertificate L) :
    L.ActiveConditionalExpRatioBound
      (L.beta * (2 * L.plaquetteEnergyMax)) :=
  finite_lattice_activeConditionalExpRatioBound_of_localActionOscillation
    L (2 * L.plaquetteEnergyMax)
      (mul_nonneg (by norm_num)
        (finite_lattice_plaquetteEnergyMax_nonneg L))
      D.activeLocalActionDifferenceOscillationBound_two_mul_energyMax

/-- The exact active influence maximum is bounded by the explicit
four-dimensional one-plaquette normalized-exponential majorant. -/
theorem
    FiniteLatticeWilsonFourDimensionalIncidenceCertificate.canonicalActivePlaquetteInfluenceBound_le_two_mul_energyMaxExpRatio
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonFourDimensionalIncidenceCertificate L) :
    L.canonicalActivePlaquetteInfluenceBound D.edgeCard_pos ≤
      (Real.exp (L.beta * (2 * L.plaquetteEnergyMax)) - 1) /
        (Real.exp (L.beta * (2 * L.plaquetteEnergyMax)) + 1) :=
  finite_lattice_canonicalActivePlaquetteInfluenceBound_le_expRatioBound
    L D.edgeCard_pos
      (L.beta * (2 * L.plaquetteEnergyMax))
      (mul_nonneg L.beta_nonneg
        (mul_nonneg (by norm_num)
          (finite_lattice_plaquetteEnergyMax_nonneg L)))
      D.activeConditionalExpRatioBound_two_mul_energyMax

/-- The explicit scalar inequality `TV_majorant < 1/18` is sufficient for
strict canonical Dobrushin contraction in a certified four-dimensional
hypercubic incidence geometry. -/
theorem
    FiniteLatticeWilsonFourDimensionalIncidenceCertificate.canonicalDobrushinCoefficient_lt_one
    {L : FiniteLatticeWilsonSystem}
    (D : FiniteLatticeWilsonFourDimensionalIncidenceCertificate L)
    (hThreshold :
      (Real.exp (L.beta * (2 * L.plaquetteEnergyMax)) - 1) /
          (Real.exp (L.beta * (2 * L.plaquetteEnergyMax)) + 1) <
        (18 : ℝ)⁻¹) :
    L.canonicalDobrushinCoefficient D.edgeCard_pos < 1 := by
  let q : ℝ :=
    (Real.exp (L.beta * (2 * L.plaquetteEnergyMax)) - 1) /
      (Real.exp (L.beta * (2 * L.plaquetteEnergyMax)) + 1)
  have hRadiusNonneg :
      0 ≤ L.beta * (2 * L.plaquetteEnergyMax) :=
    mul_nonneg L.beta_nonneg
      (mul_nonneg (by norm_num)
        (finite_lattice_plaquetteEnergyMax_nonneg L))
  have hQNonneg : 0 ≤ q := by
    exact expLikelihoodRatioTotalVariationBound_nonneg
      (L.beta * (2 * L.plaquetteEnergyMax)) hRadiusNonneg
  have hDegreeNat := D.canonicalActivePlaquetteDegree_le_eighteen
  have hDegree :
      (L.canonicalActivePlaquetteDegree D.edgeCard_pos : ℝ) ≤ 18 := by
    exact_mod_cast hDegreeNat
  have hInfluence :=
    D.canonicalActivePlaquetteInfluenceBound_le_two_mul_energyMaxExpRatio
  have hProduct :
      (L.canonicalActivePlaquetteDegree D.edgeCard_pos : ℝ) *
          L.canonicalActivePlaquetteInfluenceBound D.edgeCard_pos ≤
        18 * q := by
    exact mul_le_mul hDegree hInfluence
      (finite_lattice_canonicalActivePlaquetteInfluenceBound_nonneg
        L D.edgeCard_pos)
      (by norm_num)
  have hEighteenQ : 18 * q < 1 := by
    dsimp [q] at hThreshold ⊢
    norm_num at hThreshold ⊢
    linarith
  exact lt_of_le_of_lt
    (le_trans
      (finite_lattice_canonicalDobrushinCoefficient_le_exactActivePlaquetteProduct
        L D.edgeCard_pos)
      hProduct)
    hEighteenQ

end

end MathlibAnalytic
end MGAP4D
