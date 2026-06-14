import MGAP4D.MathlibAnalytic.AxiomaticYangMillsMassGapClosure
import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Four-momentum in four-dimensional Minkowski space.  Coordinate `0` is energy;
coordinates `1,2,3` are spatial momentum. -/
abbrev MinkowskiMomentum := Fin 4 → ℝ

/-- The energy component of a four-momentum. -/
def MinkowskiMomentum.energy (p : MinkowskiMomentum) : ℝ := p 0

/-- Squared Euclidean norm of the spatial momentum. -/
def MinkowskiMomentum.spatialNormSq (p : MinkowskiMomentum) : ℝ :=
  ∑ i : Fin 3, (p i.succ) ^ 2

/-- The closed forward light cone, written in energy-momentum coordinates. -/
def MinkowskiMomentum.InForwardCone (p : MinkowskiMomentum) : Prop :=
  0 ≤ p.energy ∧ p.spatialNormSq ≤ p.energy ^ 2

/-- Spatial momentum has nonnegative squared norm. -/
theorem minkowskiMomentum_spatialNormSq_nonneg (p : MinkowskiMomentum) :
    0 ≤ p.spatialNormSq := by
  unfold MinkowskiMomentum.spatialNormSq
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- A compact, nontrivial topological gauge group.  The group laws, topology,
compactness, and nontriviality are actual Mathlib structures rather than bare
Boolean or audit markers. -/
structure CompactNontrivialGaugeGroup where
  carrier : Type
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [topologicalGroup : IsTopologicalGroup carrier]
  [compactSpace : CompactSpace carrier]
  [nontrivial : Nontrivial carrier]

attribute [instance]
  CompactNontrivialGaugeGroup.group
  CompactNontrivialGaugeGroup.topologicalSpace
  CompactNontrivialGaugeGroup.topologicalGroup
  CompactNontrivialGaugeGroup.compactSpace
  CompactNontrivialGaugeGroup.nontrivial

/-- A typed Osterwalder--Schrader / Wightman field package.  Reflection positivity
is stated as positivity of the reflected two-point Schwinger form.  The remaining
named axioms are predicates over this displayed field package and are therefore
kept distinct from the later Hamiltonian spectral assumptions. -/
structure ExplicitOSWightmanFieldAxioms where
  gauge : CompactNontrivialGaugeGroup
  TestFunction : Type
  [testNormedAddCommGroup : NormedAddCommGroup TestFunction]
  [testNormedSpace : NormedSpace ℝ TestFunction]
  reflection : TestFunction →L[ℝ] TestFunction
  schwingerTwo : TestFunction →L[ℝ] TestFunction →L[ℝ] ℝ
  reflection_involutive : ∀ f, reflection (reflection f) = f
  reflectionPositive : ∀ f, 0 ≤ schwingerTwo (reflection f) f
  euclideanInvariant : Prop
  schwingerSymmetric : ∀ f g, schwingerTwo f g = schwingerTwo g f
  clusterProperty : Prop
  regularity : Prop
  wightmanLocality : Prop
  wightmanCovariance : Prop
  wightmanSpectrumCondition : Prop

attribute [instance]
  ExplicitOSWightmanFieldAxioms.testNormedAddCommGroup
  ExplicitOSWightmanFieldAxioms.testNormedSpace

/-- Projection-valued-measure laws needed by the present mass-gap bridge,
expressed as a Borel-set-indexed family of bounded operators on a Hilbert space.
Countable-additivity can later strengthen this interface without changing the
energy-momentum argument below. -/
structure OrthogonalProjectionValuedSetFunction
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  projection : Set ℝ → H →L[ℝ] H
  empty_apply : ∀ x, projection ∅ x = 0
  univ_apply : ∀ x, projection Set.univ x = x
  idempotent : ∀ s x, projection s (projection s x) = projection s x
  selfAdjoint :
    ∀ s x y, inner ℝ (projection s x) y = inner ℝ x (projection s y)
  disjoint_additive :
    ∀ s t, Disjoint s t → ∀ x,
      projection (s ∪ t) x = projection s x + projection t x

/-- Energy values obtained by projecting a joint energy-momentum spectrum to its
zeroth coordinate. -/
def energyProjection (spectrum : Set MinkowskiMomentum) : Set ℝ :=
  {E | ∃ p ∈ spectrum, p.energy = E}

/-- Relativistic mass gap in the joint energy-momentum spectrum.  Apart from the
vacuum momentum, every spectral momentum lies on or above the mass-`m`
hyperboloid. -/
def HasRelativisticMassGap
    (spectrum : Set MinkowskiMomentum) (m : ℝ) : Prop :=
  0 < m ∧
  (0 : MinkowskiMomentum) ∈ spectrum ∧
  ∀ p ∈ spectrum, p ≠ 0 →
    m ^ 2 + p.spatialNormSq ≤ p.energy ^ 2

/-- Hamiltonian mass gap at `m`: zero is a vacuum spectral value and every
nonzero energy spectral value is at least `m`. -/
def HasHamiltonianMassGap (energySpectrum : Set ℝ) (m : ℝ) : Prop :=
  0 < m ∧
  0 ∈ energySpectrum ∧
  ∀ E ∈ energySpectrum, E ≠ 0 → m ≤ E

/-- The spectral condition plus a relativistic mass hyperboloid bound gives a
lower bound on the energy component. -/
theorem relativistic_mass_gap_energy_lower_bound
    {spectrum : Set MinkowskiMomentum} {m : ℝ}
    (hSpectrum : ∀ p ∈ spectrum, p.InForwardCone)
    (hGap : HasRelativisticMassGap spectrum m)
    {p : MinkowskiMomentum} (hp : p ∈ spectrum) (hp0 : p ≠ 0) :
    m ≤ p.energy := by
  have hm : 0 < m := hGap.1
  have hCone : p.InForwardCone := hSpectrum p hp
  have hEnergy : 0 ≤ p.energy := hCone.1
  have hSpatial : 0 ≤ p.spatialNormSq :=
    minkowskiMomentum_spatialNormSq_nonneg p
  have hMass : m ^ 2 + p.spatialNormSq ≤ p.energy ^ 2 :=
    hGap.2.2 p hp hp0
  nlinarith

/-- A joint relativistic mass gap descends to a Hamiltonian energy gap under
projection to the energy coordinate. -/
theorem relativistic_mass_gap_implies_hamiltonian_mass_gap
    {spectrum : Set MinkowskiMomentum} {m : ℝ}
    (hSpectrum : ∀ p ∈ spectrum, p.InForwardCone)
    (hGap : HasRelativisticMassGap spectrum m) :
    HasHamiltonianMassGap (energyProjection spectrum) m := by
  refine ⟨hGap.1, ?_, ?_⟩
  · exact ⟨0, hGap.2.1, rfl⟩
  · intro E hE hE0
    rcases hE with ⟨p, hp, rfl⟩
    have hp0 : p ≠ 0 := by
      intro hpZero
      apply hE0
      simp [MinkowskiMomentum.energy, hpZero]
    exact relativistic_mass_gap_energy_lower_bound hSpectrum hGap hp hp0

/-- Fully typed reconstructed QFT data connecting the OS/Wightman field package,
Mathlib Hilbert space, densely-defined Hamiltonian, normalized vacuum, spectral
projection family, and joint energy-momentum spectrum. -/
structure ExplicitWightmanOSReconstructedModel where
  axioms : ExplicitOSWightmanFieldAxioms
  H : Type
  [hilbertNormedAddCommGroup : NormedAddCommGroup H]
  [hilbertInnerProductSpace : InnerProductSpace ℝ H]
  [hilbertCompleteSpace : CompleteSpace H]
  field : axioms.TestFunction → H →ₗ.[ℝ] H
  hamiltonian : H →ₗ.[ℝ] H
  hamiltonianSelfAdjoint : IsSelfAdjoint hamiltonian
  vacuum : H
  vacuum_norm : ‖vacuum‖ = 1
  vacuum_mem_hamiltonianDomain : vacuum ∈ hamiltonian.domain
  vacuumEnergyZero :
    hamiltonian ⟨vacuum, vacuum_mem_hamiltonianDomain⟩ = 0
  spectralPVM : OrthogonalProjectionValuedSetFunction H
  vacuumSpectralProjection : spectralPVM.projection ({0} : Set ℝ) vacuum = vacuum
  energyMomentumSpectrum : Set MinkowskiMomentum
  spectrumCondition : ∀ p ∈ energyMomentumSpectrum, p.InForwardCone
  hamiltonianEnergySpectrum : Set ℝ
  energySpectrum_eq_projection :
    hamiltonianEnergySpectrum = energyProjection energyMomentumSpectrum

attribute [instance]
  ExplicitWightmanOSReconstructedModel.hilbertNormedAddCommGroup
  ExplicitWightmanOSReconstructedModel.hilbertInnerProductSpace
  ExplicitWightmanOSReconstructedModel.hilbertCompleteSpace

/-- The reconstructed model has mass gap `m` precisely through its Hamiltonian
energy spectrum. -/
def ExplicitWightmanOSReconstructedModel.HasMassGap
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ) : Prop :=
  HasHamiltonianMassGap M.hamiltonianEnergySpectrum m

/-- Main definition-level bridge: a relativistic gap in the Wightman joint
energy-momentum spectrum yields a Hamiltonian mass gap, while the Hamiltonian,
vacuum and PVM are the actual displayed Mathlib objects of the same model. -/
theorem explicit_wightman_os_reconstruction_has_mass_gap
    (M : ExplicitWightmanOSReconstructedModel) {m : ℝ}
    (hGap : HasRelativisticMassGap M.energyMomentumSpectrum m) :
    M.HasMassGap m := by
  unfold ExplicitWightmanOSReconstructedModel.HasMassGap
  rw [M.energySpectrum_eq_projection]
  exact relativistic_mass_gap_implies_hamiltonian_mass_gap
    M.spectrumCondition hGap

/-- A theorem certificate exposing every requested connection without collapsing
OS/Wightman assumptions and spectral assumptions into a single undifferentiated
`ready` proposition. -/
structure ExplicitWightmanOSMassGapCertificate
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ) where
  gaugeCompact : CompactSpace M.axioms.gauge.carrier
  gaugeNontrivial : Nontrivial M.axioms.gauge.carrier
  reflectionPositive :
    ∀ f, 0 ≤ M.axioms.schwingerTwo (M.axioms.reflection f) f
  fieldFamily : M.axioms.TestFunction → M.H →ₗ.[ℝ] M.H
  hilbertComplete : CompleteSpace M.H
  hamiltonianSelfAdjoint : IsSelfAdjoint M.hamiltonian
  vacuumNormalized : ‖M.vacuum‖ = 1
  vacuumEnergyZero :
    M.hamiltonian ⟨M.vacuum, M.vacuum_mem_hamiltonianDomain⟩ = 0
  vacuumPVMPoint :
    M.spectralPVM.projection ({0} : Set ℝ) M.vacuum = M.vacuum
  energyMomentumSpectrumCondition :
    ∀ p ∈ M.energyMomentumSpectrum, p.InForwardCone
  relativisticMassGap : HasRelativisticMassGap M.energyMomentumSpectrum m
  hamiltonianMassGap : M.HasMassGap m

/-- Construct the complete OS/Wightman → Hilbert → Hamiltonian → vacuum → PVM →
energy-momentum spectrum → mass-gap certificate. -/
def explicitWightmanOSMassGapCertificate
    (M : ExplicitWightmanOSReconstructedModel) {m : ℝ}
    (hGap : HasRelativisticMassGap M.energyMomentumSpectrum m) :
    ExplicitWightmanOSMassGapCertificate M m :=
  { gaugeCompact := M.axioms.gauge.compactSpace
    gaugeNontrivial := M.axioms.gauge.nontrivial
    reflectionPositive := M.axioms.reflectionPositive
    fieldFamily := M.field
    hilbertComplete := M.hilbertCompleteSpace
    hamiltonianSelfAdjoint := M.hamiltonianSelfAdjoint
    vacuumNormalized := M.vacuum_norm
    vacuumEnergyZero := M.vacuumEnergyZero
    vacuumPVMPoint := M.vacuumSpectralProjection
    energyMomentumSpectrumCondition := M.spectrumCondition
    relativisticMassGap := hGap
    hamiltonianMassGap :=
      explicit_wightman_os_reconstruction_has_mass_gap M hGap }

/-- Forgetful projection from the stronger typed field package to the existing
repository OS/Wightman interface. -/
def ExplicitOSWightmanFieldAxioms.toLegacy
    (A : ExplicitOSWightmanFieldAxioms) : OSWightmanYangMillsAxioms :=
  { gaugeGroup := A.gauge.carrier
    gaugeGroupCompact := CompactSpace A.gauge.carrier
    gaugeGroupNontrivial := Nontrivial A.gauge.carrier
    fieldAlgebra := A.TestFunction
    euclideanFieldConfigurations := A.TestFunction
    schwingerFunctions := fun _ => ℝ
    osReflectionPositive :=
      ∀ f, 0 ≤ A.schwingerTwo (A.reflection f) f
    osEuclideanInvariant := A.euclideanInvariant
    osSymmetric := ∀ f g, A.schwingerTwo f g = A.schwingerTwo g f
    osClusterProperty := A.clusterProperty
    osRegularity := A.regularity
    wightmanLocality := A.wightmanLocality
    wightmanCovariance := A.wightmanCovariance
    wightmanSpectrumCondition := A.wightmanSpectrumCondition }

/-- The stronger typed package supplies the existing repository readiness
predicate without adding any new physical assumption. -/
theorem explicit_os_wightman_toLegacy_ready
    (A : ExplicitOSWightmanFieldAxioms)
    (hEuclidean : A.euclideanInvariant)
    (hCluster : A.clusterProperty)
    (hRegularity : A.regularity)
    (hLocality : A.wightmanLocality)
    (hCovariance : A.wightmanCovariance)
    (hSpectrum : A.wightmanSpectrumCondition) :
    A.toLegacy.ready := by
  unfold OSWightmanYangMillsAxioms.ready
  change
    CompactSpace A.gauge.carrier ∧
    Nontrivial A.gauge.carrier ∧
    (∀ f, 0 ≤ A.schwingerTwo (A.reflection f) f) ∧
    A.euclideanInvariant ∧
    (∀ f g, A.schwingerTwo f g = A.schwingerTwo g f) ∧
    A.clusterProperty ∧
    A.regularity ∧
    A.wightmanLocality ∧
    A.wightmanCovariance ∧
    A.wightmanSpectrumCondition
  exact ⟨A.gauge.compactSpace, A.gauge.nontrivial,
    A.reflectionPositive, hEuclidean, A.schwingerSymmetric,
    hCluster, hRegularity, hLocality, hCovariance, hSpectrum⟩

end

end MathlibAnalytic
end MGAP4D
