import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

variable [X.HasSpectralSequence data]

variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq')
  (hi₀ : i₀ = data.i₀ r pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq')
  (hi₃' : i₃' = data.i₃ r' pq')
  (n₀ n₁ n₂ : ℤ) (hn₁' : n₁ = data.deg pq')

theorem spectralSequence_iso (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X.spectralSequence data).iso r r' pq' =
    ((X.spectralSequence data).page r).homologyIsoSc' pq pq' pq'' hpq hpq' ≪≫
      (X.spectralSequenceHomologyData data r r' hrr' hr pq pq' pq'' hpq hpq'
      i₀' i₀ i₁ i₂ i₃ i₃' hi₀' hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').left.homologyIso ≪≫
        (X.spectralSequencePageXIso data r' (by lia) _ _ _ _ _
          hi₀' hi₁ hi₂ hi₃' _ _ _ hn₁').symm := by
  obtain rfl : n₀ = n₁ - 1 := by lia
  obtain rfl : n₂ = n₁ + 1 := by lia
  subst hpq hpq' hn₁' hi₀ hi₁ hi₂ hi₃ hi₀' hi₃'
  ext
  simp [CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIso, CategoryTheory.Abelian.SpectralObject.spectralSequence, CategoryTheory.Abelian.SpectralObject.spectralSequenceHomologyData,
    SpectralSequence.homologyIso, SpectralSequence.homologyIso']

