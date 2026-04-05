import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

variable (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
  (pq pq' pq'' : κ) (hpq : (c r).prev pq' = pq) (hpq' : (c r).next pq' = pq'')
  (i₀' i₀ i₁ i₂ i₃ i₃' : ι)
  (hi₀' : i₀' = data.i₀ r' pq')
  (hi₀ : i₀ = data.i₀ r pq')
  (hi₁ : i₁ = data.i₁ pq')
  (hi₂ : i₂ = data.i₂ pq')
  (hi₃ : i₃ = data.i₃ r pq')
  (hi₃' : i₃' = data.i₃ r' pq')
  (n₀ n₁ n₂ : ℤ)
  (hn₁' : n₁ = data.deg pq')

set_option backward.isDefEq.respectTransparency false in
theorem fac (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
  (kf X data r r' hrr' hr pq' pq'' i₀' i₀ i₁ i₂ i₃
      hi₀' hi₀ hi₁ hi₂ hi₃ n₀ n₁ n₂ hn₁').ι ≫
    (cc X data r r' hrr' hr pq pq' i₀ i₁ i₂ i₃ i₃'
      hi₀ hi₁ hi₂ hi₃ hi₃' n₀ n₁ n₂ hn₁').π =
  X.mapFourδ₄Toδ₃' i₀' i₁ i₂ i₃ i₃' _ _ _ (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂ ≫
    X.mapFourδ₁Toδ₀' i₀' i₀ i₁ i₂ i₃'
      (data.i₀_le' hrr' hr pq' hi₀' hi₀) _ _ _ n₀ n₁ n₂ := by
  simp [← map_comp]
  rfl

