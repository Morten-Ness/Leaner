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

include hpq' hn₁' in
theorem isIso_mapFourδ₁Toδ₀' (h : ¬ (c r).Rel pq' pq'')
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.mapFourδ₁Toδ₀'
      i₀' i₀ i₁ i₂ i₃ (data.i₀_le' hrr' hr pq' hi₀' hi₀) (data.le₀₁' r hr pq' hi₀ hi₁)
        (data.le₁₂' pq' hi₁ hi₂) (data.le₂₃' r hr pq' hi₂ hi₃) n₀ n₁ n₂ hn₁ hn₂) := by
  apply X.isIso_map_fourδ₁Toδ₀_of_isZero ..
  refine X.isZero_H_obj_mk₁_i₀_le' data r r' hrr' hr pq' (fun k hk ↦ ?_) _ (by lia) _ _ hi₀' hi₀
  obtain rfl := (c r).next_eq' hk
  subst hpq'
  exact h hk

