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

include hpq hn₁' in
theorem isIso_mapFourδ₄Toδ₃' (h : ¬ (c r).Rel pq pq')
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₃'
      (data.le₀₁' r hr pq' hi₀ hi₁) (data.le₁₂' pq' hi₁ hi₂)
      (data.le₂₃' r hr pq' hi₂ hi₃) (data.le₃₃' hrr' hr pq' hi₃ hi₃') n₀ n₁ n₂) := by
  apply X.isIso_map_fourδ₄Toδ₃_of_isZero _ _ _ _ _ _ _ _ _ _
  refine X.isZero_H_obj_mk₁_i₃_le' data r r' hrr' hr pq' (fun _ hk ↦ ?_) _ (by lia) _ _ hi₃ hi₃'
  obtain rfl := (c r).prev_eq' hk
  subst hpq
  exact h hk

