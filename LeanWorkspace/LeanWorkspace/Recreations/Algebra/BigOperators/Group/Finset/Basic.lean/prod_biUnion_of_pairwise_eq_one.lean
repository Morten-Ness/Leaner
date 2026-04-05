import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_biUnion_of_pairwise_eq_one [DecidableEq ι] {s : Finset κ} {t : κ → Finset ι}
    (hs : (s : Set κ).Pairwise fun i j ↦ ∀ k ∈ t i ∩ t j, f k = 1) :
    ∏ x ∈ s.biUnion t, f x = ∏ x ∈ s, ∏ i ∈ t x, f i := by
  classical
  let t' k := (t k).filter (fun i ↦ f i ≠ 1)
  have : s.biUnion t' = (s.biUnion t).filter (fun i ↦ f i ≠ 1) := by grind
  rw [← Finset.prod_filter_ne_one, ← this, Finset.prod_biUnion]
  swap
  · intro i hi j hj hij a hai haj k hk
    have hki : k ∈ t' i := hai hk
    have hkj : k ∈ t' j := haj hk
    simp only [ne_eq, mem_filter, t'] at hki hkj
    exact (hki.2 (hs hi hj hij k (by grind))).elim
  exact Finset.prod_congr rfl (fun i hi ↦ Finset.prod_filter_ne_one (t i))

