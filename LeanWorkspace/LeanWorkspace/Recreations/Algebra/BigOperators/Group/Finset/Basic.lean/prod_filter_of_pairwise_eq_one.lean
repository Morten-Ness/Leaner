import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_filter_of_pairwise_eq_one [DecidableEq ι] {f : κ → ι} {g : ι → M} {n : κ} {I : Finset κ}
    (hn : n ∈ I) (hf : (I : Set κ).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ j ∈ I with f j = f n, g (f j) = g (f n) := by
  classical
  have h j (hj : j ∈ {i ∈ I | f i = f n}.erase n) : g (f j) = 1 := by
    simp only [mem_erase, mem_filter] at hj
    exact hf hj.2.1 hn hj.1 hj.2.2
  rw [← mul_one (g (f n)), ← Finset.prod_eq_one h,
    ← Finset.mul_prod_erase {i ∈ I | f i = f n} (fun i ↦ g (f i)) <| mem_filter.mpr ⟨hn, by rfl⟩]

