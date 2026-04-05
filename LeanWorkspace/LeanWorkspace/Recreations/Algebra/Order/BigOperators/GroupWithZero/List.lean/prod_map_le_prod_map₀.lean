import Mathlib

variable {R : Type*} [CommMonoidWithZero R] [PartialOrder R] [ZeroLEOneClass R] [PosMulMono R]

theorem prod_map_le_prod_map₀ {ι : Type*} {s : List ι} (f : ι → R) (g : ι → R)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    (map f s).prod ≤ (map g s).prod := by
  induction s with
  | nil => simp
  | cons a s hind =>
    simp only [map_cons, prod_cons]
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    apply mul_le_mul
    · apply h
      simp
    · grind
    · grind [List.prod_nonneg]
    · apply (h0 _ _).trans (h _ _) <;> simp only [mem_cons, true_or]

