import Mathlib

variable {ι R S : Type*}

variable [CommMonoidWithZero R]

variable [Preorder R] [ZeroLEOneClass R] [PosMulMono R] {f g : ι → R} {s t : Finset ι}

theorem prod_le_prod (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    simp only [prod_cons, forall_mem_cons] at h0 h1 ⊢
    have := posMulMono_iff_mulPosMono.1 ‹PosMulMono R›
    gcongr
    exacts [Finset.prod_nonneg h0.2, h0.1.trans h1.1, h1.1, ih h0.2 h1.2]

