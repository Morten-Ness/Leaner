import Mathlib

variable {ι α β M N G k R : Type*}

variable [CommMonoid M] [CommMonoid N] [Preorder N]

theorem le_prod_nonempty_of_submultiplicative_on_pred [IsOrderedMonoid N] (f : M → N) (p : M → Prop)
    (h_mul : ∀ x y, p x → p y → f (x * y) ≤ f x * f y) (hp_mul : ∀ x y, p x → p y → p (x * y))
    (g : ι → M) (s : Finset ι) (hs_nonempty : s.Nonempty) (hs : ∀ i ∈ s, p (g i)) :
    f (∏ i ∈ s, g i) ≤ ∏ i ∈ s, f (g i) := by
  refine le_trans
    (Multiset.le_prod_nonempty_of_submultiplicative_on_pred f p h_mul hp_mul _ ?_ ?_) ?_
  · simp [hs_nonempty.ne_empty]
  · exact Multiset.forall_mem_map_iff.mpr hs
  simp

