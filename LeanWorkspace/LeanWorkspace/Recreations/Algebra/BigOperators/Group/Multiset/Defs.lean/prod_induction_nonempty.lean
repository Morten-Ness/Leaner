import Mathlib

variable {F ι M N : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_induction_nonempty (p : M → Prop) (p_mul : ∀ a b, p a → p b → p (a * b)) (hs : s ≠ ∅)
    (p_s : ∀ a ∈ s, p a) : p s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp at hs
  | cons a s hsa =>
    rw [Multiset.prod_cons]
    by_cases hs_empty : s = ∅
    · simp [hs_empty, p_s a]
    have hps : ∀ x, x ∈ s → p x := fun x hxs => p_s x (mem_cons_of_mem hxs)
    exact p_mul a s.prod (p_s a (mem_cons_self a s)) (hsa hs_empty hps)

