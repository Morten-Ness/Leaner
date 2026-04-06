FAIL
import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_hom₂_ne_zero [CommMonoid O] {s : Multiset ι} (hs : s ≠ 0) (f : M → N → O)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι → M) (f₂ : ι → N) :
    (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      contradiction
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [ih (by simp)]
      symm
      exact hf (f₁ a) (Multiset.prod (Multiset.map f₁ s)) (f₂ a) (Multiset.prod (Multiset.map f₂ s))
