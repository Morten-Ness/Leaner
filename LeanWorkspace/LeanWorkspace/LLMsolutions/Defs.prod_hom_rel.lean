import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_hom_rel [CommMonoid N] {r : M → N → Prop} {f : ι → M} {g : ι → N} {s : Finset ι}
    (h₁ : r 1 1) (h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)) :
    r (∏ x ∈ s, f x) (∏ x ∈ s, g x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using h₁
  | @insert a s ha ih =>
      simpa [Finset.prod_insert, ha, mul_comm, mul_left_comm, mul_assoc] using h₂ a _ _ ih
