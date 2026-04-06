import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

theorem prod_induction {M : Type*} [CommMonoid M] (f : ι → M) (p : M → Prop)
    (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p <| f x) :
    p <| ∏ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using unit
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      apply hom
      · exact base a (Finset.mem_insert_self a s)
      · apply ih
        intro x hx
        exact base x (Finset.mem_insert_of_mem hx)
