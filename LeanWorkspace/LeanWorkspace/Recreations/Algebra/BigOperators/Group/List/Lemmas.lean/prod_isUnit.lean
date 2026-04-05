import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_isUnit : ∀ {L : List M}, (∀ m ∈ L, IsUnit m) → IsUnit L.prod
  | [], _ => by simp
  | h :: t, u => by
    simp only [List.prod_cons]
    exact IsUnit.mul (u h mem_cons_self) (prod_isUnit fun m mt => u m (mem_cons_of_mem h mt))
