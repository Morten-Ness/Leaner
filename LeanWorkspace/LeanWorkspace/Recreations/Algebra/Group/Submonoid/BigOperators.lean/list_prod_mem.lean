import Mathlib

variable {M A B : Type*}

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ S) : l.prod ∈ S := by
  lift l to List S using hl
  rw [← SubmonoidClass.coe_list_prod]
  exact l.prod.coe_prop

