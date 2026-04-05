import Mathlib

variable {M A B : Type*}

variable [AddMonoid A]

theorem mem_closure_singleton {x y : A} : y ∈ closure ({x} : Set A) ↔ ∃ n : ℕ, n • x = y := by
  rw [AddSubmonoid.closure_singleton_eq, AddMonoidHom.mem_mrange]; rfl

