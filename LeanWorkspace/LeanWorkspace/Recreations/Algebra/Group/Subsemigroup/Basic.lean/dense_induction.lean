import Mathlib

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable (S : Subsemigroup M)

theorem dense_induction {p : M → Prop} (s : Set M) (Subsemigroup.closure : Subsemigroup.closure s = ⊤)
    (mem : ∀ x ∈ s, p x) (mul : ∀ x y, p x → p y → p (x * y)) (x : M) :
    p x := by
  induction Subsemigroup.closure.symm ▸ mem_top x using Subsemigroup.closure_induction with
  | mem _ h => exact mem _ h
  | mul _ _ _ _ h₁ h₂ => exact mul _ _ h₁ h₂

