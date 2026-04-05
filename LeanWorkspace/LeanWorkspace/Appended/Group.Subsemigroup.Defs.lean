import Mathlib

section

variable {M : Type*} {N : Type*}

variable {A : Type*} [Mul M] [SetLike A M] [hA : MulMemClass A M] (S' : A)

theorem coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y := rfl

-- lower priority so later simp lemmas are used first; to appease simp_nf

end

section

variable {M : Type*} {N : Type*}

variable [Mul M] {s : Set M}

variable {S : Subsemigroup M}

theorem subsingleton_of_subsingleton [Subsingleton (Subsemigroup M)] : Subsingleton M := by
  constructor; intro x y
  have : ∀ a : M, a ∈ (⊥ : Subsemigroup M) := by simp [Subsingleton.elim (⊥ : Subsemigroup M) ⊤]
  exact absurd (this x) Subsemigroup.notMem_bot

end
