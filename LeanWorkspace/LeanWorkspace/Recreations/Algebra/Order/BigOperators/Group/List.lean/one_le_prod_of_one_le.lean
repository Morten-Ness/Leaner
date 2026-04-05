import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem one_le_prod_of_one_le [Preorder M] [MulLeftMono M] {l : List M}
    (hl₁ : ∀ x ∈ l, (1 : M) ≤ x) : 1 ≤ l.prod := by
  -- We don't use `List.pow_card_le_prod` to avoid assumption
  -- [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)]
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    rw [prod_cons]
    exact one_le_mul (hl₁ hd mem_cons_self) (ih fun x h => hl₁ x (mem_cons_of_mem hd h))

