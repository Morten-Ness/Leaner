import Mathlib

variable {R : Type*}

variable [AddMonoid R] [Mul R] {s : R}

theorem closure_mul_self : closure {x * x | x ≠ (0 : R)} = AddSubsemigroup.sumNonzeroSq R := by
  refine closure_eq_of_le (fun x hx ↦ by aesop) (fun x hx ↦ ?_)
  -- TODO : fix aesop timeout and change to `induction hx <;> aesop`
  induction hx with
  | sq ha => aesop
  | sq_add ha hs ih =>
    -- `aesop` times out
    apply add_mem
    · apply AddSubsemigroup.mem_closure_of_mem
      aesop
    aesop

