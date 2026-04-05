import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_map_eq_pow_single [DecidableEq α] {l : List α} (a : α) (f : α → M)
    (hf : ∀ a', a' ≠ a → a' ∈ l → f a' = 1) : (l.map f).prod = f a ^ l.count a := by
  induction l generalizing a with
  | nil => rw [map_nil, prod_nil, count_nil, _root_.pow_zero]
  | cons a' as h =>
    specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons, List.prod_cons, count_cons, h]
    simp only [beq_iff_eq]
    split_ifs with ha'
    · rw [ha', _root_.pow_succ']
    · rw [hf a' ha' mem_cons_self, one_mul, add_zero]

