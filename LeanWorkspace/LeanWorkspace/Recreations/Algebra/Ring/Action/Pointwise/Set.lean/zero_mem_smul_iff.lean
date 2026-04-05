import Mathlib

open scoped Pointwise

variable {α β : Type*}

variable [Semiring α] [AddCommMonoid β] [Module α β]

variable [IsDomain α] [Module.IsTorsionFree α β] {a : α} {s : Set α} {t : Set β}

theorem zero_mem_smul_iff : 0 ∈ s • t ↔ 0 ∈ s ∧ t.Nonempty ∨ 0 ∈ t ∧ s.Nonempty where
  mp | ⟨a, ha, b, hb, h⟩ => by
      obtain rfl | rfl := smul_eq_zero.1 h; exacts [.inl ⟨ha, b, hb⟩, .inr ⟨hb, a, ha⟩]
  mpr
  | .inl ⟨hs, b, hb⟩ => ⟨0, hs, b, hb, zero_smul _ _⟩
  | .inr ⟨ht, a, ha⟩ => ⟨a, ha, 0, ht, smul_zero _⟩

