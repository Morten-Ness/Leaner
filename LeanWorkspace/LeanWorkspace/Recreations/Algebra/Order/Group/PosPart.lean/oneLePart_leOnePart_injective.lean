import Mathlib

variable {α : Type*}

variable [Lattice α]

variable [Group α] {a b : α}

variable [MulLeftMono α]

theorem oneLePart_leOnePart_injective : Function.Injective fun a : α ↦ (a⁺ᵐ, a⁻ᵐ) := by
  simp only [Function.Injective, Prod.mk.injEq, and_imp]
  rintro a b hpos hneg
  rw [← oneLePart_div_leOnePart a, ← oneLePart_div_leOnePart b, hpos, hneg]

