import Mathlib

variable {α : Type*} {n : ℕ} {f : α → ℕ}

theorem _root_.StrictMono.nat_pow [Preorder α] (hn : n ≠ 0) (hf : StrictMono f) :
    StrictMono (f · ^ n) := (Nat.pow_left_strictMono hn).comp hf

