FAIL
import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_eq_bot {S : Submonoid Mᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := by
  constructor
  · intro h
    ext x
    constructor
    · intro hx
      have hx' : MulOpposite.unop x ∈ S.unop := hx
      rw [h] at hx'
      change MulOpposite.unop x = 1 at hx'
      apply MulOpposite.unop_injective
      simpa using hx'
    · intro hx
      rw [Submonoid.mem_bot] at hx
      rw [hx]
      exact S.one_mem
  · intro h
    rw [h]
    ext x
    rw [Submonoid.mem_bot]
    rw [Submonoid.mem_bot]
    constructor <;> intro hx <;> simpa using hx
