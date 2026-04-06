import Mathlib

variable {A B M N : Type*} [AddMonoid A] [AddMonoid B] [Monoid M] [Monoid N] {ψ : AddChar A M}

theorem ne_zero_iff : ψ ≠ 0 ↔ ∃ x, ψ x ≠ 1 := by
  constructor
  · intro h
    by_contra h'
    apply h
    ext x
    by_contra hx
    exact h' ⟨x, hx⟩
  · rintro ⟨x, hx⟩ hψ
    apply hx
    rw [hψ]
    rfl
