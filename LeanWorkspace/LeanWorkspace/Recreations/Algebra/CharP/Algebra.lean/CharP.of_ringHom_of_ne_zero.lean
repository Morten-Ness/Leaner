import Mathlib

variable {R A : Type*}

theorem CharP.of_ringHom_of_ne_zero [NonAssocSemiring R] [NoZeroDivisors R]
    [NonAssocSemiring A] [Nontrivial A]
    (f : R →+* A) (p : ℕ) (hp : p ≠ 0) [CharP R p] : CharP A p := by
  have := f.domain_nontrivial
  have H := (CharP.char_is_prime_or_zero R p).resolve_right hp
  obtain ⟨q, hq⟩ := CharP.exists A
  obtain ⟨k, e⟩ := dvd_of_ringHom f p q
  have := Nat.isUnit_iff.mp ((H.2 e).resolve_left (Nat.isUnit_iff.not.mpr (char_ne_one A q)))
  rw [this, mul_one] at e
  exact e ▸ hq

