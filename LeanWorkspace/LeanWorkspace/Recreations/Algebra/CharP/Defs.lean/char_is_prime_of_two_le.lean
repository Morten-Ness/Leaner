import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

theorem char_is_prime_of_two_le (p : ℕ) [CharP R p] (hp : 2 ≤ p) : Nat.Prime p := suffices ∀ (d) (_ : d ∣ p), d = 1 ∨ d = p from Nat.prime_def.mpr ⟨hp, this⟩
  fun (d : ℕ) (hdvd : ∃ e, p = d * e) =>
  let ⟨e, hmul⟩ := hdvd
  have : (p : R) = 0 := (cast_eq_zero_iff R p p).mpr (dvd_refl p)
  have : (d : R) * e = 0 := @Nat.cast_mul R _ d e ▸ hmul ▸ this
  Or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
    (fun hd : (d : R) = 0 =>
      have : p ∣ d := (cast_eq_zero_iff R p d).mp hd
      show d = 1 ∨ d = p from Or.inr (this.antisymm' ⟨e, hmul⟩))
    fun he : (e : R) = 0 =>
    have : p ∣ e := (cast_eq_zero_iff R p e).mp he
    have : e ∣ p := dvd_of_mul_left_eq d (Eq.symm hmul)
    have : e = p := ‹e ∣ p›.antisymm ‹p ∣ e›
    have h₀ : 0 < p := by grind
    have : d * p = 1 * p := by grind
    show d = 1 ∨ d = p from Or.inl (mul_right_cancel₀ h₀.ne' this)

