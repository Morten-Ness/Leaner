import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

theorem _root_.exists_squarefree_dvd_pow_of_ne_zero {x : R} (hx : x ≠ 0) :
    ∃ (y : R) (n : ℕ), Squarefree y ∧ y ∣ x ∧ x ∣ y ^ n := by
  induction x using WfDvdMonoid.induction_on_irreducible with
  | zero => contradiction
  | unit u hu => exact ⟨1, 0, squarefree_one, one_dvd u, hu.dvd⟩
  | mul z p hz hp ih =>
    obtain ⟨y, n, hy, hyx, hy'⟩ := ih hz
    rcases n.eq_zero_or_pos with rfl | hn
    · exact ⟨p, 1, hp.squarefree, dvd_mul_right p z, by simp [isUnit_of_dvd_one (pow_zero y ▸ hy')]⟩
    by_cases hp' : p ∣ y
    · exact ⟨y, n + 1, hy, dvd_mul_of_dvd_right hyx _,
        mul_comm p z ▸ pow_succ y n ▸ mul_dvd_mul hy' hp'⟩
    · suffices Squarefree (p * y) from ⟨p * y, n, this,
        mul_dvd_mul_left p hyx, mul_pow p y n ▸ mul_dvd_mul (dvd_pow_self p hn.ne') hy'⟩
      exact squarefree_mul_iff.mpr ⟨hp.isRelPrime_iff_not_dvd.mpr hp', hp.squarefree, hy⟩

