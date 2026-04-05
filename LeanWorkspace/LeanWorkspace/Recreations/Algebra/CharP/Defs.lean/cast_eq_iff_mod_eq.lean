import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem cast_eq_iff_mod_eq [IsLeftCancelAdd R] : (a : R) = (b : R) ↔ a % p = b % p := by
  wlog! hle : a ≤ b
  · simpa only [eq_comm] using (this _ _ hle.le)
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [Nat.cast_add, left_eq_add, CharP.cast_eq_zero_iff R p]
  constructor
  · simp +contextual [Nat.add_mod, Nat.dvd_iff_mod_eq_zero]
  intro h
  have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  simpa [Nat.dvd_iff_mod_eq_zero] using this

-- TODO: This lemma needs to be `@[simp]` for confluence in the presence of `CharP.cast_eq_zero` and
-- `Nat.cast_ofNat`, but with `no_index` on its entire LHS, it matches literally every expression so
-- is too expensive. If https://github.com/leanprover/lean4/issues/2867 is fixed in a performant way, this can be made `@[simp]`.
--
-- @[simp]

