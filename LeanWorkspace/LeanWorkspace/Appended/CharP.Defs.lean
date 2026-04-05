import Mathlib

section

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem CharOne.subsingleton [CharP R 1] : Subsingleton R := Subsingleton.intro <|
    suffices ∀ r : R, r = 0 from fun a b => show a = b by rw [this a, this b]
    fun r =>
    calc
      r = 1 * r := by rw [one_mul]
      _ = (1 : ℕ) * r := by rw [Nat.cast_one]
      _ = 0 * r := by rw [CharP.cast_eq_zero]
      _ = 0 := by rw [zero_mul]

end

section

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

end

section

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem char_is_prime_of_pos (p : ℕ) [NeZero p] [CharP R p] : Fact p.Prime := ⟨(CharP.char_is_prime_or_zero R _).resolve_right <| NeZero.ne p⟩

end

section

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem char_is_prime_or_zero (p : ℕ) [hc : CharP R p] : Nat.Prime p ∨ p = 0 := match p, hc with
  | 0, _ => Or.inr rfl
  | 1, hc => absurd (Eq.refl (1 : ℕ)) (@CharP.char_ne_one R _ _ (1 : ℕ) hc)
  | m + 2, hc => Or.inl (@CharP.char_is_prime_of_two_le R _ _ (m + 2) hc (Nat.le_add_left 2 m))

end

section

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem char_prime_of_ne_zero {p : ℕ} [CharP R p] (hp : p ≠ 0) : p.Prime := (CharP.char_is_prime_or_zero R p).resolve_right hp

end

section

variable (R : Type*)

variable [NonAssocSemiring R]

theorem eq_iff {p : ℕ} : ringChar R = p ↔ CharP R p := ⟨ringChar.of_eq, @ringChar.eq R _ p⟩

end

section

variable (R : Type*)

variable [NonAssocSemiring R]

variable [NoZeroDivisors R]

variable [Nontrivial R]

theorem exists' (R : Type*) [NonAssocRing R] [NoZeroDivisors R] [Nontrivial R] :
    CharZero R ∨ ∃ p : ℕ, Fact p.Prime ∧ CharP R p := by
  obtain ⟨p, hchar⟩ := CharP.exists R
  rcases CharP.char_is_prime_or_zero R p with h | rfl
  exacts [Or.inr ⟨p, Fact.mk h, hchar⟩, Or.inl (CharP.charP_to_charZero R)]

end

section

variable (R : Type*)

variable [NonAssocSemiring R]

theorem existsUnique : ∃! p, CharP R p := let ⟨c, H⟩ := CharP.exists R
  ⟨c, H, fun _y H2 => CharP.eq R H2 H⟩

end

section

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem false_of_nontrivial_of_char_one [Nontrivial R] [CharP R 1] : False := by
  have : Subsingleton R := CharP.CharOne.subsingleton
  exact false_of_nontrivial_of_subsingleton R

end

section

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem intCast_eq_zero_iff (a : ℤ) : (a : R) = 0 ↔ (p : ℤ) ∣ a := by
  rcases lt_trichotomy a 0 with (h | rfl | h)
  · rw [← neg_eq_zero, ← Int.cast_neg, ← Int.dvd_neg]
    lift -a to ℕ using Int.neg_nonneg.mpr (le_of_lt h) with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]
  · simp
  · lift a to ℕ using le_of_lt h with b
    rw [Int.cast_natCast, CharP.cast_eq_zero_iff R p, Int.natCast_dvd_natCast]

end

section

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem nontrivial_of_char_ne_one {v : ℕ} (hv : v ≠ 1) [hr : CharP R v] : Nontrivial R := ⟨⟨(1 : ℕ), 0, fun h =>
      hv <| by rwa [CharP.cast_eq_zero_iff _ v, Nat.dvd_one] at h⟩⟩

end

section

variable (R : Type*)

variable [AddMonoidWithOne R] {r : R} {n p : ℕ}

theorem not_char_dvd (p : ℕ) [CharP R p] (k : ℕ) [h : NeZero (k : R)] : ¬p ∣ k := by
  rwa [← CharP.cast_eq_zero_iff R p k, ← Ne, ← neZero_iff]

end

section

variable (R : Type*)

variable [AddMonoidWithOne R] {r : R} {n p : ℕ}

theorem of_not_dvd [CharP R p] (h : ¬p ∣ n) : NeZero (n : R) := ⟨(CharP.cast_eq_zero_iff R p n).not.mpr h⟩

end

section

variable (R : Type*)

variable [NonAssocSemiring R]

theorem ringChar_eq_one : ringChar R = 1 ↔ Subsingleton R := by
  rw [← Nat.dvd_one, ← ringChar.spec, eq_comm, Nat.cast_one, subsingleton_iff_zero_eq_one]

end

section

variable (R : Type*)

variable {R} [NonAssocSemiring R]

theorem ringChar_ne_one [Nontrivial R] : ringChar R ≠ 1 := by
  simpa using not_subsingleton R

end

section

variable (R : Type*)

variable [NonAssocSemiring R]

theorem spec : ∀ x : ℕ, (x : R) = 0 ↔ ringChar R ∣ x := by
  letI : CharP R (ringChar R) := (Classical.choose_spec (CharP.existsUnique R)).1
  exact CharP.cast_eq_zero_iff R (ringChar R)

end

section

variable (R : Type*)

variable [NonAssocSemiring R]

theorem «exists» : ∃ p, CharP R p := letI := Classical.decEq R
  by_cases
    (fun H : ∀ p : ℕ, (p : R) = 0 → p = 0 =>
      ⟨0, ⟨fun x => by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; simp⟩⟩⟩)
    fun H =>
    ⟨Nat.find (not_forall.1 H),
      ⟨fun x =>
        ⟨fun H1 =>
          Nat.dvd_of_mod_eq_zero
            (by_contradiction fun H2 =>
              Nat.find_min (not_forall.1 H)
                (Nat.mod_lt x <|
                  Nat.pos_of_ne_zero <| not_of_not_imp <| Nat.find_spec (not_forall.1 H))
                (not_imp_of_and_not
                  ⟨by
                    rwa [← Nat.mod_add_div x (Nat.find (not_forall.1 H)), Nat.cast_add,
                      Nat.cast_mul,
                      of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H)),
                      zero_mul, add_zero] at H1,
                    H2⟩)),
          fun H1 => by
          rw [← Nat.mul_div_cancel' H1, Nat.cast_mul,
            of_not_not (not_not_of_not_imp <| Nat.find_spec (not_forall.1 H)),
            zero_mul]⟩⟩⟩

end
