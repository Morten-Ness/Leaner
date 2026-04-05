import Mathlib

section

variable {R ι : Type*}

variable [Semiring R] [CharP R 2]

theorem add_cancel_left (a b : R) : a + (a + b) = b := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

end

section

variable {R ι : Type*}

variable [Semiring R] [CharP R 2]

theorem add_cancel_right (a b : R) : a + b + b = a := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

end

section

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem add_eq_iff_eq_add {a b c : R} : a + b = c ↔ a = c + b := by
  rw [← sub_eq_iff_eq_add, CharTwo.sub_eq_add]

end

section

variable {R ι : Type*}

variable [CommSemiring R] [CharP R 2]

theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  rw [← pow_two, ← pow_two, ← pow_two, CharTwo.add_sq]

end

section

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem eq_add_iff_add_eq {a b c : R} : a = b + c ↔ a + c = b := by
  rw [← eq_sub_iff_add_eq, CharTwo.sub_eq_add]

end

section

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem intCast_cases (n : ℤ) : (n : R) = 0 ∨ (n : R) = 1 := (Set.ext_iff.1 CharTwo.range_intCast _).1 (Set.mem_range_self _)

end

section

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem intCast_eq_mod (n : ℤ) : (n : R) = (n % 2 : ℤ) := by
  simp [CharTwo.intCast_eq_ite, Int.even_iff]

end

section

variable {R ι : Type*}

variable [CommSemiring R] [CharP R 2]

private def sqAddMonoidHom : R →+ R where
  toFun := (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := CharTwo.add_sq


theorem list_sum_mul_self (l : List R) : l.sum * l.sum = (List.map (fun x => x * x) l).sum := by
  simp_rw [← pow_two, CharTwo.list_sum_sq]

end

section

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem natCast_cases (n : ℕ) : (n : R) = 0 ∨ (n : R) = 1 := CharTwo.range_natCast.le (Set.mem_range_self _)

end

section

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem natCast_eq_mod (n : ℕ) : (n : R) = (n % 2 : ℕ) := by
  simp [CharTwo.natCast_eq_ite, Nat.even_iff]

end

section

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem neg_eq (x : R) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, CharTwo.add_self_eq_zero]

end

section

variable {R ι : Type*}

variable [AddMonoidWithOne R]

theorem of_one_ne_zero_of_two_eq_zero (h₁ : (1 : R) ≠ 0) (h₂ : (2 : R) = 0) : CharP R 2 where
  cast_eq_zero_iff n := by
    obtain hn | hn := Nat.even_or_odd n
    · simp_rw [hn.two_dvd, iff_true]
      exact natCast_eq_zero_of_even_of_two_eq_zero hn h₂
    · simp_rw [hn.not_two_dvd_nat, iff_false]
      rwa [natCast_eq_one_of_odd_of_two_eq_zero hn h₂]

end

section

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem range_intCast : Set.range ((↑) : ℤ → R) = {0, 1} := by
  rw [funext CharTwo.intCast_eq_ite, Set.range_ite_const]
  · use 0; simp
  · use 1; simp

end

section

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem range_natCast : Set.range ((↑) : ℕ → R) = {0, 1} := by
  rw [funext CharTwo.natCast_eq_ite, Set.range_ite_const]
  · use 0; simp
  · use 1; simp

end

section

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem sub_eq_add (x y : R) : x - y = x + y := by rw [sub_eq_add_neg, CharTwo.neg_eq]

end

section

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem two_eq_zero : (2 : R) = 0 := by
  rw [← Nat.cast_two, CharP.cast_eq_zero]

end
