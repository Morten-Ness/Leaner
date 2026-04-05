import Mathlib

variable {G M R K : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R] [ExistsAddOfLE R]
  {x y : R}

theorem exists_nat_pow_near (hx : 1 ≤ x) (hy : 1 < y) : ∃ n : ℕ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
  have h : ∃ n : ℕ, x < y ^ n := pow_unbounded_of_one_lt _ hy
  classical exact
      let n := Nat.find h
      have hn : x < y ^ n := Nat.find_spec h
      have hnp : 0 < n :=
        pos_iff_ne_zero.2 fun hn0 => by rw [hn0, pow_zero] at hn; exact not_le_of_gt hn hx
      have hnsp : Nat.pred n + 1 = n := Nat.succ_pred_eq_of_pos hnp
      have hltn : Nat.pred n < n := Nat.pred_lt (ne_of_gt hnp)
      ⟨Nat.pred n, le_of_not_gt (Nat.find_min h hltn), by rwa [hnsp]⟩

