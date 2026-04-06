FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n • b := by
  cases n using Int.inductionOn with
  | hz =>
      simp
  | hp n ih =>
      simpa [Int.ofNat_eq_coe, add_assoc, add_left_comm, add_comm, zsmul_intNatEq_natCast_mul] using
        (by
          rw [show x + (n : ℤ) + 1 = (x + (n : ℤ)) + 1 by abel]
          rw [map_add, ih, map_one]
          abel)
  | hn n ih =>
      simpa [Int.negSucc_eq, add_assoc, add_left_comm, add_comm] using
        (by
          rw [show x + Int.negSucc n = (x + (Int.ofNat (n + 1) : ℤ)) + (-1) by
            simp [Int.negSucc_eq, add_assoc, add_left_comm, add_comm]]
          rw [map_add, map_neg_eq_sub, map_one, ih]
          simp [Int.negSucc_eq, add_assoc, add_left_comm, add_comm, sub_eq_add_neg, zsmul_neg]
          abel)
