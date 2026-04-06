FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_int_add' [AddCommGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n • b := by
  rw [Int.induction_on n]
  · simp
  · intro z hz
    calc
      f ((↑z.succ : G) + x)
          = f (((↑z : G) + 1) + x) := by simp
      _ = f ((↑z : G) + (1 + x)) := by abel
      _ = f (1 + x) + z • b := by simpa using hz (1 + x)
      _ = (f x + b) + z • b := by simpa [map_add, add_comm, add_left_comm, add_assoc, one_nsmul]
      _ = f x + (z • b + b) := by abel
      _ = f x + (Int.succ z) • b := by simp [Int.succ_eq_add_one, add_comm]
  · intro z hz
    calc
      f ((↑(z - 1) : G) + x)
          = f ((↑z : G) + (-1 + x)) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = f (-1 + x) + z • b := by simpa using hz (-1 + x)
      _ = (f x + (-b)) + z • b := by
            have h := map_add (f := f) (-1 : G) x
            simpa [show (-1 : G) = -((1 : G)) by simp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
              one_nsmul] using h
      _ = f x + (z • b - b) := by abel
      _ = f x + (z - 1) • b := by simp [sub_eq_add_neg]
