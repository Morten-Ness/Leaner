FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [h : n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + (ofNat(n) : ℕ) • b := by
  have h' : 2 ≤ n := h.1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h'
  induction m with
  | zero =>
      simp [map_add_const, two_nsmul, add_assoc]
  | succ m ih =>
      rw [Nat.add_assoc, ← Nat.succ_eq_add_one, ← Nat.succ_eq_add_one]
      rw [show ofNat (m + 2 + 1) = (ofNat (m + 2) : G) + 1 by simp [Nat.add_assoc]]
      rw [add_assoc, map_add_const, ih]
      simp [add_assoc, add_left_comm, add_comm, nsmul_add]
