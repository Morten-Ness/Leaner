FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_ofNat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) • b := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt' (show 1 < n by infer_instance)
  induction m with
  | zero =>
      simp [map_add_const]
  | succ m ih =>
      rw [show ofNat (m + 3) = (1 : G) + ofNat (m + 2) by simp [ofNat_eq_natCast]]
      rw [add_assoc, map_add_const, ih]
      simp [add_nsmul, add_assoc]
