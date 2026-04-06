FAIL
import Mathlib

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x - ofNat(n)) = f x - ofNat(n) • b := by
  rw [show ofNat n = (n : G) by rfl, show ofNat n • b = (n : ℤ) • b by rfl]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    map_zsmul₀ (f := f) (a := x) (n := (-((n : ℤ)))) (b := b)
