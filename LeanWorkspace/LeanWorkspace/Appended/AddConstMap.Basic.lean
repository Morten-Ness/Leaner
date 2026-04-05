import Mathlib

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x + n) = f x + n • b := by
  rw [← AddConstMapClass.map_add_zsmul f x n, zsmul_one]

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x + n) = f x + n • b := by simp [← AddConstMapClass.map_add_nsmul]

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_nsmul [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x + n • a) = f x + n • b := by
  simpa using (AddConstMapClass.semiconj f).iterate_right n x

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_add_ofNat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x + ofNat(n)) = f x + (ofNat(n) : ℕ) • b := AddConstMapClass.map_add_nat' f x n

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_int_add' [AddCommGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℤ) (x : G) : f (↑n + x) = f x + n • b := by
  rw [← AddConstMapClass.map_zsmul_add, zsmul_one]

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nat' [AddMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) : f n = f 0 + n • b := by
  simpa using AddConstMapClass.map_add_nat' f 0 n

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) (x : G) : f (↑n + x) = f x + n • b := by
  simpa using AddConstMapClass.map_nsmul_add f n x

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nsmul_add [AddCommMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, AddConstMapClass.map_add_nsmul]

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_nsmul_const [AddMonoid G] [AddMonoid H] [AddConstMapClass F G H a b]
    (f : F) (n : ℕ) : f (n • a) = f 0 + n • b := by
  simpa using AddConstMapClass.map_add_nsmul f 0 n

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_ofNat_add' [AddCommMonoidWithOne G] [AddMonoid H] [AddConstMapClass F G H 1 b]
    (f : F) (n : ℕ) [n.AtLeastTwo] (x : G) :
    f (ofNat(n) + x) = f x + ofNat(n) • b := AddConstMapClass.map_nat_add' f n x

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) : f (x - a) = f x - b := by
  simpa using AddConstMapClass.map_sub_nsmul f x 1

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_int' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℤ) : f (x - n) = f x - n • b := by
  rw [← AddConstMapClass.map_sub_zsmul, zsmul_one]

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_nat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) : f (x - n) = f x - n • b := by
  simpa using AddConstMapClass.map_sub_nsmul f x n

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_nsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℕ) : f (x - n • a) = f x - n • b := by
  conv_rhs => rw [← sub_add_cancel x (n • a), AddConstMapClass.map_add_nsmul, add_sub_cancel_right]

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_ofNat' [AddGroupWithOne G] [AddGroup H] [AddConstMapClass F G H 1 b]
    (f : F) (x : G) (n : ℕ) [n.AtLeastTwo] :
    f (x - ofNat(n)) = f x - ofNat(n) • b := AddConstMapClass.map_sub_nat' f x n

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_sub_zsmul [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (x : G) (n : ℤ) : f (x - n • a) = f x - n • b := by
  simpa [sub_eq_add_neg] using AddConstMapClass.map_add_zsmul f x (-n)

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_zsmul_add [AddCommGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) (x : G) : f (n • a + x) = f x + n • b := by
  rw [add_comm, AddConstMapClass.map_add_zsmul]

end

section

variable {F G H : Type*} [FunLike F G H] {a : G} {b : H}

theorem map_zsmul_const [AddGroup G] [AddGroup H] [AddConstMapClass F G H a b]
    (f : F) (n : ℤ) : f (n • a) = f 0 + n • b := by
  simpa using AddConstMapClass.map_add_zsmul f 0 n

end
