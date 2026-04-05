import Mathlib

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem ModEq.symm (h : a ≡ b [PMOD p]) : b ≡ a [PMOD p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  exact ⟨n, m, h.symm⟩

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem ModEq.trans (hab : a ≡ b [PMOD p]) (hbc : b ≡ c [PMOD p]) :
    a ≡ c [PMOD p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases hab with ⟨m, n, hab⟩
  rcases hbc with ⟨k, l, hbc⟩
  use k + m, n + l
  rw [add_nsmul, add_assoc, hab, add_nsmul, add_assoc, ← hbc, add_left_comm]

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add (hab : a ≡ b [PMOD p]) (hcd : c ≡ d [PMOD p]) :
    a + c ≡ b + d [PMOD p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases hab with ⟨k, l, hab⟩
  rcases hcd with ⟨m, n, hcd⟩
  use k + m, l + n
  rw [add_nsmul, add_add_add_comm, hab, hcd, add_nsmul, add_add_add_comm]

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_left (c : M) (h : a ≡ b [PMOD p]) : c + a ≡ c + b [PMOD p] := AddCommGroup.ModEq.add AddCommGroup.modEq_rfl h

end

section

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_left_cancel' (c : M) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] := AddCommGroup.modEq_rfl.add_left_cancel

end

section

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_modEq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] := by
  simpa using AddCommGroup.ModEq.add_iff_left (AddCommGroup.modEq_refl a) (d := 0)

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_nsmul_modEq (n : ℕ) : a + n • p ≡ a [PMOD p] := AddCommGroup.modEq_iff_nsmul.mpr ⟨0, n, by simp [add_comm]⟩

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem add_right (c : M) (h : a ≡ b [PMOD p]) : a + c ≡ b + c [PMOD p] := AddCommGroup.ModEq.add h AddCommGroup.modEq_rfl

end

section

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_right_cancel' (c : M) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] := AddCommGroup.modEq_rfl.add_right_cancel

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem add_zsmul_modEq (z : ℤ) : a + z • p ≡ a [PMOD p] := AddCommGroup.modEq_iff_zsmul.mpr ⟨-z, by simp⟩

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem map {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (h : a ≡ b [PMOD p]) : f a ≡ f b [PMOD f p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases h with ⟨m, n, h⟩
  use m, n
  simpa using congr(f $h)

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem map_modEq_iff {N F : Type*} [AddCommMonoid N] [FunLike F M N] [AddMonoidHomClass F M N]
    (f : F) (hf : Function.Injective f) : f a ≡ f b [PMOD f p] ↔ a ≡ b [PMOD p] := by
  simp only [AddCommGroup.modEq_iff_nsmul, ← map_nsmul, ← map_add, hf.eq_iff]

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_eq_add_zsmul : a ≡ b [PMOD p] ↔ ∃ z : ℤ, b = a + z • p := by
  simp_rw [AddCommGroup.modEq_iff_zsmul', sub_eq_iff_eq_add']

-- this roughly matches `Int.modEq_zero_iff_dvd`

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_zsmul' : a ≡ b [PMOD p] ↔ ∃ m : ℤ, b - a = m • p := by
  simp only [AddCommGroup.modEq_iff_zsmul, eq_comm]

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_iff_zsmul : a ≡ b [PMOD p] ↔ ∃ m : ℤ, m • p = b - a := by
  rw [AddCommGroup.modEq_iff_nsmul]
  constructor
  · rintro ⟨m, n, h⟩
    use m - n
    rw [sub_zsmul, ← sub_eq_add_neg, sub_eq_sub_iff_add_eq_add, add_comm b]
    exact mod_cast h
  · rintro ⟨m, h⟩
    use m.toNat, (-m).toNat
    rwa [add_comm _ b, ← sub_eq_sub_iff_add_eq_add, ← natCast_zsmul, ← natCast_zsmul,
      sub_eq_add_neg, ← sub_zsmul, m.toNat_sub_toNat_neg]

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_sub_iff_add_modEq' : a ≡ b - c [PMOD p] ↔ c + a ≡ b [PMOD p] := by
  simp [AddCommGroup.modEq_iff_zsmul', sub_sub]

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_sub_iff_add_modEq : a ≡ b - c [PMOD p] ↔ a + c ≡ b [PMOD p] := AddCommGroup.modEq_sub_iff_add_modEq'.trans <| by rw [add_comm]

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem modEq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [AddCommGroup.modEq_iff_nsmul]

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem modEq_zero_iff_eq_zsmul : a ≡ 0 [PMOD p] ↔ ∃ z : ℤ, a = z • p := by
  rw [AddCommGroup.modEq_comm, AddCommGroup.modEq_iff_eq_add_zsmul]
  simp_rw [zero_add]

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem not_modEq_iff_ne_add_zsmul : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  rw [AddCommGroup.modEq_iff_eq_add_zsmul, not_exists]

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem nsmul {n : ℕ} (h : a ≡ b [PMOD p]) : n • a ≡ n • b [PMOD n • p] := by
  rw [AddCommGroup.modEq_iff_nsmul] at *
  rcases h with ⟨k, l, h⟩
  use k, l
  rw [← mul_nsmul, mul_nsmul', ← nsmul_add, h, nsmul_add, ← mul_nsmul, mul_nsmul']

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem nsmul_add_modEq (n : ℕ) : n • p + a ≡ a [PMOD p] := AddCommGroup.modEq_iff_nsmul.mpr ⟨0, n, by simp⟩

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem of_nsmul {n : ℕ} : a ≡ b [PMOD n • p] → a ≡ b [PMOD p] := fun ⟨k, l, h⟩ =>
  ⟨k * n, l * n, by simpa [mul_nsmul']⟩

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem of_zsmul (h : a ≡ b [PMOD z • p]) : a ≡ b [PMOD p] := by
  rw [AddCommGroup.modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  simp [← h, ← mul_zsmul]

end

section

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem self_modEq_zero : p ≡ 0 [PMOD p] := AddCommGroup.modEq_iff_nsmul.mpr ⟨0, 1, by simp [one_nsmul]⟩

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_left_cancel' (c : G) : c - a ≡ c - b [PMOD p] → a ≡ b [PMOD p] := AddCommGroup.modEq_rfl.sub_left_cancel

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_modEq_iff_modEq_add' : a - b ≡ c [PMOD p] ↔ a ≡ b + c [PMOD p] := AddCommGroup.modEq_comm.trans <| AddCommGroup.modEq_sub_iff_add_modEq'.trans AddCommGroup.modEq_comm

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_modEq_iff_modEq_add : a - b ≡ c [PMOD p] ↔ a ≡ c + b [PMOD p] := AddCommGroup.modEq_comm.trans <| AddCommGroup.modEq_sub_iff_add_modEq.trans AddCommGroup.modEq_comm

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_modEq_zero : a - b ≡ 0 [PMOD p] ↔ a ≡ b [PMOD p] := by simp [AddCommGroup.sub_modEq_iff_modEq_add]

-- this matches `Int.modEq_iff_add_fac`

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem sub_right_cancel' (c : G) : a - c ≡ b - c [PMOD p] → a ≡ b [PMOD p] := AddCommGroup.modEq_rfl.sub_right_cancel

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul (h : a ≡ b [PMOD p]) : z • a ≡ z • b [PMOD z • p] := by
  rw [AddCommGroup.modEq_iff_zsmul] at *
  rcases h with ⟨m, h⟩
  use m
  rw [← zsmul_sub, ← h, ← mul_zsmul, ← mul_zsmul']

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul_add_modEq (z : ℤ) : z • p + a ≡ a [PMOD p] := AddCommGroup.modEq_iff_zsmul.mpr ⟨-z, by simp⟩

end

section

variable {G : Type*} [AddCommGroup G] {p a a₁ a₂ b b₁ b₂ c : G} {n : ℕ} {z : ℤ}

theorem zsmul_modEq_zero (z : ℤ) : z • p ≡ 0 [PMOD p] := AddCommGroup.modEq_iff_zsmul.mpr ⟨-z, by simp⟩

end
