import Mathlib

section

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [Group G]

theorem _root_.injective_iff_map_eq_one' {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 ↔ a = 1 := (injective_iff_map_eq_one f).trans <|
    forall_congr' fun _ => ⟨fun h => ⟨h, fun H => H.symm ▸ map_one f⟩, Iff.mp⟩

end

section

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [Group G]

theorem _root_.injective_iff_map_eq_one {G H} [Group G] [MulOneClass H]
    [FunLike F G H] [MonoidHomClass F G H]
    (f : F) : Function.Injective f ↔ ∀ a, f a = 1 → a = 1 := ⟨fun h _ => (map_eq_one_iff f h).mp, fun h x y hxy =>
    mul_inv_eq_one.1 <| h _ <| by rw [map_mul, hxy, ← map_mul, mul_inv_cancel, map_one]⟩

end

section

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [DivisionCommMonoid α]

theorem invMonoidHom_comp_invMonoidHom : (invMonoidHom (α := α)).comp invMonoidHom = .id _ := by
  ext; simp

end
