import Mathlib

variable {G H : Type*} [Mul G] [Mul H] {A B : Finset G} {a0 b0 : G}

theorem mulHom_image_iff [DecidableEq H] (f : G →ₙ* H) (hf : Function.Injective f) :
    UniqueMul (A.image f) (B.image f) (f a0) (f b0) ↔ UniqueMul A B a0 b0 := ⟨of_mulHom_image f fun _ _ _ _ _ ↦ .imp (hf ·) (hf ·), fun h _ _ ↦ by
    simp_rw [Finset.mem_image]
    rintro ⟨a, aA, rfl⟩ ⟨b, bB, rfl⟩ ab
    simp_rw [← map_mul, hf.eq_iff] at ab ⊢
    exact h aA bB ab⟩

