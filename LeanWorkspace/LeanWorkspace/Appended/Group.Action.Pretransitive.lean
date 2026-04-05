import Mathlib

section

variable {M G α β : Type*}

variable (M) [SMul M α] [IsPretransitive M α]

theorem IsPretransitive.of_orbit {X : Type*} [Group G] [MulAction G X] {x₀ : X}
    (ha : ∀ x, ∃ g : G, g • x₀ = x) :
    IsPretransitive G X := by
  constructor
  intro x y
  rcases ha x with ⟨g, rfl⟩
  rcases ha y with ⟨h, rfl⟩
  exact ⟨h * g⁻¹, by simp [mul_smul]⟩

end

section

variable {M G α β : Type*}

theorem IsPretransitive.of_smul_eq {M N α : Type*} [SMul M α] [SMul N α] [IsPretransitive M α]
    (f : M → N) (hf : ∀ {c : M} {x : α}, f c • x = c • x) : IsPretransitive N α where
  MulAction.exists_smul_eq x y := (MulAction.exists_smul_eq x y).elim fun m h ↦ ⟨f m, hf.trans h⟩

end

section

variable {M G α β : Type*}

theorem MulAction.IsPretransitive.of_isScalarTower (M : Type*) {N α : Type*} [Monoid N] [SMul M N]
    [MulAction N α] [SMul M α] [IsScalarTower M N α] [IsPretransitive M α] : IsPretransitive N α := of_smul_eq (fun x : M ↦ x • 1) (smul_one_smul N _ _)

end
