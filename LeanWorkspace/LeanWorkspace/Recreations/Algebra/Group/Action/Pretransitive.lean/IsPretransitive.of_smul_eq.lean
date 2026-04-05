import Mathlib

variable {M G α β : Type*}

theorem IsPretransitive.of_smul_eq {M N α : Type*} [SMul M α] [SMul N α] [IsPretransitive M α]
    (f : M → N) (hf : ∀ {c : M} {x : α}, f c • x = c • x) : IsPretransitive N α where
  MulAction.exists_smul_eq x y := (MulAction.exists_smul_eq x y).elim fun m h ↦ ⟨f m, hf.trans h⟩

