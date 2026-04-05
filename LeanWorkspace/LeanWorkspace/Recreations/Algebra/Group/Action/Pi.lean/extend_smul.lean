import Mathlib

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

theorem extend_smul {M α β : Type*} [SMul M β] (r : M) (f : ι → α) (g : ι → β) (e : α → β) :
    extend f (r • g) (r • e) = r • extend f g e := by
  funext x
  classical
  simp only [extend_def, Pi.smul_apply]
  split_ifs <;> rfl

