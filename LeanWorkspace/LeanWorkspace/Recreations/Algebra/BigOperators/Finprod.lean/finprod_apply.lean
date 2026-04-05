import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_apply {α ι : Type*} {f : ι → α → N} (hf : HasFiniteMulSupport f) (a : α) :
    (∏ᶠ i, f i) a = ∏ᶠ i, f i a := by
  classical
  have hf' : HasFiniteMulSupport fun i ↦ f i a := by fun_prop (disch := simp)
  simp only [finprod_def, dif_pos, hf, hf', Finset.prod_apply]
  symm
  apply Finset.prod_subset <;> aesop

