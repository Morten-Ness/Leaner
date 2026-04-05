import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

variable {γ : Type u₁} [AddCommMonoid γ]

variable (φ : ∀ i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

theorem toAddMonoid.unique (f : ⨁ i, β i) : ψ f = DirectSum.toAddMonoid (fun i => ψ.comp (DirectSum.of β i)) f := by
  congr
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` applies DirectSum.addHom_ext' here, which isn't what we want.
  apply DFinsupp.addHom_ext'
  intro
  simp [DirectSum.toAddMonoid]
  rfl

