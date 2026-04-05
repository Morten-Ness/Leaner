import Mathlib

variable {A : Type u} [Ring A] {ι : Type w} [DecidableEq ι]
  (relations : ι → Relations.{w₀, w₁} A)
  {M : ι → Type v} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]

variable {N : Type v} [AddCommGroup N] [Module A N]
  (pres : Presentation A N) (ι : Type w) [DecidableEq ι] [DecidableEq N]

theorem finsupp_var (i : ι) (g : pres.G) :
    (Module.Presentation.finsupp pres ι).var ⟨i, g⟩ = Finsupp.single i (pres.var g) := by
  apply (finsuppLequivDFinsupp A).injective
  erw [(finsuppLequivDFinsupp A).apply_symm_apply]
  rw [Module.Presentation.directSum_var, finsuppLequivDFinsupp_apply_apply, Finsupp.toDFinsupp_single]
  rfl

