import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

theorem IsInternal.addSubmonoid_iSup_eq_top {M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (A : ι → AddSubmonoid M) (h : DirectSum.IsInternal A) : iSup A = ⊤ := by
  rw [AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom, AddMonoidHom.mrange_eq_top]
  exact Function.Bijective.surjective h

