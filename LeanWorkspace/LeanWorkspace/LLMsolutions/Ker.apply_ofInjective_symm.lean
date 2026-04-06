import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem apply_ofInjective_symm {f : G →* N} (hf : Function.Injective f) (x : f.range) :
    f ((MonoidHom.ofInjective hf).symm x) = x := by
  exact congrArg Subtype.val ((MonoidHom.ofInjective hf).apply_symm_apply x)
