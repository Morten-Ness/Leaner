import Mathlib

variable {R : Type u} [Ring R] (M : ModuleCat.{v} R)

theorem toKernelSubobject_arrow {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker f.hom) :
    (kernelSubobject f).arrow (ModuleCat.toKernelSubobject x) = x.1 := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10959): the whole proof was just `simp [ModuleCat.toKernelSubobject]`.
  simp [ModuleCat.toKernelSubobject, -hom_comp, ← CategoryTheory.comp_apply]

