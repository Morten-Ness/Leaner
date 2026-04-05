import Mathlib

section

variable {F α M N G : Type*}

variable [Monoid M] [Monoid N] [EquivLike F M N] [MulEquivClass F M N] (f : F) {x : M}

theorem MulEquiv.isUnit_map : IsUnit (f x) ↔ IsUnit x where
  mp hx := by
    simpa using hx.map <| MonoidHom.mk ⟨EquivLike.inv f, EquivLike.injective f <| by simp⟩
      fun x y ↦ EquivLike.injective f <| by simp
  mpr := .map f

end

section

variable {F α M N G : Type*}

theorem toUnits_val_apply {G : Type*} [Group G] (x : Gˣ) : toUnits (x : G) = x := by
  simp_rw [MulEquiv.apply_eq_iff_symm_apply, toUnits_symm_apply]

end
