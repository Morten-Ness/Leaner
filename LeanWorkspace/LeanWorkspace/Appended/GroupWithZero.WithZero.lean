import Mathlib

section

variable {α β γ : Type*}

variable [Group α]

theorem coe_unitsWithZeroEquiv_eq_units_val (γ : (WithZero α)ˣ) :
    ↑(WithZero.unitsWithZeroEquiv γ) = γ.val := by
  simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]

end

section

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_comp (f : α →* β) (g : β →* γ) : WithZero.map' (g.comp f) = (WithZero.map' g).comp (WithZero.map' f) := MonoidWithZeroHom.ext fun x => (WithZero.map'_map' f g x).symm

end

section

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulOneClass β] [MulOneClass γ]

theorem map'_injective_iff {f : α →* β} : Function.Injective (WithZero.map' f) ↔ Function.Injective f := by
  simp [Function.Injective, WithZero.forall]

alias ⟨_, map'_injective⟩ := map'_injective_iff

end

section

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulZeroOneClass β]

theorem monoidWithZeroHom_ext ⦃f g : WithZero α →*₀ β⦄
    (h : f.toMonoidHom.comp WithZero.coeMonoidHom = g.toMonoidHom.comp WithZero.coeMonoidHom) :
    f = g := DFunLike.ext _ _ fun
    | 0 => (map_zero f).trans (map_zero g).symm
    | (g : α) => DFunLike.congr_fun h g

end
