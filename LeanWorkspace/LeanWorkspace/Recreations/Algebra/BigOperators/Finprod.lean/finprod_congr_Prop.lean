import Mathlib

variable {G M N : Type*} {α β ι : Sort*} [CommMonoid M] [CommMonoid N]

theorem finprod_congr_Prop {p q : Prop} {f : p → M} {g : q → M} (hpq : p = q)
    (hfg : ∀ h : q, f (hpq.mpr h) = g h) : finprod f = finprod g := by
  subst q
  exact finprod_congr hfg

