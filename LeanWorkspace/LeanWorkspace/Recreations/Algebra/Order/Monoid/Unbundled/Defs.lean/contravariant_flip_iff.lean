import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem contravariant_flip_iff [h : Std.Commutative mu] :
    Contravariant N N (flip mu) r ↔ Contravariant N N mu r := by unfold flip; simp_rw [h.comm]

