import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

variable (mu : N → N → N)

theorem covariant_flip_iff [h : Std.Commutative mu] :
    Covariant N N (flip mu) r ↔ Covariant N N mu r := by unfold flip; simp_rw [h.comm]

