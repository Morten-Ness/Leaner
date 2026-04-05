import Mathlib

variable {A : Type*}

theorem _root_.Units.isStrictlyPositive_iff [LE A] [Monoid A] [Zero A] {a : Aˣ} :
    IsStrictlyPositive (a : A) ↔ (0 : A) ≤ a := ⟨fun h => h.nonneg, fun h => IsStrictlyPositive.iff_of_unital.mp ⟨h, a.isUnit⟩⟩

