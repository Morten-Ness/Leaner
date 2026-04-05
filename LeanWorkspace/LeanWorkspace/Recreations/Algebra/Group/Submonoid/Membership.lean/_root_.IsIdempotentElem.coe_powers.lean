import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem Submonoid.coe_powers _root_.IsIdempotentElem {a : M} (ha : IsIdempotentElem a) :
    (Submonoid.powers a : Set M) = {1, a} := let S : Submonoid M :=
  { carrier := {1, a},
    mul_mem' := by
      rintro _ _ (rfl | rfl) (rfl | rfl)
      · rw [one_mul]; exact .inl rfl
      · rw [one_mul]; exact .inr rfl
      · rw [mul_one]; exact .inr rfl
      · rw [ha]; exact .inr rfl
    one_mem' := .inl rfl }
  suffices Submonoid.powers a = S from congr_arg _ this
  le_antisymm (Submonoid.powers_le.mpr <| .inr rfl)
    (by rintro _ (rfl | rfl); exacts [one_mem _, Submonoid.mem_powers _])

