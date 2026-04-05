import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_inj {c : α} : toIcoMod hp c a = toIcoMod hp c b ↔ a ≡ b [PMOD p] := by
  rw [toIcoMod_eq_toIcoMod, AddCommGroup.modEq_iff_zsmul']

alias ⟨_, AddCommGroup.ModEq.toIcoMod_eq_toIcoMod⟩ := toIcoMod_inj

