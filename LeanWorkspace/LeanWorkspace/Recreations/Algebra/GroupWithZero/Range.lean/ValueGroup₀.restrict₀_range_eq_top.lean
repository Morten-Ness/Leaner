import Mathlib

variable [GroupWithZero A] [GroupWithZero B] [MonoidWithZeroHomClass F A B] {f}

theorem ValueGroup₀.restrict₀_range_eq_top : range (MonoidWithZeroHom.ValueGroup₀.restrict₀ f) = ⊤ := by
  rw [top_eq_univ, range_eq_univ]
  intro x
  match x with
  | 0 => use 0; simp
  | some ⟨u, hu⟩ =>
    change u ∈ (MonoidWithZeroHom.valueGroup f : Set Bˣ) at hu
    rw [← valueMonoid_eq_valueGroup'] at hu
    obtain ⟨v, hv⟩ := hu
    use v
    simp [restrict₀_apply, hv, Units.ne_zero, WithZero.coe]

