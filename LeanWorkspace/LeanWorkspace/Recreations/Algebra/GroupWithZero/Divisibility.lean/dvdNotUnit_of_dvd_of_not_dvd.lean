import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem dvdNotUnit_of_dvd_of_not_dvd {a b : α} (hd : a ∣ b) (hnd : ¬b ∣ a) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    exact hnd (dvd_zero _)
  · rcases hd with ⟨c, rfl⟩
    refine ⟨c, ?_, rfl⟩
    rintro ⟨u, rfl⟩
    simp at hnd

