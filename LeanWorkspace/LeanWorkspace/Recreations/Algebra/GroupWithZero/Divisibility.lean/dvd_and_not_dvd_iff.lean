import Mathlib

variable {α : Type*}

theorem dvd_and_not_dvd_iff [CommMonoidWithZero α] [IsCancelMulZero α] {x y : α} :
    x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y := ⟨fun ⟨⟨d, hd⟩, hyx⟩ =>
    ⟨fun hx0 => by simp [hx0] at hyx,
      ⟨d, mt isUnit_iff_dvd_one.1 fun ⟨e, he⟩ => hyx ⟨e, by rw [hd, mul_assoc, ← he, mul_one]⟩,
        hd⟩⟩,
    fun ⟨hx0, d, hdu, hdx⟩ =>
    ⟨⟨d, hdx⟩, fun ⟨e, he⟩ =>
      hdu
        (isUnit_of_dvd_one
          ⟨e, mul_left_cancel₀ hx0 <| by conv =>
            lhs
            rw [he, hdx]
            simp [mul_assoc]⟩)⟩⟩

