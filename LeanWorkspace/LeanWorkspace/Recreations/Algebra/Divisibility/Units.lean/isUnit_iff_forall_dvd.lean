import Mathlib

variable {α : Type*}

variable [CommMonoid α]

theorem isUnit_iff_forall_dvd {x : α} : IsUnit x ↔ ∀ y, x ∣ y := isUnit_iff_dvd_one.trans ⟨fun h _ => h.trans (one_dvd _), fun h => h _⟩

