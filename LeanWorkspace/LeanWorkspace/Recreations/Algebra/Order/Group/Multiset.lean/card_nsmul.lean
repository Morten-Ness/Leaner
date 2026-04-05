import Mathlib

variable {α β : Type*}

theorem card_nsmul (s : Multiset α) (n : ℕ) : card (n • s) = n * card s := Multiset.cardHom.map_nsmul ..

