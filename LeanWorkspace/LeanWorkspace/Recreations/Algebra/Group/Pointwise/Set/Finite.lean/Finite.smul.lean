import Mathlib

variable {F α β γ : Type*}

variable [SMul α β] {s : Set α} {t : Set β}

theorem Finite.smul : s.Finite → t.Finite → (s • t).Finite := Finite.image2 _

