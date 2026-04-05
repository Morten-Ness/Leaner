import Mathlib

variable {F α β γ : Type*}

variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

theorem image_mul_prod : (fun x : α × α => x.fst * x.snd) '' s ×ˢ t = s * t := image_prod _

