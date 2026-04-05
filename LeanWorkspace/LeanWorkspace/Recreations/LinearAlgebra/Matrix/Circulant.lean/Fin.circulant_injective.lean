import Mathlib

variable {α β n R : Type*}

theorem Fin.circulant_injective : ∀ n, Function.Injective fun v : Fin n → α => Matrix.circulant v
  | 0 => by simp [Function.Injective]
  | _ + 1 => Matrix.circulant_injective
