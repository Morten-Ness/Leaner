import Mathlib

variable {α β n R : Type*}

theorem circulant_injective [SubtractionMonoid n] :
    Function.Injective (Matrix.circulant : (n → α) → Matrix n n α) := by
  intro v w h
  funext i
  have := congrArg (fun M => M i 0) h
  simpa using this
