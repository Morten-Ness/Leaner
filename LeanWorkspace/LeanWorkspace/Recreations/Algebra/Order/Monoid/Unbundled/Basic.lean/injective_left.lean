import Mathlib

variable {α β : Type*}

theorem injective_left [Mul α] [i : @Std.Commutative α (· * ·)] [PartialOrder α] {a : α}
    (ha : MulLECancellable a) :
    Function.Injective (· * a) := fun b c h => MulLECancellable.Injective ha <| by dsimp; rwa [i.comm a, i.comm a]

