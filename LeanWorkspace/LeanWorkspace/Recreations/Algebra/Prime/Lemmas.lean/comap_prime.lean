import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M]

variable [CommMonoidWithZero N] {F : Type*} {G : Type*} [FunLike F M N]

variable [MonoidWithZeroHomClass F M N] [FunLike G N M] [MulHomClass G N M]

variable (f : F) (g : G) {p : M}

theorem comap_prime (hinv : ∀ a, g (f a : N) = a) (hp : Prime (f p)) : Prime p := ⟨fun h => hp.1 <| by simp [h], fun h => hp.2.1 <| h.map f, fun a b h => by
    refine
        (hp.2.2 (f a) (f b) <| by
              convert map_dvd f h
              simp).imp
          ?_ ?_ <;>
      · intro h
        convert ← map_dvd g h <;> apply hinv⟩

