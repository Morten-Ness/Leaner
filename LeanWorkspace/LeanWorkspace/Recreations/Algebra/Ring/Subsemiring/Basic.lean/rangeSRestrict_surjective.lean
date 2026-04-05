import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {s : Subsemiring R}

variable {σR σS : Type*}

variable [SetLike σR R] [SetLike σS S] [SubsemiringClass σR R] [SubsemiringClass σS S]

theorem rangeSRestrict_surjective (f : R →+* S) : Function.Surjective f.rangeSRestrict := fun ⟨_, hy⟩ =>
  let ⟨x, hx⟩ := RingHom.mem_rangeS.mp hy
  ⟨x, Subtype.ext hx⟩

