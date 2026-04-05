import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

theorem MonoidHom.comp_id [MulOne M] [MulOne N] (f : M →* N) :
    f.comp (MonoidHom.id M) = f := MonoidHom.ext fun _ => rfl

