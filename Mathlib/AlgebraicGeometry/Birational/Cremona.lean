/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.BirationalMap

/-!
# The Cremona group

## TODO

-/

@[expose] public section

universe u

namespace AlgebraicGeometry

abbrev Cremona (n : Type u) (S : Scheme.{u}) [IrreducibleSpace S] :=
  Scheme.BirationalMapOver S 𝔸(n; S) 𝔸(n; S)

noncomputable example (n : Type u) (S : Scheme.{u}) [IrreducibleSpace S] : Group (Cremona n S) :=
  inferInstance

end AlgebraicGeometry




