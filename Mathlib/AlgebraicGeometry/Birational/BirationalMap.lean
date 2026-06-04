/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.Birational.Composition
/-!

# Birational maps between schemes

## TODO

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Scheme

structure BirationalMap (X Y : Scheme.{u}) [IrreducibleSpace X] [IrreducibleSpace Y] where
  hom : X ⤏ Y
  [isDominant_hom : hom.IsDominant]
  inv : Y ⤏ X
  [isDominant_inv : inv.IsDominant]
  hom_comp_inv_id : hom.comp inv = .id X
  inv_comp_hom_id : inv.comp hom = .id Y

variable {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]

set_option backward.defeqAttrib.useBackward true in
def PartialIso.toBirationalMap {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X.PartialIso Y) : X.BirationalMap Y where
  hom := f.toRationalMap
  inv := f.symm.toRationalMap 
  hom_comp_inv_id := by
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff]
    refine ⟨f.source, f.dense_source, by simp, by simp, ?_⟩
    sorry
  inv_comp_hom_id := by
    rw [RationalMap.toRationalMap_comp, PartialMap.toRationalMap_eq_iff]
    refine ⟨f.target, f.dense_target, by simp; sorry, by simp, ?_⟩
    sorry

end Scheme

end AlgebraicGeometry
