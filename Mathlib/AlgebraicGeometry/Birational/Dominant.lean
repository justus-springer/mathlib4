/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
/-!

# Dominant rational maps

TODO

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

namespace Scheme

namespace PartialMap

instance isDominant_restrict_hom (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) : IsDominant (f.restrict U hU hU').hom := by
  dsimp only [restrict_domain, restrict_hom]
  have : IsDominant (X.homOfLE hU') := Opens.isDominant_homOfLE hU hU'
  infer_instance

lemma isDominant_hom_of_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) [H : IsDominant (f.restrict U hU hU').hom] :
    IsDominant f.hom :=
  IsDominant.of_comp (X.homOfLE hU') f.hom (H := H)

lemma isDominant_hom_iff_isDominant_restrict_hom (f : X.PartialMap Y) (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) :
    IsDominant f.hom ↔ IsDominant (f.restrict U hU hU').hom := by
  constructor
  · intro H
    apply isDominant_restrict_hom
  · intro H
    apply isDominant_hom_of_isDominant_restrict_hom (H := H)

lemma isDominant_hom_iff_of_equiv (f g : X.PartialMap Y) (h : f.equiv g) :
    IsDominant f.hom ↔ IsDominant g.hom := by
  obtain ⟨W, hW, hWl, hWr, h⟩ := h
  have e₁ := isDominant_hom_iff_isDominant_restrict_hom f W hW hWl
  have e₂ := isDominant_hom_iff_isDominant_restrict_hom g W hW hWr
  dsimp only [restrict_domain, restrict_hom] at ⊢ e₁ e₂ h
  rw [e₁, h, ← e₂]

end PartialMap

namespace RationalMap

@[mk_iff]
protected class IsDominant (f : X ⤏ Y) : Prop where
  exists_dominant_rep' : ∃ g : X.PartialMap Y, IsDominant g.hom ∧ g.toRationalMap = f

lemma exists_dominant_rep (f : X ⤏ Y) [f.IsDominant] :
    ∃ g : X.PartialMap Y, IsDominant g.hom ∧ g.toRationalMap = f :=
  IsDominant.exists_dominant_rep'

noncomputable def dominantRep (f : X ⤏ Y) [f.IsDominant] : X.PartialMap Y :=
  f.exists_dominant_rep.choose

instance (f : X ⤏ Y) [f.IsDominant] : IsDominant f.dominantRep.hom :=
  f.exists_dominant_rep.choose_spec.1

lemma toRationalMap_dominantRep (f : X ⤏ Y) [f.IsDominant] :
    f.dominantRep.toRationalMap = f :=
  f.exists_dominant_rep.choose_spec.2

lemma IsDominant.of_exists_dominant_rep (f : X ⤏ Y) (g : X.PartialMap Y)
    [IsDominant g.hom] (hg : g.toRationalMap = f) : f.IsDominant :=
  ⟨g, ‹_›, hg⟩

instance (f : X.PartialMap Y) [IsDominant f.hom] : f.toRationalMap.IsDominant :=
  ⟨f, ‹_›, rfl⟩

end RationalMap

lemma PartialMap.isDominant_hom_of_toRationalMap_eq (f : X.PartialMap Y) (g : X ⤏ Y)
    [H : g.IsDominant] (h : f.toRationalMap = g) : IsDominant f.hom := by
  obtain ⟨_, _, rfl⟩ := H
  rwa [isDominant_hom_iff_of_equiv _ _ (toRationalMap_eq_iff.mp h)]

lemma PartialMap.isDominant_hom_of_isDominant_toRationalMap (f : X.PartialMap Y)
    [H : f.toRationalMap.IsDominant] : IsDominant f.hom :=
  isDominant_hom_of_toRationalMap_eq f f.toRationalMap rfl

end Scheme

end AlgebraicGeometry

