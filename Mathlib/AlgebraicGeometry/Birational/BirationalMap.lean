/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Birational.RationalMap
/-!

# Birational maps between schemes

TODO

-/

@[expose] public section

universe u v

open CategoryTheory hiding Quotient

namespace AlgebraicGeometry

namespace Scheme

variable {X Y Z S : Scheme.{u}}

/--
A partial isomorphism from `X` to `Y` (`X.BipartialMap Y`) is... TODO
-/
structure PartialIso (X Y : Scheme.{u}) where
  /-- The source of definition of a partial iso. -/
  source : X.Opens
  dense_source : Dense (source : Set X)
  /-- The target of a partial iso. -/
  target : Y.Opens
  dense_target : Dense (target : Set Y)
  /-- The underlying isomorphism of a partial iso. -/
  iso : source.toScheme ≅ target.toScheme

namespace PartialIso

variable (S) in
abbrev IsOver (f : X.PartialIso Y) [X.Over S] [Y.Over S] : Prop :=
  f.iso.hom.IsOver S

lemma ext_iff (f g : X.PartialIso Y) :
    f = g ↔ ∃ (e : f.source = g.source) (e' : g.target = f.target),
      f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e' := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U₁, hU₁, U₂, hU₂, f⟩ := f
    obtain ⟨V₁, hV₁, V₂, hU₂, g⟩ := g
    simp only [forall_exists_index]
    rintro rfl rfl e
    simpa using e

@[ext]
lemma ext (f g : X.PartialIso Y) (e : f.source = g.source) (e' : g.target = f.target)
    (H : f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e') : f = g := by
  rw [ext_iff]
  exact ⟨e, e', H⟩

variable (X) in
@[simps]
def refl : X.PartialIso X where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := Iso.refl _

instance [X.Over S] : (refl X).IsOver S := by
  simp only [Hom.isOver_iff, refl_source, refl_target, refl_iso, Iso.refl_hom, Category.id_comp]
  rfl

@[symm, simps]
def symm (f : X.PartialIso Y) : Y.PartialIso X where
  source := f.target
  dense_source := f.dense_target
  target := f.source
  dense_target := f.dense_source
  iso := f.iso.symm

set_option backward.isDefEq.respectTransparency false in
instance [X.Over S] [Y.Over S] (f : X.PartialIso Y) [f.IsOver S] :
    f.symm.IsOver S :=
  OverClass.instHomIsOverInvOfHom S

@[simps]
noncomputable def trans' (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source) :
    X.PartialIso Z where
  source := f.source
  dense_source := f.dense_source
  target := g.target
  dense_target := g.dense_target
  iso := f.iso ≪≫ Y.isoOfEq e ≪≫ g.iso

@[simps]
noncomputable def restrictSource (f : X.PartialIso Y) (U : Opens X) (hU : Dense (U : Set X))
    (hU' : U ≤ f.source) : X.PartialIso Y where
  source := U
  dense_source := hU
  target := f.target.ι ''ᵁ f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U
  dense_target :=
    have := PartialMap.Opens.isDominant_ι f.dense_target
    f.target.ι.denseRange.dense_image f.target.ι.continuous <|
      f.iso.hom.denseRange.dense_image f.iso.hom.continuous <|
        hU.preimage f.source.ι.isOpenEmbedding.isOpenMap
  iso := (Opens.isoOfLE hU').symm ≪≫
    (f.iso.hom.isoImage (f.source.ι ⁻¹ᵁ U)) ≪≫
    (f.target.ι.isoImage (f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U))

noncomputable def restrictTarget (f : X.PartialIso Y) (U : Opens Y) (hU : Dense (U : Set Y))
    (hU' : U ≤ f.target) : X.PartialIso Y where
  source := sorry
  dense_source := sorry
  target := U
  dense_target := hU
  iso := sorry
 
@[simps]
def toPartialMap (f : X.PartialIso Y) : X.PartialMap Y where
  domain := f.source
  dense_domain := f.dense_source
  hom := f.iso.hom ≫ f.target.ι

abbrev toRationalMap (f : X.PartialIso Y) : X ⤏ Y := f.toPartialMap.toRationalMap

@[simps]
noncomputable def _root_.CategoryTheory.Iso.toPartialIso (f : X ≅ Y) : X.PartialIso Y where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := X.topIso ≪≫ f ≪≫ Y.topIso.symm

end PartialIso

variable (X Y) in
def Birational : Prop := Nonempty (PartialIso X Y)

noncomputable def Birational.partialIso (h : Birational X Y) : PartialIso X Y :=
  Classical.choice h

variable (X) in
lemma Birational.refl : Birational X X :=
  ⟨.refl X⟩

lemma Birational.symm (h : Birational X Y) : Birational Y X :=
  ⟨h.partialIso.symm⟩

variable (X Y S) in
def BirationalOver [X.Over S] [Y.Over S] : Prop :=
  ∃ f : PartialIso X Y, f.IsOver S

noncomputable def BirationalOver.partialIso [X.Over S] [Y.Over S] (h : BirationalOver X Y S) :=
  h.choose

instance BirationalOver.partialIso_isOver [X.Over S] [Y.Over S] (h : BirationalOver X Y S) :
    h.partialIso.IsOver S :=
  h.choose_spec

variable (X) in
lemma BirationalOver.refl [X.Over S] : BirationalOver X X S :=
  ⟨.refl X, inferInstance⟩

lemma BirationalOver.symm [X.Over S] [Y.Over S] (h : BirationalOver X Y S) :
    BirationalOver Y X S :=
  ⟨h.partialIso.symm, inferInstance⟩

variable (X S) in
@[mk_iff]
class IsRationalOver [X.Over S] : Prop where
  exists_birationalOver_affineSpace : ∃ n, BirationalOver X 𝔸(Fin n; S) S

instance (n : ℕ) : IsRationalOver 𝔸(Fin n; S) S where
  exists_birationalOver_affineSpace := ⟨n, .refl _⟩

end Scheme

end AlgebraicGeometry
