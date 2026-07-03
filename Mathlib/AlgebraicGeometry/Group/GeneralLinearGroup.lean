/-
Copyright (c) 2026 Justus Springer, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer, Peiran Wu
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# General linear group as a group scheme

TODO

-/

@[expose] public section

open MvPolynomial
open scoped TensorProduct

namespace GLAlgGroup

universe u

variable (K : Type u) [Field K] (n : ℕ)

/-- det (T_{ij})_(ij) -/
noncomputable abbrev detPolynomial : MvPolynomial (Fin n × Fin n) K :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) K).det

/-- K[T_{ij} | i, j : Fin n]_(det (T_{ij})_(ij)) -/
abbrev Alg : Type u := Localization.Away (detPolynomial K n)

variable {K n} in
noncomputable abbrev ι := algebraMap (MvPolynomial (Fin n × Fin n) K) (Alg K n)

variable {K n} in
lemma isUnit_ι_detPolynomial : IsUnit (ι (detPolynomial K n)) :=
  IsLocalization.Away.algebraMap_isUnit _

abbrev counitAux : MvPolynomial (Fin n × Fin n) K →ₐ[K] K :=
  aeval ((Equiv.curry _ _ _).symm (1 : Matrix (Fin n) (Fin n) K))

@[simp]
lemma Matrix.of_self {m n α : Type*} (M : Matrix m n α) : Matrix.of M = M := rfl

noncomputable def counit : Alg K n →ₐ[K] K :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (detPolynomial K n))
    (f := aeval ((Equiv.curry _ _ _).symm (1 : Matrix (Fin n) (Fin n) K))) <| by
    rintro ⟨y, k, rfl⟩
    simp only [aeval_eq_eval, Equiv.curry_symm_apply, map_pow]
    apply IsUnit.pow
    simp [Matrix.eval_det_mvPolynomialX]

noncomputable abbrev comulAux : MvPolynomial (Fin n × Fin n) K →ₐ[K] Alg K n ⊗[K] Alg K n :=
  aeval fun (i, j) => ∑ k, ι (X (i, k)) ⊗ₜ ι (X (k, j))

noncomputable def comul : Alg K n →ₐ[K] Alg K n ⊗[K] Alg K n :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (detPolynomial K n)) (f := aeval fun (i, j) => ∑ k, ι (X (i, k)) ⊗ₜ ι (X (k, j))) <| by
    rintro ⟨y, k, rfl⟩
    simp only [map_pow]
    apply IsUnit.pow
    have h : (comulAux K n).mapMatrix (.mvPolynomialX (Fin n) (Fin n) K) =
        (Algebra.TensorProduct.includeLeftRingHom.comp ι).mapMatrix
          (.mvPolynomialX (Fin n) (Fin n) K) *
        (Algebra.TensorProduct.includeRight.toRingHom.comp ι).mapMatrix
          (.mvPolynomialX (Fin n) (Fin n) K) := by
      ext i j
      simp [Matrix.mul_apply, comulAux]
    rw [AlgHom.map_det, h, Matrix.det_mul, ← RingHom.map_det, ← RingHom.map_det]
    exact IsUnit.mul
      (isUnit_ι_detPolynomial.map Algebra.TensorProduct.includeLeftRingHom)
      (isUnit_ι_detPolynomial.map Algebra.TensorProduct.includeRight.toRingHom)

noncomputable instance : Bialgebra K (Alg K n) := .ofAlgHom (comul ..) (counit ..)
  sorry
  (by ext ⟨i, j⟩; simp [comul, counit, Algebra.algHom, Matrix.one_apply, TensorProduct.ite_tmul])
  (by ext ⟨i, j⟩; simp [comul, counit, Algebra.algHom, Matrix.one_apply, TensorProduct.tmul_ite])

noncomputable instance : HopfAlgebra K (Alg K n) where
  antipode := sorry
  mul_antipode_rTensor_comul := sorry
  mul_antipode_lTensor_comul := sorry

end GLAlgGroup
