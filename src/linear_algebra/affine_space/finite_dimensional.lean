/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import linear_algebra.affine_space.basic
import linear_algebra.finite_dimensional

noncomputable theory
open_locale big_operators
open_locale classical

/-!
# Finite-dimensional subspaces of affine spaces.

This file provides a few results relating to finite-dimensional
subspaces of affine spaces.

-/

open add_torsor

namespace affine_space

variables (k : Type*) (V : Type*) {P : Type*} [field k] [add_comm_group V] [module k V]
          [affine_space k V P]
variables {ι : Type*}

/-- The `vector_span` of a finite set is finite-dimensional. -/
lemma finite_dimensional_vector_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (vector_span k V s) :=
finite_dimensional.span_of_finite k $ vsub_set_finite_of_finite V h

/-- The direction of the affine span of a finite set is
finite-dimensional. -/
lemma finite_dimensional_direction_affine_span_of_finite {s : set P} (h : set.finite s) :
  finite_dimensional k (affine_span k V s).direction :=
(direction_affine_span k V s).symm ▸ finite_dimensional_vector_span_of_finite k V h

/-- The direction of the affine span of a family indexed by a
`fintype` is finite-dimensional. -/
instance finite_dimensional_direction_affine_span_of_fintype [fintype ι] (p : ι → P) :
  finite_dimensional k (affine_span k V (set.range p)).direction :=
finite_dimensional_direction_affine_span_of_finite k V (set.finite_range _)

end affine_space
