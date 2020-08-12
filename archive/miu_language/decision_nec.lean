/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import .basic
import data.nat.modeq
import tactic.ring

/-!
# Decision procedure - necessary condition

We introduce a condition `decstr` and show that if a string `en` is `derivable`, then `decstr en`
holds.

Using this, we give a negative answer to the question: is `"MU"` derivable?
-/

namespace miu

open miu_atom

/-!
### Numerical condition on the `I` count

Suppose `st : miustr`. Then `count I st` is the number of `I`s in `st. We'll show, if
`derivable st`, then `count I st` must be 1 or 2 modulo 3. To do this, it suffices to show that if
the `en : miustr` is derived from `st`, then `count I en` moudulo 3 is either equal to or is twice
`count I st`, modulo 3.
-/


open nat
open list

/--
Given `st en : miustr`, the relation `count_equiv_or_equiv_two_mul_mod3 st en` holds if `st` and
`en` either have equal `count I`, modulo 3, or `count I en` is twice `count I st`, modulo 3.
 -/
def count_equiv_or_equiv_two_mul_mod3 (st en : miustr) : Prop :=
  let a := (count I st) in
  let b := (count I en) in
  b ≡ a [MOD 3] ∨ b ≡ 2*a [MOD 3]

example : count_equiv_or_equiv_two_mul_mod3 "II" "MIUI" :=
  or.inl rfl

example : count_equiv_or_equiv_two_mul_mod3 "IUIM" "MI" :=
  or.inr rfl

/-!
We show the `count I`, mod 3, stays the same or is multiplied by 2 under the rules of inference.
-/

open nat

/-!
Now we show that the `count I` of a derivable string is 1 or 2 modulo 3.
-/



/-!
We start with a general result about natural numbers.
-/

lemma inherit_mod3 {a b : ℕ} (h1 : a % 3 = 1 ∨ a % 3 = 2)
  (h2 : b % 3 = a % 3 ∨  b % 3 = (2 * a % 3)) :
    b % 3 = 1 ∨ b % 3 = 2 :=
begin
  cases h2, {
    rw h2, exact h1,
  }, {
    cases h1, {
      right, simpa [h2,mul_mod,h1],
    }, {
      left, simpa [h2,mul_mod,h1],
    }
  }
end


/--
`count_equiv_one_or_two_mod3_of_derivable` shows any derivable string must have an `count I` that
is 1 or 2 modulo 3.
-/
theorem count_equiv_one_or_two_mod3_of_derivable (en : miustr): derivable en →
  (count I en) % 3 = 1 ∨ (count I en) % 3 = 2:=
begin
  intro h,
  induction h,
    left,
    apply mod_def,
    any_goals {apply inherit_mod3 h_ih},
      left, simp only [count_append], refl,
      right, simp [count,count_append], ring,
      left, simp [count_append,count I,refl], ring,
      left, simp [count_append,count I,refl],
end

/--
Using the above theorem, we solve the MU puzzle, showing that `"MU"` is not derivable.
-/
theorem not_derivable_mu : ¬(derivable "MU") :=
begin
  intro h,
  cases (count_equiv_one_or_two_mod3_of_derivable _ h);
    contradiction,
end


/-!
### Condition on `M`

That solves the MU puzzle, but we'll proceed by demonstrating the other necessary condition for a
string to be derivable, namely that the string must start with an M and contain no M in its tail.
-/


/--
`goodm xs` holds if `xs : miustr` begins with `M` and contains no `M` in its tail.
-/
@[derive decidable_pred]
def goodm (xs : miustr) : Prop :=
  list.head xs = M ∧ ¬(M ∈ list.tail xs)

/-!
Example usage
-/

lemma goodmi : goodm [M,I] :=
begin
  split,
    { refl },
  rw [tail,mem_singleton], trivial
end

/-!
We'll show, for each `i` from 1 to 4, that if `en` follows by rule `i` from `st` and if
`goodm st` holds, then so does `goodm en`.
-/

open list

lemma tail_append_singleton_of_ne_nil {a : miu_atom} {as : miustr} (h₁ : as ≠ nil) :
  tail (as ++ [a]) = tail as ++ [a] :=
begin
  induction as with x xs hxs,
    { contradiction, },
  rw [tail,cons_append,tail],
end

lemma exists_cons_of_ne_nil {as : miustr} (h : as ≠ nil) : ∃ c cs, as = c :: cs :=
begin
  induction as with x xs hxs,
    { contradiction, },
  use [x,xs],
end

lemma goodm_of_rule1 (xs : miustr) (h₁ : derivable (xs ++ [I])) (h₂ : goodm (xs ++ [I]))
  : goodm (xs ++ [I,U]) :=
begin
  cases h₂ with mhead nmtail,
  have : xs ≠ nil,
    intro h, rw h at *, rw [nil_append,head] at mhead, contradiction,
  split, {
    rwa [head_append] at *; exact this,
  },
  change [I,U] with [I] ++ [U],
  rw [←append_assoc,tail_append_singleton_of_ne_nil],
    { simp [mem_append,nmtail], },
  exact append_ne_nil_of_ne_nil_left _ _ this,
end


lemma goodm_of_rule2 (xs : miustr) (h₁ : derivable (M :: xs))
  (h₂ : goodm (M :: xs)) : goodm (M :: xs ++ xs) :=
begin
  split,
    { refl, },
  cases h₂ with mhead mtail,
  contrapose! mtail,
  rw cons_append at mtail,
  rw [tail] at *,
  exact (or_self _).mp (mem_append.mp mtail),
end

lemma goodm_of_rule3  (as bs : miustr) (h₁ : derivable (as ++ [I,I,I] ++ bs))
  (h₂ : goodm (as ++ [I,I,I] ++ bs)) : goodm (as ++ U :: bs) :=
begin
  cases h₂ with mhead nmtail,
  have k : as ≠ nil , {
    intro h, rw h at mhead, rw [nil_append] at mhead, contradiction,
  },
  split, {
    rw [append_assoc,head_append] at *, {
      rw head_append, { exact mhead, },
      exact k,
    }, exact k,
  },
  contrapose! nmtail,
  rcases (exists_cons_of_ne_nil k) with ⟨x,xs,rfl⟩,
  simp [cons_append, tail,mem_append] at *, exact nmtail,
end


/-!
 The proof of the next lemma is identical to the previous proof!
-/

lemma goodm_of_rule4  (as bs : miustr) (h₁ : derivable (as ++ [U,U] ++ bs))
  (h₂ : goodm (as ++ [U,U] ++ bs)) : goodm (as ++ bs) :=
begin
  cases h₂ with mhead nmtail,
  have k : as ≠ nil , {
    intro h, rw h at mhead, rw [nil_append] at mhead, contradiction,
  },
  split, {
    rw [append_assoc,head_append] at *, {
      rw head_append, { exact mhead, },
      exact k,
    }, exact k,
  },
  contrapose! nmtail,
  rcases (exists_cons_of_ne_nil k) with ⟨x,xs,rfl⟩,
  simp [cons_append, tail,mem_append] at *, exact nmtail,
end


/--
Any derivable string must begin with `M` and have no `M` in its tail.
-/
theorem goodm_of_derivable (en : miustr): derivable en →
  goodm en:=
begin
  intro h,
  induction h,
    exact goodmi,
  apply goodm_of_rule1; assumption,
  apply goodm_of_rule2; assumption,
  apply goodm_of_rule3; assumption,
  apply goodm_of_rule4; assumption,
end

/-!
We put togther our two conditions to give one condition `decstr`. Once we've proved sufficiency of
this condition, we'll have proved that checking the condition is a decision procedure.
-/

/--
`decstr en` is the condition that `count I en` is 1 or 2 modulo 3, that `en` starts with `M`, and
that `en` contains no `M` in its tail.
-/
@[derive decidable_pred]
def decstr (en : miustr) :=
  goodm en ∧ ((count I en) % 3 = 1 ∨ (count I en) % 3 = 2)

/--
Suppose `en : miustr`. If `en` is `derivable`, then the condition `decstr en` holds.
-/
theorem decstr_of_der {en : miustr} : derivable en → decstr en :=
begin
  intro h,
  split,
    exact goodm_of_derivable en h,
    exact count_equiv_one_or_two_mod3_of_derivable en h
end

end miu