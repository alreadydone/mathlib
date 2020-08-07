/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure_space

/-!
# The product measure space

TODO:

σ-finite measures (is locally finite enough?):
- A measure space (X, B, µ) is σ-finite if X can be expressed as the countable union of sets of
  finite measure

Define product measure
Define finite (and countably infinite) product measure
Fubini's theorem

-/
noncomputable theory
open_locale classical big_operators
open function


namespace set
section
variables {ι : Type*} {α : ι → Type*} {s : set ι} {t : Π i, set (α i)}
@[simp] lemma mem_pi {f : Π i, α i} : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i :=
by refl

@[simp] lemma mem_pi_univ {f : Π i, α i} : f ∈ pi univ t ↔ ∀ i, f i ∈ t i :=
by simp

lemma pi_eq_empty {i : ι} (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ :=
by { ext f, simp only [mem_empty_eq, classical.not_forall, iff_false, mem_pi, classical.not_imp],
     exact ⟨i, hs, by simp [ht]⟩ }

lemma pi_univ_eq_empty {i : ι} (ht : t i = ∅) : pi univ t = ∅ :=
pi_eq_empty (mem_univ i) ht

lemma pi_nonempty_iff : (s.pi t).nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i :=
by simp [classical.skolem, set.nonempty]

lemma pi_univ_nonempty_iff : (pi univ t).nonempty ↔ ∀ i, (t i).nonempty :=
by simp [classical.skolem, set.nonempty]

lemma pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, (α i → false) ∨ (i ∈ s ∧ t i = ∅) :=
begin
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff], push_neg, apply exists_congr, intro i,
  split,
  { intro h, by_cases hα : nonempty (α i),
    { cases hα with x, refine or.inr ⟨(h x).1, by simp [eq_empty_iff_forall_not_mem, h]⟩ },
    { exact or.inl (λ x, hα ⟨x⟩) }},
  { rintro (h|h) x, exfalso, exact h x, simp [h] }
end

lemma pi_univ_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ :=
by simp [← not_nonempty_iff_eq_empty, pi_univ_nonempty_iff]

lemma apply_image_pi {i : ι} (hs : i ∈ s) (ht : (s.pi t).nonempty) :
  (λ f : Π i, α i, f i) '' s.pi t = t i :=
begin
  ext x, rcases ht with ⟨f, hf⟩, split,
  { rintro ⟨g, hg, rfl⟩, exact hg i hs },
  { intro hg, refine ⟨function.update f i x, _, by simp⟩,
    intros j hj, by_cases hji : j = i,
    { subst hji, simp [hg] },
    { simp at hf, simp [hji, hf, hj] }},
end

@[simp] lemma apply_image_pi_univ {i : ι} (ht : (pi univ t).nonempty) :
  (λ f : Π i, α i, f i) '' pi univ t = t i :=
apply_image_pi (mem_univ i) ht

lemma update_preimage_pi {i : ι} {f : Π i, α i} (hi : i ∈ s)
  (hf : ∀ j ∈ s, j ≠ i → f j ∈ t j) : (update f i) ⁻¹' s.pi t = t i :=
begin
  ext x, split,
  { intro h, convert h i hi, simp },
  { intros hx j hj, by_cases h : j = i,
    { cases h, simpa },
    { rw [update_noteq h], exact hf j hj h }}
end

lemma update_preimage_pi_univ {i : ι} {f : Π i, α i} (hf : ∀ j ≠ i, f j ∈ t j) :
  (update f i) ⁻¹' pi univ t = t i :=
update_preimage_pi (mem_univ i) (λ j _, hf j)

end

section
variables {α β : Type*}
-- rename this and set.push_pull'. Ping Patrick Massot
lemma image_inter_preimage {f : α → β} {s : set α} {t : set β} : f '' (s ∩ f ⁻¹' t) = f '' s ∩ t :=
set.push_pull f s t

lemma image_compl_preimage {f : α → β} {s : set α} {t : set β} : f '' (s \ f ⁻¹' t) = f '' s \ t :=
by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]

end
end set
open set

namespace canonically_ordered_semiring
variables {α : Type*} [canonically_ordered_comm_semiring α]

lemma mul_le_mul_left' {b c : α} (h : b ≤ c) (a : α) : a * b ≤ a * c :=
mul_le_mul (le_refl a) h

lemma mul_le_mul_right' {b c : α} (h : b ≤ c) (a : α) : b * a ≤ c * a :=
mul_le_mul h (le_refl a)

end canonically_ordered_semiring

namespace finset
@[to_additive]
lemma prod_split {α β} [decidable_eq α] [comm_monoid β] (s t : finset α) (f : α → β) :
  (∏ x in s, f x) = (∏ x in s ∩ t, f x) * (∏ x in s \ t, f x) :=
by { convert s.prod_piecewise t f f, simp [finset.piecewise] }

@[to_additive]
lemma prod_split_single {α β} [decidable_eq α] [comm_monoid β] {s : finset α} {i : α} (h : i ∈ s)
  (f : α → β) : (∏ x in s, f x) = f i * (∏ x in s \ {i}, f x) :=
by { convert s.prod_split {i} f, simp [h] }

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
lemma prod_add_prod_eq {α β} [comm_semiring β] {s : finset α} {i : α} {f g h : α → β}
  (hi : i ∈ s) (h1 : g i + h i = f i) (h2 : ∀ j ∈ s, j ≠ i → g j = f j)
  (h3 : ∀ j ∈ s, j ≠ i → h j = f j) : ∏ i in s, g i + ∏ i in s, h i = ∏ i in s, f i :=
by { simp_rw [prod_split_single hi, ← h1, right_distrib], congr' 2; apply prod_congr rfl; simpa }

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` is the
  sum of the products of `g` and `h`. -/
lemma prod_univ_add_prod_univ_eq {α β} [fintype α] [comm_semiring β] (i : α) {f g h : α → β}
  (h1 : g i + h i = f i) (h2 : ∀ j ≠ i, g j = f j) (h3 : ∀ j ≠ i, h j = f j) :
  ∏ i, g i + ∏ i, h i = ∏ i, f i :=
prod_add_prod_eq (mem_univ i) h1 (λ j _, h2 j) (λ j _, h3 j)

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `linear_ordered_comm_ring`. -/
lemma prod_add_prod_le {α β} [linear_ordered_comm_ring β] {s : finset α} {i : α} {f g h : α → β}
  (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
  (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i) :
  ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  simp_rw [prod_split_single hi],
  refine le_trans _ (mul_le_mul_of_nonneg_right h2i _),
  { rw [right_distrib],
    apply add_le_add; apply mul_le_mul_of_nonneg_left; try { apply prod_le_prod };
    simp only [and_imp, mem_sdiff, mem_singleton]; intros; apply_assumption; assumption },
  { apply prod_nonneg, simp only [and_imp, mem_sdiff, mem_singleton],
    intros j h1j h2j, refine le_trans (hg j h1j) (hgf j h1j h2j) }
end

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` is at least the sum of the
  products of `g` and `h`. This is the version for `linear_ordered_comm_ring`. -/
lemma prod_univ_add_prod_univ_le {α β} [fintype α] [linear_ordered_comm_ring β] (i : α)
  {f g h : α → β} (h2i : g i + h i ≤ f i) (hgf : ∀ j ≠ i, g j ≤ f j)
  (hhf : ∀ j ≠ i, h j ≤ f j) (hg : ∀ i, 0 ≤ g i) (hh : ∀ i, 0 ≤ h i) :
  ∏ i, g i + ∏ i, h i ≤ ∏ i, f i :=
prod_add_prod_le (mem_univ i) h2i (λ j _, hgf j) (λ j _, hhf j) (λ j _, hg j) (λ j _, hh j)

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` over `s` is at least the
  sum of the products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`.
-/
lemma prod_add_prod_le' {α β} [canonically_ordered_comm_semiring β] {s : finset α} {i : α}
  {f g h : α → β} (hi : i ∈ s) (h2i : g i + h i ≤ f i) (hgf : ∀ j ∈ s, j ≠ i → g j ≤ f j)
  (hhf : ∀ j ∈ s, j ≠ i → h j ≤ f j) : ∏ i in s, g i + ∏ i in s, h i ≤ ∏ i in s, f i :=
begin
  simp_rw [prod_split_single hi],
  refine le_trans _ (canonically_ordered_semiring.mul_le_mul_right' h2i _),
  rw [right_distrib],
  apply add_le_add; apply canonically_ordered_semiring.mul_le_mul_left'; apply prod_le_prod';
  simp only [and_imp, mem_sdiff, mem_singleton]; intros; apply_assumption; assumption
end

/-- If `g, h ≤ f` and `g i + h i ≤ f i`, then the product of `f` is at least the sum of the
  products of `g` and `h`. This is the version for `canonically_ordered_comm_semiring`. -/
lemma prod_univ_add_prod_univ_le' {α β} [fintype α] [canonically_ordered_comm_semiring β] (i : α)
  {f g h : α → β} (h2i : g i + h i ≤ f i) (hgf : ∀ j ≠ i, g j ≤ f j)
  (hhf : ∀ j ≠ i, h j ≤ f j) : ∏ i, g i + ∏ i, h i ≤ ∏ i, f i :=
prod_add_prod_le' (mem_univ i) h2i (λ j _, hgf j) (λ j _, hhf j)

end finset

namespace measure_theory

section
variables {α : Type*} {β : α → Type*} [Πa, measurable_space (β a)]

lemma is_measurable.pi [encodable α] {t : Π i, set (β i)} (hs : ∀ i, is_measurable (t i)) :
  is_measurable (pi univ t) :=
by { convert is_measurable.Inter (λ i, measurable_pi_apply _ (hs i) : _), simp [pi_def] }

lemma measurable_update (f : Π (a : α), β a) {i : α} : measurable (update f i) :=
begin
  apply measurable_pi_lambda,
  intro j, by_cases hj : j = i,
  { cases hj, convert measurable_id, ext, simp },
  simp_rw [update_noteq hj], apply measurable_const,
end

lemma is_measurable_pi_of_nonempty [encodable α] {t : Π i, set (β i)} (h : (pi univ t).nonempty) :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) :=
begin
  rcases h with ⟨f, hf⟩, refine ⟨λ hst i, _, is_measurable.pi⟩,
  convert measurable_update f hst, rw [update_preimage_pi_univ], exact λ j _, hf j (mem_univ j)
end

lemma is_measurable_pi [encodable α] {t : Π i, set (β i)} :
  is_measurable (pi univ t) ↔ ∀ i, is_measurable (t i) ∨ ∃ i, t i = ∅ :=
begin
  cases (pi univ t).eq_empty_or_nonempty with h h,
  { have := pi_univ_eq_empty_iff.mp h, simp [h, pi_univ_eq_empty_iff.mp h] },
  { simp [←not_nonempty_iff_eq_empty, pi_univ_nonempty_iff.mp h, is_measurable_pi_of_nonempty h] }
end

end

variables {ι : Type*} [fintype ι] {α : ι → Type*} {m : ∀ i, outer_measure (α i)}

/-- An upper bound for the measure in a product space.
  It is defined to be the product of the measures of all its projections.
  For boxes it should be equal to the correct measure
  It is explicitly defined to be 0 for the empty set (which only matters if `ι` is empty. -/
def pi_premeasure (m : ∀ i, outer_measure (α i)) (s : set (Π i, α i)) : ennreal :=
if s = ∅ then 0 else ∏ i, m i ((λ f : Π i, α i, f i) '' s)

@[simp] lemma pi_premeasure_empty : pi_premeasure m ∅ = 0 :=
by simp [pi_premeasure]

@[simp] lemma pi_premeasure_nonempty {s : set (Π i, α i)} (hs : s.nonempty) :
  pi_premeasure m s = ∏ i, m i ((λ f : Π i, α i, f i) '' s) :=
by simp [pi_premeasure, hs, ← not_nonempty_iff_eq_empty]

lemma pi_premeasure_le_prod {s : set (Π i, α i)} :
  pi_premeasure m s ≤ ∏ i, m i ((λ f : Π i, α i, f i) '' s) :=
by { cases s.eq_empty_or_nonempty with h h; simp [h, le_refl] }

lemma pi_premeasure_pi (s : Π i, set (α i)) (hs : (pi univ s).nonempty) :
  pi_premeasure m (pi univ s) = finset.univ.prod (λ i, m i (s i)) :=
by simp [hs]

/-- The outer measure on a finite product of of types. -/
def outer_measure.pi (m : ∀ i, outer_measure (α i)) : outer_measure (Π i, α i) :=
outer_measure.of_function (pi_premeasure m) pi_premeasure_empty

namespace measure

variables [∀ i, measurable_space (α i)] (μ : ∀ i, measure (α i))

protected lemma caratheodory {α} [measurable_space α] (μ : measure α) {s t : set α}
  (hs : is_measurable s) : μ (t ∩ s) + μ (t \ s) = μ t :=
(le_to_outer_measure_caratheodory μ s hs t).symm

lemma pi_caratheodory :
  measurable_space.pi ≤ (outer_measure.pi (λ i, (μ i).to_outer_measure)).caratheodory :=
begin
  refine supr_le _, intros i s hs,
  simp [measurable_space.comap] at hs, rcases hs with ⟨s, hs, rfl⟩,
  apply outer_measure.of_function_caratheodory,
  intro t, cases t.eq_empty_or_nonempty with h h, { simp [h] },
  rw [pi_premeasure_nonempty h],
  refine le_trans (add_le_add pi_premeasure_le_prod pi_premeasure_le_prod) _,
  refine finset.prod_univ_add_prod_univ_le' i _ _ _,
  { simp [image_inter_preimage, image_compl_preimage, (μ i).caratheodory hs, le_refl] },
  { intros j hj, apply outer_measure.mono', apply image_subset, apply inter_subset_left },
  { intros j hj, apply outer_measure.mono', apply image_subset, apply diff_subset }
end

protected def pi : measure (Π i, α i) :=
outer_measure.to_measure (outer_measure.pi (λ i, (μ i).to_outer_measure)) (pi_caratheodory μ)

lemma pi_pi (s : Π i, set (α i)) (hs : (pi univ s).nonempty) :
  measure.pi μ (pi univ s) = finset.univ.prod (λ i, μ i (s i)) :=
begin
  sorry
end

def measure.pi2 : measurable_space (Π i, α i) := by apply_instance

#print measure.pi2
#print measurable_space.pi

end measure

end measure_theory
