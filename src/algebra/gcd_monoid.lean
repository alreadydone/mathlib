import algebra.associated
import data.nat.basic
import data.int.gcd
import algebra.euclidean_domain
import algebra.gcd_domain
import data.polynomial

variable (α : Type*)

local infix ` ~ᵤ ` : 50 := associated

class gcd_monoid [comm_monoid α] :=
(gcd : α → α → α)
(lcm : α → α → α)
(coprime : α → α → Prop)
(gcd_dvd_left   : ∀a b, gcd a b ∣ a)
(gcd_dvd_right  : ∀a b, gcd a b ∣ b)
(dvd_gcd        : ∀{a b c}, a ∣ c → a ∣ b → a ∣ gcd c b)
(gcd_mul_lcm    : ∀a b, gcd a b * lcm a b ~ᵤ (a * b))
(coprime_iff : ∀{a b}, coprime a b ↔ is_unit (gcd a b))

variable {α}

instance nat.gcd_monoid : gcd_monoid ℕ :=
{ gcd := nat.gcd,
  lcm := nat.lcm,
  coprime := nat.coprime,
  gcd_dvd_left := nat.gcd_dvd_left,
  gcd_dvd_right := nat.gcd_dvd_right,
  dvd_gcd := λ a b c, nat.dvd_gcd,
  gcd_mul_lcm := λ a b, (nat.gcd_mul_lcm a b).symm ▸ associated.refl (a * b),
  coprime_iff := by {
    intros a b, split; intro h, { unfold nat.coprime at h, rw h, apply is_unit_one, },
    rw nat.is_unit_iff at h, apply h,
  } }

instance gcd_domain.gcd_monoid [gcd_domain α] : gcd_monoid α :=
{ coprime := λ a b, gcd a b = 1,
  gcd_mul_lcm := λ a b, by { rw gcd_mul_lcm, apply associated_normalize.symm, },
  coprime_iff := by {
    intros a b, split; intro h, { rw h, apply is_unit_one, },
    cases h, rw [← normalize_gcd, ← h_h, normalize_coe_units],
  },
  .. (infer_instance : gcd_domain α) }

instance euclidean_domain.gcd_monoid [euclidean_domain α] [decidable_eq α] : gcd_monoid α :=
{ gcd := euclidean_domain.gcd,
  lcm := euclidean_domain.lcm,
  coprime := λ a b, is_unit (euclidean_domain.gcd a b),
  gcd_dvd_left := euclidean_domain.gcd_dvd_left,
  gcd_dvd_right := euclidean_domain.gcd_dvd_right,
  dvd_gcd := λ a b c, euclidean_domain.dvd_gcd,
  gcd_mul_lcm := λ a b, (euclidean_domain.gcd_mul_lcm a b).symm ▸ associated.refl (a * b),
  coprime_iff := λ a b, iff.rfl, }
