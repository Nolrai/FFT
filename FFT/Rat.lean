import Mathlib

/-!
# Basics for the Rational Numbers

## Summary

We define a rational number `q` as a structure `{ num, denom, pos, cop }`, where
- `num` is the numerator of `q`,
- `denom` is the denominator of `q`,
- `pos` is a proof that `denom > 0`, and
- `cop` is a proof `num` and `denom` are coprime.

We then define the integral domain structure on `nnℚ` and prove basic lemmas about it.
The definition of the field structure on `nnℚ` will be done in `data.nnRat.basic` once the
`field` class has been defined.

## Main Definitions

- `nnRat` is the structure encoding `nnℚ`.
- `nnRat.mk n d` constructs a nonnegative rational number `q = n / d` from `n d : ℕ`.

## Notations

- `/.` is infix notation for `nnRat.mk`.

## Tags

Rat, rationals, semifield, nnℚ, numerator, denominator, num, denom
-/

/-- `Rat`, or `nnℚ`, is the type of rational numbers. It is defined
  as the set of pairs ⟨n, d⟩ of integers such that `d` is positive and `n` and
  `d` are coprime. This representation is preferred to the quotient
  because without periodic reduction, the numerator and denominator can grow
  exponentially (for example, adding 1/2 to itself repeatedly). -/
structure nnRat := mk' ::
(num : ℕ)
(denom : ℕ)
(pos : 0 < denom)
(cop : num.coprime denom)
notation "nnℚ" => nnRat

namespace nnRat

/-- String representation of a rational numbers, used in `has_repr`, `has_to_string`, and
`has_to_format` instances. -/
protected def repr : nnℚ → Lean.Format
| ⟨n, d, _, _⟩ => if d = 1 then _root_.repr n else
  _root_.repr n ++ "/" ++ _root_.repr d

instance : Repr nnℚ where
  reprPrec q _ := q.repr

instance : ToString nnℚ where
  toString q := toString q.repr

-- instance : Encodable nnℚ := Encodable.of_equiv (Σ n : ℕ, {d : ℕ // 0 < d ∧ n.coprime d})
--   ⟨λ ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, λ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩,
--    λ ⟨a, b, c, d⟩ => rfl, λ⟨a, b, c, d⟩ => rfl⟩

/-- Embed an natural as a rational number -/
instance : OfNat nnℚ n :=
⟨n, 1, Nat.one_pos, Nat.coprime_one_right _⟩

instance : Inhabited nnℚ := ⟨0⟩

lemma ext_iff {p q : nnℚ} : p = q ↔ p.num = q.num ∧ p.denom = q.denom :=
  by 
  cases p
  cases q
  simp

@[ext] lemma ext {p q : nnℚ} (hn : p.num = q.num) (hd : p.denom = q.denom) : p = q :=
nnRat.ext_iff.mpr ⟨hn, hd⟩

lemma mk_pnat_aux1 (n : Int) (dpos: 0 < d) : 0 < d / (n.gcd d) :=
  by
    apply lt_of_lt_of_le Nat.zero_lt_one
    rw [Nat.le_div_iff_mul_le]
    rw [one_mul]
    apply Nat.gcd_le_right _ dpos
    apply Nat.gcd_pos_of_pos_right _ dpos

lemma mk_pnat_aux2 (dpos : 0 < d) : 
  let g  := (n.gcd d : Nat)
  Nat.coprime (n / g) (d / g) := 
    by
    intros _
    exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ dpos)

/-- Form the quotient `n / d` where `n:ℕ` and `d:ℕ+` (not necessarily coprime) -/
def mk_pnat (n : ℕ) : {d // 0 < d} → nnℚ 
| ⟨d, dpos⟩ =>
  let n' := n
  let g := n'.gcd d
  {
    num := n / g
    denom := d / g
    pos := mk_pnat_aux1 n dpos
    cop := mk_pnat_aux2 dpos
  }


/-- Form the quotient `n / d` where `n:ℕ` and `d:ℕ`. In the case `d = 0`, we
  define `n / 0 = 0` by convention. -/
def mk (n : ℕ) (d : ℕ) : nnℚ :=
if d0 : d = 0 then 0 else mk_pnat n ⟨d, Nat.pos_of_ne_zero d0⟩

local infix:70 " /. " => nnRat.mk

theorem mk_pnat_eq (n d h) : mk_pnat n ⟨d, h⟩ = n /. d := by
  simp [mk_pnat, mk]
  have : d ≠ 0 := (Nat.ne_of_lt h).symm
  rw [dif_neg this]
  ext

@[simp] theorem mk_zero (n) : n /. 0 = 0 := rfl

@[simp] theorem zero_mk_pnat (n) : mk_pnat 0 n = 0 := by
  cases n
  case mk n npos =>
  simp only [mk_pnat, Nat.div_self npos, Nat.gcd_zero_left, Nat.zero_div]
  rfl

@[simp] theorem zero_mk (n) : 0 /. n = 0 :=
  by 
  cases n
  all_goals {simp [mk]}

lemma Nat.eq_zero_of_div_gcd_eq_zero {a b : ℕ} : a / a.gcd b = 0 → a = 0 := by
  have ⟨a₀, a₀_def⟩ : a.gcd b ∣ a := by apply Nat.gcd_dvd_left
  have : a / a.gcd b = a.gcd b * a₀ / a.gcd b := by rw [← a₀_def]
  intros h
  rw [this] at h 
  have : 0 ≤ a.gcd b := by 
    apply Nat.zero_le
  rw [le_iff_lt_or_eq] at this
  cases this
  case inl h_pos =>
    rw [Nat.mul_div_cancel_left _ h_pos] at h
    rw [a₀_def, h, Nat.mul_zero]
  case inr h_zero =>
    have : a = 0 ∧ b = 0
    case _ =>
      rw [← Nat.gcd_eq_zero_iff]
      apply h_zero.symm
    apply this.1

lemma mk_pnat_zero : ∀ {b}, mk_pnat a b = 0 → a = 0 := by
  intro ⟨b', h⟩ e
  injection e with e_a e_b
  apply Nat.eq_zero_of_div_gcd_eq_zero e_a

@[simp] theorem mk_eq_zero {a b : ℕ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 :=
  by
  apply Iff.intro 
  case mpr => 
    intro a0
    cases a0
    apply zero_mk
  case mp =>
    intro a0
    rw [mk, dif_neg b0] at a0
    apply mk_pnat_zero a0

theorem mk_ne_zero {a b : ℕ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 := by 
  simp [mk_eq_zero b0]

lemma mk_eq_aux : mk_pnat a ⟨b, hb⟩ = mk_pnat c ⟨d, hd⟩ ↔ a * d = c * b := 
  by
  simp [mk_pnat]
  -- cases b
  -- case zero => cases hb
  -- case succ b =>
  --   cases d
  --   case zero => cases hd
  --   case succ d =>
  --     cases a
  --     case zero =>
  --       simp
  --       apply Iff.intro
  --       case mp =>
  --         intros h
  --         have : c = 0 := Nat.eq_zero_of_div_gcd_eq_zero h.1.symm
  --         cases this
  --         simp
  --       case mpr =>
  --         intros h
  --         have hc : c = 0
  --         case hc =>
  --           have : c = 0 ∨ b.succ = 0 := Nat.eq_zero_of_mul_eq_zero h.symm
  --           cases this
  --           case inl hc => exact hc
  --           case inr bc => cases bc
  --         case _ => simp [hc, Nat.div_self hb, Nat.div_self hd]
  --     case succ a =>
  --       simp


theorem mk_eq : ∀ {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0),
  a /. b = c /. d ↔ a * d = c * b :=
