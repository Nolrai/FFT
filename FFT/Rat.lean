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

@[simp] theorem mk_eq_zero {a b : ℕ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 :=
by
  apply Iff.intro 
  case mpr => 
    intro a0
    cases a0
    apply zero_mk
  case mp =>
    intro a0
    have : ∀ {a b}, mk_pnat a b = 0 → a = 0 := by
      intro a ⟨b, h⟩ e
      injection e with e
      
end

theorem mk_ne_zero {a b : ℕ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
(mk_eq_zero b0).not

theorem mk_eq : ∀ {a b c d : ℕ} (hb : b ≠ 0) (hd : d ≠ 0),
  a /. b = c /. d ↔ a * d = c * b :=
suffices ∀ a b c d hb hd, mk_pnat a ⟨b, hb⟩ = mk_pnat c ⟨d, hd⟩ ↔ a * d = c * b,
begin
  intros, cases b with b b; simp [mk, mk_nat, Nat.succ_pnat],
  simp [mt (congr_arg int.of_nat) hb],
  all_goals
  { cases d with d d; simp [mk, mk_nat, Nat.succ_pnat],
    simp [mt (congr_arg int.of_nat) hd],
    all_goals { rw this, try {refl} } },
  { change a * ↑(d.succ) = -c * ↑b ↔ a * -(d.succ) = c * b,
    constructor; intro h; apply neg_injective; simpa [left_distrib, neg_add_eq_iff_eq_add,
      eq_neg_iff_add_eq_zero, neg_eq_iff_add_eq_zero] using h },
  { change -a * ↑d = c * b.succ ↔ a * d = c * -b.succ,
    constructor; intro h; apply neg_injective; simpa [left_distrib, eq_comm] using h },
  { change -a * d.succ = -c * b.succ ↔ a * -d.succ = c * -b.succ,
    simp [left_distrib, sub_eq_add_neg], cc }
end,
begin
  intros, simp [mk_pnat], constructor; intro h,
  { cases h with ha hb,
    have ha,
    { have dv := @gcd_abs_dvd_left,
      have := int.eq_mul_of_div_eq_right dv ha,
      rw ← int.mul_div_assoc _ dv at this,
      exact int.eq_mul_of_div_eq_left (dv.mul_left _) this.symm },
    have hb,
    { have dv := λ {a b}, Nat.gcd_dvd_right (int a) b,
      have := Nat.eq_mul_of_div_eq_right dv hb,
      rw ← Nat.mul_div_assoc _ dv at this,
      exact Nat.eq_mul_of_div_eq_left (dv.mul_left _) this.symm },
    have m0 : (a.gcd b * c.gcd d : ℕ) ≠ 0,
    { refine int.coe_nat_ne_zero.2 (ne_of_gt _),
      apply mul_pos; apply Nat.gcd_pos_of_pos_right; assumption },
    apply mul_right_cancel₀ m0,
    simpa [mul_comm, mul_left_comm] using
      congr (congr_arg (*) ha.symm) (congr_arg coe hb) },
  { suffices : ∀ a c, a * d = c * b →
      a / a.gcd b = c / c.gcd d ∧ b / a.gcd b = d / c.gcd d,
    { cases this a c
        (by simpa [int.nat_abs_mul] using congr_arg int h) with h₁ h₂,
      have hs := congr_arg int.sign h,
      simp [int.sign_eq_one_of_pos (int.coe_nat_lt.2 hb),
            int.sign_eq_one_of_pos (int.coe_nat_lt.2 hd)] at hs,
      conv in a { rw ← int.sign_mul_nat_abs a },
      conv in c { rw ← int.sign_mul_nat_abs c },
      rw [int.mul_div_assoc, int.mul_div_assoc],
      exact ⟨congr (congr_arg (*) hs) (congr_arg coe h₁), h₂⟩,
      all_goals { exact int.coe_nat_dvd.2 (Nat.gcd_dvd_left _ _) } },
    intros a c h,
    suffices bd : b / a.gcd b = d / c.gcd d,
    { refine ⟨_, bd⟩,
      apply Nat.eq_of_mul_eq_mul_left hb,
      rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), mul_comm,
          Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), bd,
          ← Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), h, mul_comm,
          Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _)] },
    suffices : ∀ {a c : ℕ} (b>0) (d>0),
      a * d = c * b → b / a.gcd b ≤ d / c.gcd d,
    { exact le_antisymm (this _ hb _ hd h) (this _ hd _ hb h.symm) },
    intros a c b hb d hd h,
    have gb0 := Nat.gcd_pos_of_pos_right a hb,
    have gd0 := Nat.gcd_pos_of_pos_right c hd,
    apply Nat.le_of_dvd,
    apply (Nat.le_div_iff_mul_le gd0).2,
    simp, apply Nat.le_of_dvd hd (Nat.gcd_dvd_right _ _),
    apply (Nat.coprime_div_gcd_div_gcd gb0).symm.dvd_of_dvd_mul_left,
    refine ⟨c / c.gcd d, _⟩,
    rw [← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _),
        ← Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)],
    apply congr_arg (/ c.gcd d),
    rw [mul_comm, ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _),
        mul_comm, h, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), mul_comm] }
end

@[simp] theorem div_mk_div_cancel_left {a b c : ℕ} (c0 : c ≠ 0) :
  (a * c) /. (b * c) = a /. b :=
begin
  by_cases b0 : b = 0, { subst b0, simp },
  apply (mk_eq (mul_ne_zero b0 c0) b0).2, simp [mul_comm, mul_assoc]
end

@[simp] theorem num_denom : ∀ {a : nnℚ}, a.num /. a.denom = a
| ⟨n, d, h, (c:_=1)⟩ := show mk_nat n d = _,
  by simp [mk_nat, ne_of_gt h, mk_pnat, c]

theorem num_denom' {n d h c} : (⟨n, d, h, c⟩ : nnℚ) = n /. d := num_denom.symm

theorem of_int_eq_mk (z : ℕ) : of_int z = z /. 1 := num_denom'

/-- Define a (dependent) function or prove `∀ r : nnℚ, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_eliminator] def {u} num_denom_cases_on {C : nnℚ → Sort u}
   : ∀ (a : nnℚ) (H : ∀ n d, 0 < d → (int n).coprime d → C (n /. d)), C a
| ⟨n, d, h, c⟩ H := by rw num_denom'; exact H n d h c

/-- Define a (dependent) function or prove `∀ r : nnℚ, p r` by dealing with rational
numbers of the form `n /. d` with `d ≠ 0`. -/
@[elab_as_eliminator] def {u} num_denom_cases_on' {C : nnℚ → Sort u}
   (a : nnℚ) (H : ∀ (n:ℕ) (d:ℕ), d ≠ 0 → C (n /. d)) : C a :=
num_denom_cases_on a $ λ n d h c, H n d h.ne'

theorem num_dvd (a) {b : ℕ} (b0 : b ≠ 0) : (a /. b).num ∣ a :=
begin
  cases e : a /. b with n d h c,
  rw [nnRat.num_denom', nnRat.mk_eq b0
    (ne_of_gt (int.coe_nat_pos.2 h))] at e,
  refine (int.nat_abs_dvd.1 $ int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $
    c.dvd_of_dvd_mul_right _),
  have := congr_arg int e,
  simp only [int.nat_abs_mul, int.nat_abs_of_nat] at this, simp [this]
end

theorem denom_dvd (a b : ℕ) : ((a /. b).denom : ℕ) ∣ b :=
begin
  by_cases b0 : b = 0, {simp [b0]},
  cases e : a /. b with n d h c,
  rw [num_denom', mk_eq b0 (ne_of_gt (int.coe_nat_pos.2 h))] at e,
  refine (int.dvd_nat_abs.1 $ int.coe_nat_dvd.2 $ c.symm.dvd_of_dvd_mul_left _),
  rw [← int.nat_abs_mul, ← int.coe_nat_dvd, int.dvd_nat_abs, ← e], simp
end

/-- Addition of rational numbers. Use `(+)` instead. -/
protected def add : nnℚ → nnℚ → nnℚ
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := mk_pnat (n₁ * d₂ + n₂ * d₁) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : has_add nnℚ := ⟨nnRat.add⟩

theorem lift_binop_eq (f : nnℚ → nnℚ → nnℚ) (f₁ : ℕ → ℕ → ℕ → ℕ → ℕ) (f₂ : ℕ → ℕ → ℕ → ℕ → ℕ)
  (fv : ∀ {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂},
    f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
  (f0 : ∀ {n₁ d₁ n₂ d₂} (d₁0 : d₁ ≠ 0) (d₂0 : d₂ ≠ 0), f₂ n₁ d₁ n₂ d₂ ≠ 0)
  (a b c d : ℕ) (b0 : b ≠ 0) (d0 : d ≠ 0)
  (H : ∀ {n₁ d₁ n₂ d₂} (h₁ : a * d₁ = n₁ * b) (h₂ : c * d₂ = n₂ * d),
       f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
  f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d :=
begin
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  generalize hc : c /. d = x, cases x with n₂ d₂ h₂ c₂, rw num_denom' at hc,
  rw fv,
  have d₁0 := ne_of_gt (int.coe_nat_lt.2 h₁),
  have d₂0 := ne_of_gt (int.coe_nat_lt.2 h₂),
  exact (mk_eq (f0 d₁0 d₂0) (f0 b0 d0)).2 (H ((mk_eq b0 d₁0).1 ha) ((mk_eq d0 d₂0).1 hc))
end

@[simp] theorem add_def {a b c d : ℕ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  a /. b + c /. d = (a * d + c * b) /. (b * d) :=
begin
  apply lift_binop_eq nnRat.add; intros; try {assumption},
  { apply mk_pnat_eq },
  { apply mul_ne_zero d₁0 d₂0 },
  calc (n₁ * d₂ + n₂ * d₁) * (b * d) =
          (n₁ * b) * d₂ * d + (n₂ * d) * (d₁ * b) : by simp [mul_add, mul_comm, mul_left_comm]
    ... = (a * d₁) * d₂ * d + (c * d₂) * (d₁ * b) : by rw [h₁, h₂]
    ... = (a * d + c * b) * (d₁ * d₂)             : by simp [mul_add, mul_comm, mul_left_comm]
end

/-- Negation of rational numbers. Use `-r` instead. -/
protected def neg (r : nnℚ) : nnℚ :=
⟨-r.num, r.denom, r.pos, by simp [r.cop]⟩

instance : has_neg nnℚ := ⟨nnRat.neg⟩

@[simp] theorem neg_def {a b : ℕ} : -(a /. b) = -a /. b :=
begin
  by_cases b0 :  b = 0, { subst b0, simp, refl },
  generalize ha : a /. b = x, cases x with n₁ d₁ h₁ c₁, rw num_denom' at ha,
  show nnRat.mk' _ _ _ _ = _, rw num_denom',
  have d0 := ne_of_gt (int.coe_nat_lt.2 h₁),
  apply (mk_eq d0 b0).2, have h₁ := (mk_eq b0 d0).1 ha,
  simp only [neg_mul, congr_arg has_neg.neg h₁]
end

@[simp] lemma mk_neg_denom (n d : ℕ) : n /. -d = -n /. d :=
begin
  by_cases hd : d = 0;
  simp [nnRat.mk_eq, hd]
end

/-- Multiplication of rational numbers. Use `(*)` instead. -/
protected def mul : nnℚ → nnℚ → nnℚ
| ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ := mk_pnat (n₁ * n₂) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : has_mul nnℚ := ⟨nnRat.mul⟩

@[simp] theorem mul_def {a b c d : ℕ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  (a /. b) * (c /. d) = (a * c) /. (b * d) :=
begin
  apply lift_binop_eq nnRat.mul; intros; try {assumption},
  { apply mk_pnat_eq },
  { apply mul_ne_zero d₁0 d₂0 },
  cc
end

/-- Inverse rational number. Use `r⁻¹` instead. -/
protected def inv : nnℚ → nnℚ
| ⟨(n+1:ℕ), d, h, c⟩ := ⟨d, n+1, n.succ_pos, c.symm⟩
| ⟨0, d, h, c⟩ := 0
| ⟨-[1+ n], d, h, c⟩ := ⟨-d, n+1, n.succ_pos, Nat.coprime.symm $ by simp; exact c⟩

instance : has_inv nnℚ := ⟨nnRat.inv⟩
instance : has_div nnℚ := ⟨λ a b, a * b⁻¹⟩

@[simp] theorem inv_def {a b : ℕ} : (a /. b)⁻¹ = b /. a :=
begin
  by_cases a0 : a = 0, { subst a0, simp, refl },
  by_cases b0 : b = 0, { subst b0, simp, refl },
  generalize ha : a /. b = x, cases x with n d h c, rw num_denom' at ha,
  refine eq.trans (_ : nnRat.inv ⟨n, d, h, c⟩ = d /. n) _,
  { cases n with n; [cases n with n, skip],
    { refl },
    { change int.of_nat n.succ with (n+1:ℕ),
      unfold nnRat.inv, rw num_denom' },
    { unfold nnRat.inv, rw num_denom', refl } },
  have n0 : n ≠ 0,
  { rintro rfl,
    rw [nnRat.zero_mk, mk_eq_zero b0] at ha,
    exact a0 ha },
  have d0 := ne_of_gt (int.coe_nat_lt.2 h),
  have ha := (mk_eq b0 d0).1 ha,
  apply (mk_eq n0 a0).2,
  cc
end

variables (a b c : nnℚ)

protected theorem add_zero : a + 0 = a :=
num_denom_cases_on' a $ λ n d h,
by rw [← zero_mk d]; simp [h, -zero_mk]

protected theorem zero_add : 0 + a = a :=
num_denom_cases_on' a $ λ n d h,
by rw [← zero_mk d]; simp [h, -zero_mk]

protected theorem add_comm : a + b = b + a :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
by simp [h₁, h₂]; cc

protected theorem add_assoc : a + b + c = a + (b + c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero, mul_add, mul_comm, mul_left_comm, add_left_comm, add_assoc]

protected theorem add_left_neg : -a + a = 0 :=
num_denom_cases_on' a $ λ n d h,
by simp [h]

@[simp] lemma mk_zero_one : 0 /. 1 = 0 :=
show mk_pnat _ _ = _, by { rw mk_pnat, simp, refl }

@[simp] lemma mk_one_one : 1 /. 1 = 1 :=
show mk_pnat _ _ = _, by { rw mk_pnat, simp, refl }

@[simp] lemma mk_neg_one_one : (-1) /. 1 = -1 :=
show mk_pnat _ _ = _, by { rw mk_pnat, simp, refl }

protected theorem mul_one : a * 1 = a :=
num_denom_cases_on' a $ λ n d h,
by { rw ← mk_one_one, simp [h, -mk_one_one] }

protected theorem one_mul : 1 * a = a :=
num_denom_cases_on' a $ λ n d h,
by { rw ← mk_one_one, simp [h, -mk_one_one] }

protected theorem mul_comm : a * b = b * a :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
by simp [h₁, h₂, mul_comm]

protected theorem mul_assoc : a * b * c = a * (b * c) :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero, mul_comm, mul_left_comm]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
num_denom_cases_on' a $ λ n₁ d₁ h₁,
num_denom_cases_on' b $ λ n₂ d₂ h₂,
num_denom_cases_on' c $ λ n₃ d₃ h₃,
by simp [h₁, h₂, h₃, mul_ne_zero];
   refine (div_mk_div_cancel_left (int.coe_nat_ne_zero.2 h₃)).symm.trans _;
   simp [mul_add, mul_comm, mul_assoc, mul_left_comm]

protected theorem mul_add : a * (b + c) = a * b + a * c :=
by rw [nnRat.mul_comm, nnRat.add_mul, nnRat.mul_comm, nnRat.mul_comm c a]

protected theorem zero_ne_one : 0 ≠ (1:nnℚ) :=
by { rw [ne_comm, ← mk_one_one, mk_ne_zero one_ne_zero], exact one_ne_zero }

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
num_denom_cases_on' a $ λ n d h a0,
have n0 : n ≠ 0, from mt (by { rintro rfl, simp }) a0,
by simpa [h, n0, mul_comm] using @div_mk_div_cancel_left 1 1 _ n0

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
eq.trans (nnRat.mul_comm _ _) (nnRat.mul_inv_cancel _ h)

instance : decidable_eq nnℚ := by tactic.mk_dec_eq_instance

/-! At this point in the import hierarchy we have not defined the `field` typeclass.
Instead we'll instantiate `comm_ring` and `comm_group_with_zero` at this point.
The `nnRat.field` instance and any field-specific lemmas can be found in `data.nnRat.basic`.
-/

instance : comm_ring nnℚ :=
{ zero             := 0,
  add              := (+),
  neg              := has_neg.neg,
  one              := 1,
  mul              := (*),
  zero_add         := nnRat.zero_add,
  add_zero         := nnRat.add_zero,
  add_comm         := nnRat.add_comm,
  add_assoc        := nnRat.add_assoc,
  add_left_neg     := nnRat.add_left_neg,
  mul_one          := nnRat.mul_one,
  one_mul          := nnRat.one_mul,
  mul_comm         := nnRat.mul_comm,
  mul_assoc        := nnRat.mul_assoc,
  left_distrib     := nnRat.mul_add,
  right_distrib    := nnRat.add_mul,
  nat_cast         := λ n, nnRat.of_int n,
  nat_cast_zero    := rfl,
  nat_cast_succ    := λ n, show of_int _ = of_int _ + 1,
    by simp only [of_int_eq_mk, add_def one_ne_zero one_ne_zero, ← mk_one_one]; simp }

instance : comm_group_with_zero nnℚ :=
{ zero := 0,
  one := 1,
  mul := (*),
  inv := has_inv.inv,
  div := (/),
  exists_pair_ne   := ⟨0, 1, nnRat.zero_ne_one⟩,
  inv_zero := rfl,
  mul_inv_cancel := nnRat.mul_inv_cancel,
  mul_zero := mul_zero,
  zero_mul := zero_mul,
  .. nnRat.comm_ring }

instance : is_domain nnℚ :=
{ .. nnRat.comm_group_with_zero,
  .. (infer_instance : no_zero_divisors nnℚ) }

/- Extra instances to short-circuit type class resolution -/
-- TODO(Mario): this instance slows down data.real.basic
instance : nontrivial nnℚ         := by apply_instance
--instance : ring nnℚ             := by apply_instance
instance : comm_semiring nnℚ      := by apply_instance
instance : semiring nnℚ           := by apply_instance
instance : add_comm_group nnℚ     := by apply_instance
instance : add_group nnℚ          := by apply_instance
instance : add_comm_monoid nnℚ    := by apply_instance
instance : add_monoid nnℚ         := by apply_instance
instance : add_left_cancel_semigroup nnℚ := by apply_instance
instance : add_right_cancel_semigroup nnℚ := by apply_instance
instance : add_comm_semigroup nnℚ := by apply_instance
instance : add_semigroup nnℚ      := by apply_instance
instance : comm_monoid nnℚ        := by apply_instance
instance : monoid nnℚ             := by apply_instance
instance : comm_semigroup nnℚ     := by apply_instance
instance : semigroup nnℚ          := by apply_instance

theorem sub_def {a b c d : ℕ} (b0 : b ≠ 0) (d0 : d ≠ 0) :
  a /. b - c /. d = (a * d - c * b) /. (b * d) :=
by simp [b0, d0, sub_eq_add_neg]

@[simp] lemma denom_neg_eq_denom (q : nnℚ) : (-q).denom = q.denom := rfl

@[simp] lemma num_neg_eq_neg_num (q : nnℚ) : (-q).num = -(q.num) := rfl

@[simp] lemma num_zero : nnRat.num 0 = 0 := rfl

@[simp] lemma denom_zero : nnRat.denom 0 = 1 := rfl

lemma zero_of_num_zero {q : nnℚ} (hq : q.num = 0) : q = 0 :=
have q = q.num /. q.denom, from num_denom.symm,
by simpa [hq]

lemma zero_iff_num_zero {q : nnℚ} : q = 0 ↔ q.num = 0 :=
⟨λ _, by simp *, zero_of_num_zero⟩

lemma num_ne_zero_of_ne_zero {q : nnℚ} (h : q ≠ 0) : q.num ≠ 0 :=
assume : q.num = 0,
h $ zero_of_num_zero this

@[simp] lemma num_one : (1 : nnℚ).num = 1 := rfl

@[simp] lemma denom_one : (1 : nnℚ).denom = 1 := rfl

lemma denom_ne_zero (q : nnℚ) : q.denom ≠ 0 :=
ne_of_gt q.pos

lemma eq_iff_mul_eq_mul {p q : nnℚ} : p = q ↔ p.num * q.denom = q.num * p.denom :=
begin
  conv { to_lhs, rw [← @num_denom p, ← @num_denom q] },
  apply nnRat.mk_eq; rw [← Nat.cast_zero, ne, int.coe_nat_eq_coe_nat_iff]; apply denom_ne_zero,
end

lemma mk_num_ne_zero_of_ne_zero {q : nnℚ} {n d : ℕ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 :=
assume : n = 0,
hq $ by simpa [this] using hqnd

lemma mk_denom_ne_zero_of_ne_zero {q : nnℚ} {n d : ℕ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 :=
assume : d = 0,
hq $ by simpa [this] using hqnd

lemma mk_ne_zero_of_ne_zero {n d : ℕ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
(mk_ne_zero hd).mpr h

lemma mul_num_denom (q r : nnℚ) : q * r = (q.num * r.num) /. ↑(q.denom * r.denom) :=
have hq' : (↑q.denom : ℕ) ≠ 0, by have := denom_ne_zero q; simpa,
have hr' : (↑r.denom : ℕ) ≠ 0, by have := denom_ne_zero r; simpa,
suffices (q.num /. ↑q.denom) * (r.num /. ↑r.denom) = (q.num * r.num) /. ↑(q.denom * r.denom),
  by simpa using this,
by simp [mul_def hq' hr', -num_denom]

lemma div_num_denom (q r : nnℚ) : q / r = (q.num * r.denom) /. (q.denom * r.num) :=
if hr : r.num = 0 then
  have hr' : r = 0, from zero_of_num_zero hr,
  by simp *
else
  calc q / r = q * r⁻¹ : div_eq_mul_inv q r
         ... = (q.num /. q.denom) * (r.num /. r.denom)⁻¹ : by simp
         ... = (q.num /. q.denom) * (r.denom /. r.num) : by rw inv_def
         ... = (q.num * r.denom) /. (q.denom * r.num) : mul_def (by simpa using denom_ne_zero q) hr

lemma num_denom_mk {q : nnℚ} {n d : ℕ} (hd : d ≠ 0) (qdf : q = n /. d) :
  ∃ c : ℕ, n = c * q.num ∧ d = c * q.denom :=
begin
  obtain rfl|hn := eq_or_ne n 0,
  { simp [qdf] },
  have : q.num * d = n * ↑(q.denom),
  { refine (nnRat.mk_eq _ hd).mp _,
    { exact int.coe_nat_ne_zero.mpr (nnRat.denom_ne_zero _) },
    { rwa [num_denom] } },
  have hqdn : q.num ∣ n,
  { rw qdf, exact nnRat.num_dvd _ hd },
  refine ⟨n / q.num, _, _⟩,
  { rw int.div_mul_cancel hqdn },
  { refine int.eq_mul_div_of_mul_eq_mul_of_dvd_left _ hqdn this,
    rw qdf,
    exact nnRat.num_ne_zero_of_ne_zero ((mk_ne_zero hd).mpr hn) }
end

theorem mk_pnat_num (n : ℕ) (d : ℕ+) :
  (mk_pnat n d).num = n / Nat.gcd n d :=
by cases d; refl

theorem mk_pnat_denom (n : ℕ) (d : ℕ+) :
  (mk_pnat n d).denom = d / Nat.gcd n d :=
by cases d; refl

lemma num_mk (n d : ℕ) :
  (n /. d).num = d.sign * n / n.gcd d :=
begin
  rcases d with ((_ | _) | _);
    simp [nnRat.mk, mk_nat, mk_pnat, Nat.succ_pnat, int.sign, int.gcd,
      -Nat.cast_succ, -int.coe_nat_succ, int.zero_div]
end

lemma denom_mk (n d : ℕ) :
  (n /. d).denom = if d = 0 then 1 else d / n.gcd d :=
begin
  rcases d with ((_ | _) | _);
  simp [nnRat.mk, mk_nat, mk_pnat, Nat.succ_pnat, int.sign, int.gcd,
    -Nat.cast_succ, -int.coe_nat_succ]
end

theorem mk_pnat_denom_dvd (n : ℕ) (d : ℕ+) :
  (mk_pnat n d).denom ∣ d.1 :=
begin
  rw mk_pnat_denom,
  apply Nat.div_dvd_of_dvd,
  apply Nat.gcd_dvd_right
end

theorem add_denom_dvd (q₁ q₂ : nnℚ) : (q₁ + q₂).denom ∣ q₁.denom * q₂.denom :=
by { cases q₁, cases q₂, apply mk_pnat_denom_dvd }

theorem mul_denom_dvd (q₁ q₂ : nnℚ) : (q₁ * q₂).denom ∣ q₁.denom * q₂.denom :=
by { cases q₁, cases q₂, apply mk_pnat_denom_dvd }

theorem mul_num (q₁ q₂ : nnℚ) : (q₁ * q₂).num =
  (q₁.num * q₂.num) / Nat.gcd (q₁.num * q₂.num) (q₁.denom * q₂.denom) :=
by cases q₁; cases q₂; refl

theorem mul_denom (q₁ q₂ : nnℚ) : (q₁ * q₂).denom =
  (q₁.denom * q₂.denom) / Nat.gcd (q₁.num * q₂.num) (q₁.denom * q₂.denom) :=
by cases q₁; cases q₂; refl

theorem mul_self_num (q : nnℚ) : (q * q).num = q.num * q.num :=
by rw [mul_num, int.nat_abs_mul, Nat.coprime.gcd_eq_one, int.coe_nat_one, int.div_one];
exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

theorem mul_self_denom (q : nnℚ) : (q * q).denom = q.denom * q.denom :=
by rw [nnRat.mul_denom, int.nat_abs_mul, Nat.coprime.gcd_eq_one, Nat.div_one];
exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

lemma add_num_denom (q r : nnℚ) : q + r =
  ((q.num * r.denom + q.denom * r.num : ℕ)) /. (↑q.denom * ↑r.denom : ℕ) :=
have hqd : (q.denom : ℕ) ≠ 0, from int.coe_nat_ne_zero_iff_pos.2 q.3,
have hrd : (r.denom : ℕ) ≠ 0, from int.coe_nat_ne_zero_iff_pos.2 r.3,
by conv_lhs { rw [←@num_denom q, ←@num_denom r, nnRat.add_def hqd hrd] };
  simp [mul_comm]

section casts

protected lemma add_mk (a b c : ℕ) : (a + b) /. c = a /. c + b /. c :=
if h : c = 0 then by simp [h] else
by { rw [add_def h h, mk_eq h (mul_ne_zero h h)], simp [add_mul, mul_assoc] }

theorem coe_int_eq_mk : ∀ z : ℕ, ↑z = z /. 1
| (n : ℕ) := of_int_eq_mk _
| -[1+ n] := show -(of_int _) = _, by simp [of_int_eq_mk, neg_def, int.neg_succ_of_nat_coe]

theorem mk_eq_div (n d : ℕ) : n /. d = ((n : nnℚ) / d) :=
begin
  by_cases d0 : d = 0, {simp [d0, div_zero]},
  simp [division_def, coe_int_eq_mk, mul_def one_ne_zero d0]
end

lemma mk_mul_mk_cancel {x : ℕ} (hx : x ≠ 0) (n d : ℕ) : (n /. x) * (x /. d) = n /. d :=
begin
  by_cases hd : d = 0,
  { rw hd,
    simp},
  rw [mul_def hx hd, mul_comm x, div_mk_div_cancel_left hx],
end

lemma mk_div_mk_cancel_left {x : ℕ} (hx : x ≠ 0) (n d : ℕ) : (n /. x) / (d /. x) = n /. d :=
by rw [div_eq_mul_inv, inv_def, mk_mul_mk_cancel hx]

lemma mk_div_mk_cancel_right {x : ℕ} (hx : x ≠ 0) (n d : ℕ) : (x /. n) / (x /. d) = d /. n :=
by rw [div_eq_mul_inv, inv_def, mul_comm, mk_mul_mk_cancel hx]

lemma coe_int_div_eq_mk {n d : ℕ} : (n : nnℚ) / ↑d = n /. d :=
begin
  repeat {rw coe_int_eq_mk},
  exact mk_div_mk_cancel_left one_ne_zero n d,
end

@[simp]
theorem num_div_denom (r : nnℚ) : (r.num / r.denom : nnℚ) = r :=
by rw [← int.cast_coe_nat, ← mk_eq_div, num_denom]

lemma exists_eq_mul_div_num_and_eq_mul_div_denom (n : ℕ) {d : ℕ} (d_ne_zero : d ≠ 0) :
  ∃ (c : ℕ), n = c * ((n : nnℚ) / d).num ∧ (d : ℕ) = c * ((n : nnℚ) / d).denom :=
begin
  have : ((n : nnℚ) / d) = nnRat.mk n d, by rw [←rat.mk_eq_div],
  exact nnRat.num_denom_mk d_ne_zero this
end

lemma mul_num_denom' (q r : nnℚ) :
  (q * r).num * q.denom * r.denom = q.num * r.num * (q * r).denom :=
begin
  let s := (q.num * r.num) /. (q.denom * r.denom : ℕ),
  have hs : (q.denom * r.denom : ℕ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos),
  obtain ⟨c, ⟨c_mul_num, c_mul_denom⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_denom (q.num * r.num) hs,
  rw [c_mul_num, mul_assoc, mul_comm],
  nth_rewrite 0 c_mul_denom,
  repeat {rw mul_assoc},
  apply mul_eq_mul_left_iff.2,
  rw or_iff_not_imp_right,
  intro c_pos,
  have h : _ = s := @mul_def q.num q.denom r.num r.denom
    (int.coe_nat_ne_zero_iff_pos.mpr q.pos)
    (int.coe_nat_ne_zero_iff_pos.mpr  r.pos),
  rw [num_denom, num_denom] at h,
  rw h,
  rw mul_comm,
  apply nnRat.eq_iff_mul_eq_mul.mp,
  rw ←mk_eq_div,
end

lemma add_num_denom' (q r : nnℚ) :
  (q + r).num * q.denom * r.denom = (q.num * r.denom + r.num * q.denom) * (q + r).denom :=
begin
  let s := mk (q.num * r.denom + r.num * q.denom) (q.denom * r.denom : ℕ),
  have hs : (q.denom * r.denom : ℕ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos),
  obtain ⟨c, ⟨c_mul_num, c_mul_denom⟩⟩ := exists_eq_mul_div_num_and_eq_mul_div_denom
    (q.num * r.denom + r.num * q.denom) hs,
  rw [c_mul_num, mul_assoc, mul_comm],
  nth_rewrite 0 c_mul_denom,
  repeat {rw mul_assoc},
  apply mul_eq_mul_left_iff.2,
  rw or_iff_not_imp_right,
  intro c_pos,
  have h : _ = s := @add_def q.num q.denom r.num r.denom
    (int.coe_nat_ne_zero_iff_pos.mpr q.pos)
    (int.coe_nat_ne_zero_iff_pos.mpr  r.pos),
  rw [num_denom, num_denom] at h,
  rw h,
  rw mul_comm,
  apply nnRat.eq_iff_mul_eq_mul.mp,
  rw ←mk_eq_div,
end

lemma substr_num_denom' (q r : nnℚ) :
  (q - r).num * q.denom * r.denom = (q.num * r.denom - r.num * q.denom) * (q - r).denom :=
by rw [sub_eq_add_neg, sub_eq_add_neg, ←neg_mul, ←num_neg_eq_neg_num, ←denom_neg_eq_denom r,
  add_num_denom' q (-r)]

theorem coe_int_eq_of_int (z : ℕ) : ↑z = of_int z :=
(coe_int_eq_mk z).trans (of_int_eq_mk z).symm

@[simp, norm_cast] theorem coe_int_num (n : ℕ) : (n : nnℚ).num = n :=
by rw coe_int_eq_of_int; refl

@[simp, norm_cast] theorem coe_int_denom (n : ℕ) : (n : nnℚ).denom = 1 :=
by rw coe_int_eq_of_int; refl

lemma coe_int_num_of_denom_eq_one {q : nnℚ} (hq : q.denom = 1) : ↑(q.num) = q :=
by { conv_rhs { rw [←(@num_denom q), hq] }, rw [coe_int_eq_mk], refl }

lemma denom_eq_one_iff (r : nnℚ) : r.denom = 1 ↔ ↑r.num = r :=
⟨nnRat.coe_int_num_of_denom_eq_one, λ h, h ▸ nnRat.coe_int_denom r.num⟩

instance : can_lift nnℚ ℕ :=
⟨coe, λ q, q.denom = 1, λ q hq, ⟨q.num, coe_int_num_of_denom_eq_one hq⟩⟩

theorem coe_nat_eq_mk (n : ℕ) : ↑n = n /. 1 :=
by rw [← int.cast_coe_nat, coe_int_eq_mk]

@[simp, norm_cast] theorem coe_nat_num (n : ℕ) : (n : nnℚ).num = n :=
by rw [← int.cast_coe_nat, coe_int_num]

@[simp, norm_cast] theorem coe_nat_denom (n : ℕ) : (n : nnℚ).denom = 1 :=
by rw [← int.cast_coe_nat, coe_int_denom]

-- Will be subsumed by `int.coe_inj` after we have defined
-- `linear_ordered_field nnℚ` (which implies characteristic zero).
lemma coe_int_inj (m n : ℕ) : (m : nnℚ) = n ↔ m = n :=
⟨λ h, by simpa using congr_arg num h, congr_arg _⟩

end casts

lemma inv_def' {q : nnℚ} : q⁻¹ = (q.denom : nnℚ) / q.num :=
by { conv_lhs { rw ←(@num_denom q) }, cases q, simp [div_num_denom] }

@[simp] lemma mul_denom_eq_num {q : nnℚ} : q * q.denom = q.num :=
begin
  suffices : mk (q.num) ↑(q.denom) * mk ↑(q.denom) 1 = mk (q.num) 1, by
  { conv { for q [1] { rw ←(@num_denom q) }}, rwa [coe_int_eq_mk, coe_nat_eq_mk] },
  have : (q.denom : ℕ) ≠ 0, from ne_of_gt (by exact_mod_cast q.pos),
  rw [(nnRat.mul_def this one_ne_zero), (mul_comm (q.denom : ℕ) 1), (div_mk_div_cancel_left this)]
end

lemma denom_div_cast_eq_one_iff (m n : ℕ) (hn : n ≠ 0) :
  ((m : nnℚ) / n).denom = 1 ↔ n ∣ m :=
begin
  replace hn : (n:nnℚ) ≠ 0, by rwa [ne.def, ← int.cast_zero, coe_int_inj],
  split,
  { intro h,
    lift ((m : nnℚ) / n) to ℕ using h with k hk,
    use k,
    rwa [eq_div_iff_mul_eq hn, ← int.cast_mul, mul_comm, eq_comm, coe_int_inj] at hk },
  { rintros ⟨d, rfl⟩,
    rw [int.cast_mul, mul_comm, mul_div_cancel _ hn, nnRat.coe_int_denom] }
end

lemma num_div_eq_of_coprime {a b : ℕ} (hb0 : 0 < b) (h : Nat.coprime a b) :
  (a / b : nnℚ).num = a :=
begin
  lift b to ℕ using le_of_lt hb0,
  norm_cast at hb0 h,
  rw [← nnRat.mk_eq_div, ← nnRat.mk_pnat_eq a b hb0, nnRat.mk_pnat_num, pnat.mk_coe, h.gcd_eq_one,
    int.coe_nat_one, int.div_one]
end

lemma denom_div_eq_of_coprime {a b : ℕ} (hb0 : 0 < b) (h : Nat.coprime a b) :
  ((a / b : nnℚ).denom : ℕ) = b :=
begin
  lift b to ℕ using le_of_lt hb0,
  norm_cast at hb0 h,
  rw [← nnRat.mk_eq_div, ← nnRat.mk_pnat_eq a b hb0, nnRat.mk_pnat_denom, pnat.mk_coe, h.gcd_eq_one,
    Nat.div_one]
end

lemma div_int_inj {a b c d : ℕ} (hb0 : 0 < b) (hd0 : 0 < d)
  (h1 : Nat.coprime a b) (h2 : Nat.coprime c d)
  (h : (a : nnℚ) / b = (c : nnℚ) / d) : a = c ∧ b = d :=
begin
  apply and.intro,
  { rw [← (num_div_eq_of_coprime hb0 h1), h, num_div_eq_of_coprime hd0 h2] },
  { rw [← (denom_div_eq_of_coprime hb0 h1), h, denom_div_eq_of_coprime hd0 h2] }
end

@[norm_cast] lemma coe_int_div_self (n : ℕ) : ((n / n : ℕ) : nnℚ) = n / n :=
begin
  by_cases hn : n = 0,
  { subst hn, simp only [int.cast_zero, int.zero_div, zero_div] },
  { have : (n : nnℚ) ≠ 0, { rwa ← coe_int_inj at hn },
    simp only [int.div_self hn, int.cast_one, ne.def, not_false_iff, div_self this] }
end

@[norm_cast] lemma coe_nat_div_self (n : ℕ) : ((n / n : ℕ) : nnℚ) = n / n :=
coe_int_div_self n

lemma coe_int_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : nnℚ) = a / b :=
begin
  rcases h with ⟨c, rfl⟩,
  simp only [mul_comm b, int.mul_div_assoc c (dvd_refl b), int.cast_mul, mul_div_assoc,
    coe_int_div_self]
end

lemma coe_nat_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : nnℚ) = a / b :=
begin
  rcases h with ⟨c, rfl⟩,
  simp only [mul_comm b, Nat.mul_div_assoc c (dvd_refl b), Nat.cast_mul, mul_div_assoc,
    coe_nat_div_self]
end

lemma inv_coe_int_num {a : ℕ} (ha0 : 0 < a) : (a : nnℚ)⁻¹.num = 1 :=
begin
  rw [nnRat.inv_def', nnRat.coe_int_num, nnRat.coe_int_denom, Nat.cast_one, ←int.cast_one],
  apply num_div_eq_of_coprime ha0,
  rw int.nat_abs_one,
  exact Nat.coprime_one_left _,
end

lemma inv_coe_nat_num {a : ℕ} (ha0 : 0 < a) : (a : nnℚ)⁻¹.num = 1 :=
inv_coe_int_num (by exact_mod_cast ha0 : 0 < (a : ℕ))

lemma inv_coe_int_denom {a : ℕ} (ha0 : 0 < a) : ((a : nnℚ)⁻¹.denom : ℕ) = a :=
begin
  rw [nnRat.inv_def', nnRat.coe_int_num, nnRat.coe_int_denom, Nat.cast_one, ←int.cast_one],
  apply denom_div_eq_of_coprime ha0,
  rw int.nat_abs_one,
  exact Nat.coprime_one_left _,
end

lemma inv_coe_nat_denom {a : ℕ} (ha0 : 0 < a) : (a : nnℚ)⁻¹.denom = a :=
begin
  rw [← int.coe_nat_eq_coe_nat_iff, ← int.cast_coe_nat a, inv_coe_int_denom],
  rwa [← Nat.cast_zero, Nat.cast_lt]
end

protected lemma «forall» {p : nnℚ → Prop} : (∀ r, p r) ↔ ∀ a b : ℕ, p (a / b) :=
⟨λ h _ _, h _,
  λ h q, (show q = q.num / q.denom, from by simp [nnRat.div_num_denom]).symm ▸ (h q.1 q.2)⟩

protected lemma «exists» {p : nnℚ → Prop} : (∃ r, p r) ↔ ∃ a b : ℕ, p (a / b) :=
⟨λ ⟨r, hr⟩, ⟨r.num, r.denom, by rwa [← mk_eq_div, num_denom]⟩, λ ⟨a, b, h⟩, ⟨_, h⟩⟩

/-!
### Denominator as `ℕ+`
-/
section pnat_denom

/-- Denominator as `ℕ+`. -/
def pnat_denom (x : nnℚ) : ℕ+ := ⟨x.denom, x.pos⟩

@[simp] lemma coe_pnat_denom (x : nnℚ) : (x.pnat_denom : ℕ) = x.denom := rfl

@[simp] lemma mk_pnat_pnat_denom_eq (x : nnℚ) : mk_pnat x.num x.pnat_denom = x :=
by rw [pnat_denom, mk_pnat_eq, num_denom]

lemma pnat_denom_eq_iff_denom_eq {x : nnℚ} {n : ℕ+} : x.pnat_denom = n ↔ x.denom = ↑n :=
subtype.ext_iff

end pnat_denom

end Rat
