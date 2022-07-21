import Mathlib

structure Fraction where
  num : ℕ
  denom : ℕ
  d_pos : denom > 0

def Fraction.equiv : Fraction → Fraction → Prop
  | a, b => a.num * b.denom = b.num * a.denom

lemma Fraction.equiv_refl : ∀ q, Fraction.equiv q q := λ _ => rfl

lemma Fraction.equiv_symm' : ∀ {p q}, Fraction.equiv p q -> Fraction.equiv q p
  | p, q => by
    simp [Fraction.equiv]
    intros h
    rw [h]

lemma Fraction.equiv_symm {p q} : Fraction.equiv p q ↔ Fraction.equiv q p where
  mp := Fraction.equiv_symm'
  mpr := Fraction.equiv_symm'

lemma Fraction.equiv_trans : ∀ {p q r}, Fraction.equiv p q -> Fraction.equiv q r -> Fraction.equiv p r
  | p, q, r, pq, qr => 
    if q_zero : q.num = 0
    then
      by
      simp [equiv] at *
      suffices p_zero : p.num = 0
      suffices r_zero : r.num = 0
      simp [p_zero, r_zero]
      case p_zero =>
        simp [q_zero] at *
        have h : _ := by exact Nat.eq_zero_of_mul_eq_zero pq
        cases h
        case inl h => exact h
        case inr h => exfalso; apply ne_of_gt q.d_pos h
      case r_zero =>
        simp [q_zero, p_zero] at *
        have h : _ := by exact Nat.eq_zero_of_mul_eq_zero qr.symm
        cases h
        case inl h => exact h
        case inr h => exfalso; apply ne_of_gt q.d_pos h
    else
      by
      simp [equiv] at *
      have : q.num * ↑q.denom > 0 := by
        apply Nat.mul_pos
        case ha =>
          apply Nat.gt_of_not_le
          rw [le_iff_lt_or_eq]
          intros h
          cases h
          case inl h => 
            cases h
          case inr h =>
            exact q_zero h
        case hb => exact q.d_pos
      apply Nat.eq_of_mul_eq_mul_right this 
      have : ∀ x y z w : ℕ, x * y * (z * w) = (x * w) * (z * y) := 
        by
        intros x y z w
        ring
      rw [this, qr, pq]
      rw [this]
      have : ∀ x y z w : ℕ, (x * y) * (z * w) = z * w * (x * y) := λ x y z w => by ring
      rw [this]

instance Fraction.Setoid : Setoid Fraction where
  r := equiv
  iseqv := ⟨Fraction.equiv_refl, Fraction.equiv_symm', Fraction.equiv_trans⟩

def Rat := Quotient Fraction.Setoid

namespace Rat

def mk : Fraction → Rat := Quotient.mk _ 

abbrev ℚ := Rat


def raw_add : Fraction → Fraction → Fraction
  | l, r => 
    have h :  l.denom * r.denom > 0 := by apply Nat.mul_pos l.d_pos r.d_pos
    {
      num := l.num * r.denom + r.num * l.denom
      denom := l.denom * r.denom
      d_pos := h
    }


def from_raw (f : Fraction → Fraction → Fraction) := 
  @Quotient.lift₂ _ _ _ Fraction.Setoid Fraction.Setoid (λ x y => Rat.mk $ f x y) 
  
lemma Fraction.equiv_def (a b : Fraction) : a ≈ b ↔ a.num * b.denom = b.num * a.denom := by
  simp [HasEquiv.Equiv, Setoid.r, Fraction.equiv]

instance : Add Rat where
  add := from_raw Rat.raw_add $ by
    intros a₁ b₁ a₂ b₂ a₁a₂ b₁b₂
    simp [Rat.mk, Rat.raw_add]
    apply Quotient.sound
    case a =>
      simp [Fraction.equiv_def] at *
      simp [right_distrib, left_distrib]
      apply congr_arg2
      case hx =>
        have : ∀ x y z w : ℕ, x * y * (z * w) = x * z * (w * y) := by intros; ring
        rw [this, a₁a₂]
        simp [mul_assoc]
        apply congr_arg
        ring
      case hy =>
        have : ∀ x y z w : ℕ, x * y * (z * w) = x * w * (z * y) := by intros; ring
        rw [this, b₁b₂]
        simp [mul_assoc]
        apply congr_arg
        ring

def raw_mul : Fraction → Fraction → Fraction
  | l, r => 
    have h :  l.denom * r.denom > 0 := by apply Nat.mul_pos l.d_pos r.d_pos
    {
      num := l.num * r.num
      denom := l.denom * r.denom
      d_pos := h
    }

instance : Mul Rat where
  mul := from_raw Rat.raw_mul $ by
    intros a₁ b₁ a₂ b₂ a₁a₂ b₁b₂
    simp [Rat.mk, Rat.raw_mul]
    apply Quotient.sound
    case a =>
      simp [Fraction.equiv_def] at *
      have : ∀ x y z w : ℕ, x * y * (z * w) = x * z * (y * w) := by intros; ring
      rw [this, a₁a₂, b₁b₂]
      apply Eq.symm
      rw [this]

instance : OfNat Rat n where
  ofNat := Rat.mk ⟨n, 1, Nat.one_pos⟩

lemma Nat.div_pos : ∀ n m (_n_pos : n > 0) (_m_pos : m > 0) (_n_le_m : n ≤ m), m / n > 0
  | 0, _, n_pos, _, _ => by cases n_pos
  | _, 0, _, m_pos, _ => by cases m_pos
  | n+1, m+1, n_pos, m_pos, n_le_m => by
    cases n_le_m
    case refl =>
      rw [Nat.div_self]
      exact Nat.zero_lt_one
      exact n_pos
    case step h =>
      simp at *
      apply Nat.lt_of_succ_le
      rw [Nat.le_div_iff_mul_le]
      have : Nat.succ 0 = 1 := rfl
      rw [this, one_mul]
      apply le_trans h
      apply Nat.le.step Nat.le.refl
      exact n_pos

def reduced_from_aux (q : Fraction) : Fraction := 
      { num := q.num / q.num.gcd q.denom
      , denom := q.denom / q.num.gcd q.denom
      , d_pos := by
        apply Nat.div_pos
        case _n_pos =>
          apply Nat.gcd_pos_of_pos_right _ q.d_pos
        case _m_pos =>
          exact q.d_pos
        case _n_le_m =>
          apply Nat.gcd_le_right _ q.d_pos
      }

def cross_mult (x y z w : ℕ) : 0 < z → 0 < x → w ∣ x → y ∣ z → x * y = z * w → x / w = z / y := by
  intros z_pos x_pos w_dvd_x y_dvd_z xy_eq_zw
  have y_pos : y > 0 := Nat.pos_of_dvd_of_pos y_dvd_z z_pos
  have w_pos : w > 0 := Nat.pos_of_dvd_of_pos w_dvd_x x_pos
  have ⟨a, a_def⟩ := w_dvd_x
  have ⟨b, b_def⟩ := y_dvd_z
  rw [a_def, b_def] at xy_eq_zw
  rw [a_def, b_def]
  rw [Nat.mul_div_cancel_left, Nat.mul_div_cancel_left]
  have h₁ : w * a * y = y * w * a := by ring
  have h₂ : y * b * w = y * w * b := by ring
  rw [h₁, h₂] at xy_eq_zw
  apply Nat.eq_of_mul_eq_mul_left _ xy_eq_zw
  apply Nat.mul_pos y_pos w_pos
  exact y_pos
  exact w_pos

lemma equiv_zero {a b : Fraction} (a_equiv_b : a ≈ b) (a_zero : a.num = 0) : b.num = 0 := by
  rw [Fraction.equiv_def] at a_equiv_b
  simp [a_zero] at a_equiv_b
  have : b.num = 0 ∨ a.denom = 0 := Nat.eq_zero_of_mul_eq_zero a_equiv_b.symm
  cases this
  case inl h => exact h
  case inr h =>
    have : 0 < a.denom := a.d_pos
    rw [h] at this
    exfalso
    apply Nat.not_lt_zero 0 this 

lemma coprime_pair_unique
  (a₀ a₁ b₀ b₁ : ℕ)
  (a_b' : a₀ * b₁ = a₁ * b₀)
  (a_coprime : Nat.coprime b₀ b₁)
  (b_coprime : Nat.coprime b₀ b₁)
  : a₀ = b₀ ∧ a₁ = b₁ :=
  have : Nat.coprime_div_gcd_div_gcd

  

def reduced_form : ∀ p : ℚ, Fraction :=
    Quotient.lift reduced_from_aux $ 
      fun a b a_b =>
      if h : a.num = 0 ∨ b.num = 0
        then 
          have : a.num = 0 ∧ b.num = 0 := 
            match h with
            | Or.inl a_zero => And.intro a_zero (equiv_zero a_b a_zero)
            | Or.inr b_zero => And.intro (equiv_zero a_b.symm b_zero) b_zero
          by
          simp [reduced_from_aux, this.1, this.2, Nat.div_self a.d_pos, Nat.div_self b.d_pos]
        else by
          rw [not_or] at h
          rw [← ne_eq, ← Nat.pos_iff_ne_zero] at h
          rw [← ne_eq, ← Nat.pos_iff_ne_zero] at h
          have ⟨a_pos, b_pos⟩ := h; clear h
          simp [reduced_from_aux]
          rw [Fraction.equiv_def] at a_b
          have ⟨a₀, a₀_def⟩ := Nat.gcd_dvd_left a.num a.denom
          have ⟨a₁, a₁_def⟩ := Nat.gcd_dvd_right a.num a.denom
          have ⟨b₀, b₀_def⟩ := Nat.gcd_dvd_left b.num b.denom
          have ⟨b₁, b₁_def⟩ := Nat.gcd_dvd_right b.num b.denom
          have : a.num * b.denom = (a.num.gcd a.denom) * (b.num.gcd b.denom) * (a₀ * b₁) := by
            have : a.num * b.denom = (Nat.gcd a.num a.denom * a₀) * (Nat.gcd b.num b.denom * b₁) := by
              rw [← b₁_def, ← a₀_def]
            rw [this]
            simp [mul_assoc]
            apply congr_arg
            ring
          rw [this] at a_b; clear this
          have : b.num * a.denom = (a.num.gcd a.denom) * (b.num.gcd b.denom) * (a₁ * b₀) := by
            have : b.num * a.denom = (Nat.gcd a.num a.denom * a₁) * (Nat.gcd b.num b.denom * b₀) := by
              rw [← a₁_def, ← b₀_def]
            rw [this]
            simp [mul_assoc]
            apply congr_arg
            ring
          rw [this] at a_b; clear this
          have a_b' : a₀ * b₁ = a₁ * b₀ := by
            apply Nat.eq_of_mul_eq_mul_left _ a_b
            apply Nat.mul_pos
            apply Nat.gcd_pos_of_pos_left _ a_pos
            apply Nat.gcd_pos_of_pos_left _ b_pos

          have : a.num / Nat.gcd a.num a.denom = a₀ := by
            apply Eq.trans (b := Nat.gcd a.num a.denom * a₀ / Nat.gcd a.num a.denom)
            case h₁ => rw [← a₀_def]
            case h₂ => 
              apply Nat.mul_div_cancel_left
              apply Nat.gcd_pos_of_pos_left _ a_pos
          rw [this]; clear this
          have : a.denom / Nat.gcd a.num a.denom = a₁ := by
            apply Eq.trans (b := Nat.gcd a.num a.denom * a₁ / Nat.gcd a.num a.denom)
            case h₁ => rw [← a₁_def]
            case h₂ => 
              apply Nat.mul_div_cancel_left
              apply Nat.gcd_pos_of_pos_left _ a_pos
          rw [this]; clear this
          have : b.num / Nat.gcd b.num b.denom = b₀ := by
            apply Eq.trans (b := Nat.gcd b.num b.denom * b₀ / Nat.gcd b.num b.denom)
            case h₁ => rw [← b₀_def]
            case h₂ => 
              apply Nat.mul_div_cancel_left
              apply Nat.gcd_pos_of_pos_left _ b_pos
          rw [this]; clear this
          have : b.denom / Nat.gcd b.num b.denom = b₁ := by
            apply Eq.trans (b := Nat.gcd b.num b.denom * b₁ / Nat.gcd b.num b.denom)
            case h₁ => rw [← b₁_def]
            case h₂ => 
              apply Nat.mul_div_cancel_left
              apply Nat.gcd_pos_of_pos_left _ b_pos
          rw [this]; clear this

          have a_coprime : a₀.coprime a₁ := by
            have : a₀ = a.num / Nat.gcd a.num a.denom := by
              apply Eq.symm
              apply Nat.div_eq_of_eq_mul_left
              apply Nat.gcd_pos_of_pos_left _ a_pos
              rw [mul_comm, ← a₀_def]
            rw [this]; clear this
            have : a₁ = a.denom / Nat.gcd a.num a.denom := by
              apply Eq.symm
              apply Nat.div_eq_of_eq_mul_left
              apply Nat.gcd_pos_of_pos_left _ a_pos
              rw [mul_comm, ← a₁_def]
            rw [this]; clear this
            apply Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ a_pos)

          have b_coprime : b₀.coprime b₁ := by
            have : b₀ = b.num / Nat.gcd b.num b.denom := by
              apply Eq.symm
              apply Nat.div_eq_of_eq_mul_left
              apply Nat.gcd_pos_of_pos_left _ b_pos
              rw [mul_comm, ← b₀_def]
            rw [this]; clear this
            have : b₁ = b.denom / Nat.gcd b.num b.denom := by
              apply Eq.symm
              apply Nat.div_eq_of_eq_mul_left
              apply Nat.gcd_pos_of_pos_left _ b_pos
              rw [mul_comm, ← b₁_def]
            rw [this]; clear this
            apply Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ b_pos)

          clear a b b_pos a_pos b₀_def b₁_def a₀_def a₁_def a_b



lemma mul_comm : ∀ p q : ℚ, p * q = q * p := by
  intros p q
  
  

instance : CommRing Rat where
  mul_assoc := _
  mul_comm := _
  zero_mul := _
  mul_zero := _
  one_mul := _
  mul_one := _
  gsmul_zero' := _
  gsmul_succ' := _
  gsmul_neg' := _
  
  npow_zero' := _
  npow_succ' := _

  add_assoc := _
  add_comm := _
  add_zero := _
  zero_add := _
  
  natCast := _
  natCast_zero := _
  natCast_succ := _

  intCast := _
  intCast_ofNat := _
  intCast_negSucc := _
  
  nsmul_zero' := _
  nsmul_succ' := _

  neg := _
  sub_eq_add_neg := _
  add_left_neg := _
  
  left_distrib := _
  right_distrib := _