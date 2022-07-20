import Mathlib
import Mathlib.Data.Nat.Gcd

#check PartialOrder

structure NNRat where
  up : Nat
  down : Nat
  down_nonzero : down ≠ 0
  simple : Nat.coprime up down

instance : OfNat NNRat n where
  ofNat := {up := n, down := 1, down_nonzero := Nat.zero_ne_one.symm, simple := Nat.coprime_one_right _}

def NNRat.mul' (l r : NNRat) : ℕ × ℕ := (l.up * r.up, l.down * r.down)

def Nat.pos_iff_nonzero : ∀ n, 0 < n ↔ 0 ≠ n
  | 0 =>  ⟨ λ h => (by cases h)
          , λ h => by exfalso; apply h; rfl
          ⟩
  | (succ n) => {mp := λ h => by apply ne_of_lt h, mpr := λ _ => Nat.zero_lt_succ n} 

def NNRat.fromPair : ℕ × ℕ → NNRat
  | ⟨u, d⟩ =>    
    if d_zero : d = 0
    then 0
    else  
      {
        up := u / (u.gcd d)
        down := d / (u.gcd d)
        down_nonzero := 
          by
          intro quotient_not_zero
          apply d_zero
          have ⟨m, m_h⟩ := Nat.gcd_dvd_right u d
          have : Nat.gcd u d * m / Nat.gcd u d = 0 := by
            rw [← m_h]; assumption
          rw [Nat.mul_comm, Nat.mul_div_assoc, Nat.div_self, mul_one] at this
          rw [this, mul_zero] at m_h
          exact m_h
          apply Nat.zero_lt_of_ne_zero
          simp [Nat.gcd_eq_zero_iff]
          intros _
          apply d_zero
          exists 1
          simp
        simple := by 
          apply Nat.coprime_div_gcd_div_gcd
          apply Nat.zero_lt_of_ne_zero
          simp [Nat.gcd_eq_zero_iff]
          intros _
          apply d_zero
      } 

def NNRat.mul (l r : NNRat) : NNRat := NNRat.fromPair (l.mul' r)

def NNRat.add' (l r : NNRat) : ℕ × ℕ :=
  ⟨l.up * r.down + r.up * l.down
  , l.down * r.down⟩

def NNRat.add (l r : NNRat) := NNRat.fromPair (l.add' r)

instance : Add NNRat where
  add := NNRat.add

lemma NNRat.add_assoc (n m k : NNRat) : n + m + k = n + (m + k) :=
  by
  cases n
  case mk n_up n_down n_down_nonzero n_simple =>
  cases m
  case mk m_up m_down m_down_nonzero m_simple =>
  cases k
  case mk k_up k_down k_down_nonzero k_simple =>
  simp [HAdd.hAdd, Add.add, add, add']
  simp [fromPair]

instance : AddCommMonoid NNRat where
  add_assoc := _
  add_zero := _
  add_comm := _
  nsmul_zero' := _
  nsmul_succ' := _

instance : CommSemiring NNRat where
  add_assoc := _
  add_zero