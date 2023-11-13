import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

namespace agm

#check Odd
-- example of how to use wlog and generalizing
example (P Q : Prop) : P ∨ Q → ¬ P → Q := by tauto

theorem mul_le_one_elim {a b : ℝ} : a*b ≤ 1 → a ≤ 1 ∨ b ≤ 1 := by
  intro h
  apply by_contradiction
  intro hab
  simp at hab
  have : ¬ a ≤ 1 ∧ ¬ b ≤ 1 := by exact not_or.mp hab
  simp at this
  match this with
  | ⟨h1, h2⟩ =>
  have w1 : b > 0 := by linarith
  have : 1 * b < a*b := by exact (mul_lt_mul_right w1).mpr h1
  linarith

example (a b : Nat) (hab : Even a ∨ Even b) : Even (a*b) := by
wlog h : Even a generalizing a b
have u : Even b := by tauto
specialize this b a (Or.inl u) u
rw [mul_comm] at this
exact this

match h with
| ⟨k, hk⟩ => {
  use k*b
  rw [hk]
  ring
}

#check List.Mem
theorem prod_one_imp : (l : List ℝ) →  ∀ i, (l.get i = 0 → l.prod = 0)
| [] => by simp
| a :: l => by {
  intro i
  match i with
  | ⟨i_val, is⟩ => cases i_val with
    | zero => {
      simp
      intro h
      left
      exact h
    }
    | succ n => {
      simp
      intro h
      right
      rw [← h]
      exact List.get_mem l n (Nat.lt_of_succ_lt_succ is)
    }
}

theorem base (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hab : a * b = 1) : a ≤ 1 ∧ 1 ≤ b ∨ b ≤ 1 ∧ 1 ≤ a := by
cases le_or_gt a 1 with
| inl h => {
  have : a ≠ 0 := by exact left_ne_zero_of_mul_eq_one hab
  have crux : a > 0 := by exact Ne.lt_of_le (id (Ne.symm this)) ha
  have : b = 1 / a := by exact eq_one_div_of_mul_eq_one_right hab
  rw [this]
  apply Or.inl
  use h
  exact one_le_one_div crux h
}
| inr h =>  {
  have : a ≠ 0 := by exact left_ne_zero_of_mul_eq_one hab
  have crux : a > 0 := by exact Ne.lt_of_le (id (Ne.symm this)) ha
  have : b = 1 / a := by exact eq_one_div_of_mul_eq_one_right hab
  rw [this]
  apply Or.inr
  have : 1 / a < 1 := by exact (div_lt_one crux).mpr h
  apply And.intro
  linarith
  linarith
}

-- b lies inside the line segment a1a2 on the real line
def Bet (a1 b a2 : ℝ) := a1 ≤ b ∧ b ≤ a2 ∨ a2 ≤ b ∧  b ≤ a1
theorem Bet.symm {a1 b a2}  : Bet a1 b a2 → Bet a2 b a1 := by
simp [Bet]
tauto

def ind_swap {n : Nat} (i : Fin n.succ.succ) : Fin n.succ.succ :=
match i with
| ⟨i_val, is⟩ =>
match i_val with
| 0 => ⟨1, by simp⟩
| 1 => ⟨0, by simp⟩
| Nat.succ (Nat.succ n) => ⟨n.succ.succ, is⟩

#check Function.Injective
#check Fin.eq_mk_iff_val_eq
#check Nat.succ_ne_zero
example (f : ℝ → ℝ) (hi : f.Injective) (a b : ℝ) : a ≠ b → f a ≠ f b := by
intro h
exact Function.Injective.ne hi h

def ind_swap_inj (n : Nat) : (@ind_swap n).Injective := by
intros i j
match i, j with
| ⟨i_val, is⟩, ⟨j_val, js⟩ =>
match i_val, j_val with
| 0, 0 => simp
| 1, 1 => simp
| Nat.succ (Nat.succ n), Nat.succ (Nat.succ m) => simp [ind_swap]
| 0, 1 => simp [ind_swap]
| 0, Nat.succ (Nat.succ m) => {
  simp [ind_swap]
  intro h
  apply False.elim
  rw [Fin.eq_mk_iff_val_eq] at h
  simp at h
  exact Nat.succ_ne_zero m h.symm
}
| 1, 0 => simp [ind_swap]
| 1, Nat.succ (Nat.succ m) => {
  simp [ind_swap]
  intro h
  apply False.elim
  simp [Fin.eq_mk_iff_val_eq] at h
}
| Nat.succ (Nat.succ n), 0 => {
  simp [ind_swap]
  rw [Fin.eq_mk_iff_val_eq]
  simp
}
| Nat.succ (Nat.succ n), 1 => {
  simp [ind_swap]
  rw [Fin.eq_mk_iff_val_eq]
  simp
}

theorem swap_ind_swap (a b : ℝ) (l : List ℝ) (i : Fin (a :: b :: l).length) : (a :: b :: l).get i = (b :: a :: l).get (ind_swap i) := by
match i with
| ⟨i_val, is⟩ =>
match i_val with
| 0 => simp only [List.get, ind_swap]
| 1 => simp only [List.get, ind_swap]
| Nat.succ (Nat.succ n) => simp only [List.get, ind_swap]

theorem mul_ge_one_imp (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : a*b ≥ 1 → a ≥ 1 ∨ b ≥ 1 := by
  intro hab
  apply by_contradiction
  intro h
  have := not_or.mp h
  simp at this
  have : a ≤ 1 := by linarith
  have : a*b ≤ 1*b := by exact mul_le_mul_of_nonneg_right this hb
  linarith
theorem mul_le_one_imp (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : a*b ≤ 1 → a ≤ 1 ∨ b ≤ 1 := by
  intro hab
  apply by_contradiction
  intro h
  have := not_or.mp h
  simp at this
  have : a ≥ 1 := by linarith
  have : a*b ≥ 1*b := by exact mul_le_mul_of_nonneg_right this hb
  linarith
theorem prod_gt_one : (l : List ℝ) → (hl : l.length > 0) → (h1 : ∀ i : Fin l.length, l.get i > 1) → l.prod > 1
| [] => by simp
| [a] => by simp
| (a :: b :: l) => by {
  simp
  intro h1
  have := prod_gt_one (b :: l) (by simp) (by {
    intro i
    specialize h1 ⟨i.val + 1, by {
      simp
      have := i.isLt
      simp only [List.length] at this
      linarith
    }⟩
    exact h1
  })
  simp at this
  specialize h1 ⟨0, by simp⟩
  simp at h1
  have ha : a > 0 := by linarith
  have : a * 1 < a*(b*l.prod) := by exact (mul_lt_mul_left ha).mpr this
  linarith
}

theorem agm2 : (l : List ℝ) → l.length ≥ 2 → (∀ i, l.get i ≥ 0) → l.prod = 1→
∃ i j : Fin l.length, i ≠ j ∧ Bet (l.get i) 1 (l.get j)
| [] => by {simp;}
| [a] => by {simp;}
| [a, b] => by {
  intros h1 h2
  simp
  intro hab
  have ha : a ≥ 0 := h2 ⟨0, by linarith⟩
  have hb : b ≥ 0 := h2 ⟨1, by linarith⟩
  have crux1 := mul_le_one_imp a b ha hb (Eq.le hab)
  have crux2 := mul_ge_one_imp a b ha hb (Eq.ge hab)

  wlog h : a ≤ 1 generalizing a b with w
  {
    have : b ≤ 1 := by tauto
    rw [mul_comm] at hab
    specialize w b a h1 h2 hab hb ha crux1.symm crux2.symm this
    match w with
    | ⟨i, j, hij⟩ =>
    use j; use i
    match i, j with
    | 0, 1 => {
      simp
      exact hij.right
    }
    | 1, 0 => {
      simp
      exact hij.right
    }
    | 0, 0 => simp at hij
    | 1, 1 => simp at hij
  }
  cases LE.le.lt_or_eq h with
  | inl hT => {
    have : ¬ a ≥ 1 := not_le.mpr hT
    have hl' : b ≥ 1 := by tauto
    use 0; use 1
    simp
    exact Or.inl ⟨h, hl'⟩
  }
  | inr hE => {
    rw [hE] at hab
    ring_nf at hab
    use 0; use 1
    simp [hE, hab, Bet]
  }
}
| a :: (b :: (c :: l')) => by {
  let l'' := c :: l'
  have quirk : c :: l' = l'' := Eq.refl _
  have hl' : l''.length ≥ 1 := by {
    simp
    linarith
  }
  rw [quirk]
  generalize l'' = l at *

  intros hl h1 h2
  simp at h2
  have : ∃ i, (l).get i ≤ 1 := by {
    apply by_contradiction
    intro h
    simp at h
    have := prod_gt_one l (by linarith) h
    linarith
  }
}
theorem wow : (l : List ℝ) → l.length ≥ 2 → (∀ i, l.get i ≥ 0) → l.prod = 1→
∃ i j : Fin l.length, i ≠ j ∧ l.get i ≤ 1 ∧ 1 ≤ l.get j
| [] => by {simp;}
| [a] => by {simp;}
| [a, b] => by {
  intros h1 h2
  simp
  intro hab
  have crux1 : a ≠ 0 := left_ne_zero_of_mul_eq_one hab
  have : a ≥ 0 := h2 ⟨0, by linarith⟩
  have crux2 : a > 0 := Ne.lt_of_le (id (Ne.symm crux1)) this
  have : b = 1 / a := eq_one_div_of_mul_eq_one_right hab
  cases le_or_gt 1 a with
  | inl h => {
    use 1; use 0
    simp
    apply And.intro
    rw [this]
    exact (div_le_one crux2).mpr h
    exact h
  }
  | inr h => {
    use 0; use 1
    simp
    apply And.intro
    linarith
    rw [this]
    have : 1/a > 1 := one_lt_one_div crux2 h
    linarith
  }
}
| a :: (b :: (c :: l')) => by {
  let l := c :: l'
  have quirk : c :: l' = l := Eq.refl _
  rw [quirk]
  intros hl h1 h2
  have := wow ((a*b) :: l)
  have : ((a*b) :: l).length ≥ 2 := by {
      simp
      linarith
  }
  have crux := wow ((a*b) :: l) this
  have : (∀ (i : Fin (List.length (a * b :: l))), List.get (a * b :: l) i ≥ 0) := by {
    intro i
    simp at i
    cases h : i.val with
    | zero => {
      have h : i = 0 := by exact Fin.ext h
      simp [h]
      have p := h1 ⟨0,  Nat.succ_pos (List.length (b :: l))⟩
      have q := h1 ⟨1, by norm_num⟩
      simp at p
      simp at q
      exact mul_nonneg p q
    }
    | succ n => {
      have : i = ⟨(i : ℕ), i.isLt⟩ := Eq.refl _
      simp [h] at this
      rw [this]
      simp
      have := h1 ⟨n + 2, by {
        simp
        have : i.val < l.length.succ := i.isLt
        rw [h, ← quirk] at this
        simp at this
        linarith
      }⟩
      simp at this
      exact this
    }
  }

  have := crux this
  simp at h2
  have w : (a * b :: l).prod = 1 := by {
    rw [← h2]
    simp
    ring
  }
  match this w with
  | ⟨i, j, ⟨hij, h⟩⟩ => {
    let zero' : Fin (a*b::l).length := ⟨0, by simp⟩
    have : (i = zero' ∨ j = zero') ∨ ¬ (i = zero' ∨ j = zero') := em _
    cases this with
    | inl h' => {
      cases h' with
      | inl e => {
          have : ¬ (a > 1 ∧ b > 1) := by {
            intro w
            simp [e] at h
            match w with
            | ⟨w1, w2⟩ => {
              have q1 : a > 0 := by linarith
              have q2 : b > 0 := by linarith
              have : a*b > 1 := by exact Right.one_lt_mul_of_lt_of_lt w1 w2 q2
              linarith [h.left]
            }
          }
          cases not_and_or.mp this with
          | inl u => {
            simp at u
            use ⟨i, by simp[e]⟩
            use ⟨j+1, by {
              have := j.isLt
              simp only [List.length] at this
              simp
              linarith
            }⟩
            simp
            match j with
              | ⟨j_val, j_lt⟩ => {
                cases j_val with
                | zero => {
                  simp at hij
                  apply False.elim
                  rw [e] at hij
                  simp at hij
                }
                | succ n => {
                  simp
                  have : 0 < n.succ := by simp
                  apply And.intro
                  rw [e]
                  have : zero'.val < n.succ + 1 := by linarith
                  exact Nat.ne_of_lt this

                  apply And.intro
                  simp [e]
                  exact u
                  exact h.right
                }
              }
          }
          | inr v => {
            simp at v
            use ⟨1, by simp[e]⟩
            use ⟨j + 1, by {
              have := j.isLt
              simp only [List.length] at this
              simp
              linarith
            }⟩
            simp

            match j with
              | ⟨j_val, j_lt⟩ => {
                cases j_val with
                | zero => {
                  simp at hij
                  apply False.elim
                  rw [e] at hij
                  simp at hij
                }
                | succ n => {
                  apply And.intro
                  simp [e]
                  have : 0 < n.succ := by simp
                  have : 1 < n.succ + 1 := by linarith
                  exact Fin.ne_of_lt this
                  simp [e]
                  simp [e] at h
                  have := h.left;
                  have : b ≠ 0 := by {
                    intro q
                    rw [q] at h2
                    simp at h2
                  }
                  apply And.intro
                  exact v
                  exact h.right
                }
              }
          }
        }
      | inr h' => {
        sorry -- same logic as inl
      }
    }
    | inr r => {
      have : i ≠ zero' ∧ j ≠ zero' := by exact not_or.mp r
      match i, j with
      | ⟨0, is⟩, _ => simp at this
      | _, ⟨0, is⟩ => simp at this
      | ⟨Nat.succ n, isn⟩, ⟨Nat.succ m, ism⟩ => {
        use ⟨n + 2, by {
          simp
          simp at isn
          linarith
        }⟩
        use ⟨m + 2, by {
          simp
          simp at ism
          linarith
        }⟩
        simp
        apply And.intro
        simp at hij
        exact hij
        simp at h
        exact h
      }
    }
  }
}
termination_by wow a => a.length

end agm

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  by intros x y
section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry

theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := sorry
    _ ≤ |x| * ε := sorry
    _ < 1 * ε := sorry
    _ = ε := sorry

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  sorry

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  sorry

end

section
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  sorry

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  sorry

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  sorry

end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  sorry

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  sorry

end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry

end
