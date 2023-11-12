import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Basic

namespace agm

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
