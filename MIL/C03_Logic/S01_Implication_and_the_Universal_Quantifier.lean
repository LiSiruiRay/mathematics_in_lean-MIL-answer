import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

#check mul_le_mul_right
#check mul_le_mul

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by
intro x y ε epo elo xale yale
calc
  |x * y| = |x| * |y| := by
    apply abs_mul
  _ ≤ |x| * ε := by
    apply mul_le_mul
    linarith
    linarith
    exact abs_nonneg y
    exact abs_nonneg x
  _ < 1 * ε := by
    apply mul_lt_mul
    linarith
    linarith
    exact epo
    linarith
  _ = ε := by
    exact one_mul ε

















-- by
--   intro x y ε epos elo xle yle
--   calc
--     |x * y| = |x| * |y| := by
--       rw [abs_mul x y]
--     _ ≤ |x| * ε := by
--       apply mul_le_mul -- conver the problem to proving the requirement of the theorem
--       linarith
--       linarith
--       exact abs_nonneg y -- part one of the condition
--       exact abs_nonneg x -- part two of the condition
--     _ < 1 * ε := by
--       rw [mul_lt_mul_right epos]
--       linarith
--     _ = ε := by
--       rw [one_mul]


-- by
--   intro x y ε elz elo xale yale
--   calc
--     |x * y| = |x| * |y| := by
--       exact abs_mul x y
--     _ ≤ |x| * ε := by
--       apply mul_le_mul
--       linarith
--       linarith
--       exact abs_nonneg y
--       exact abs_nonneg x
--     _ < 1 * ε := by
--       rw [mul_lt_mul_right elz]
--       linarith
--     _ = ε := by
--       exact one_mul ε


section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check abs_mul
#check abs_nonneg
#check mul_lt_mul
#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
by
intro x y ε epos elo xale yale
calc
  |x * y| = |x| * |y| := by
    apply abs_mul
  _ ≤ |x| * ε := by
    apply mul_le_mul
    linarith
    linarith
    exact abs_nonneg y
    exact abs_nonneg x
  _ < 1 * ε := by
    apply mul_lt_mul
    linarith
    linarith
    exact epos
    linarith




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


example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · exact hfa x
  -- apply hfa
  · apply hgb x

#check mul_nonneg

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  by
  intro x
  apply mul_nonneg
  · exact nnf x
  · exact nng x

#check mul_le_mul

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
by
  intro x
  dsimp
  apply mul_le_mul
  · exact hfa x
  · exact hgb x
  · exact nng x
  · exact nna

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

#check mul_le_mul_of_nonneg_left

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  dsimp
  apply mul_le_mul_of_nonneg_left
  · exact mf aleb
  · exact nnc

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) (nnc)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
intro a b aleb
dsimp
apply mf
apply mg
exact aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
fun a b aleb ↦ mf <| mg aleb


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
  intro x
  dsimp
  rw [of, og, neg_mul_neg]

#check neg_mul
example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef, og]
  linarith

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  rw [ef, og, neg_neg]

end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro a b x xr
  apply a at xr
  apply b at xr
  exact xr

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
  fun a b x xr ↦
  b a (xr)


end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

#check le_trans
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
intro x xs
apply h at xs
apply le_trans xs h'

end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

#check mul_right_inj
example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  dsimp at h'
  rw [mul_right_inj'] at h'
  exact h'
  exact h

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x :=
fun x₁ x₂ h' ↦ (mul_right_inj' h).mp h'

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

#check Injective

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x y h
  dsimp at h -- why cannot apply injg first?
  apply injf
  apply injg
  exact h
end
