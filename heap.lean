import data.bitvec
import data.dlist
import util.logic
import util.control.applicative
import util.control.monad.non_termination

universes u v w w'

open nat list function

@[reducible]
def pointer := ℕ

structure word :=
to_word :: (to_ptr : ℕ)

instance : has_zero word := ⟨ ⟨ 0 ⟩ ⟩
instance : has_one word := ⟨ ⟨ 1 ⟩ ⟩
instance : has_add word := ⟨ λ x y, ⟨ x.to_ptr + y.to_ptr ⟩ ⟩

def heap := pointer → option word

def disjoint (h₀ h₁ : heap) :=
(∀ p, h₀ p = none ∨ h₁ p = none)

infix ` ## `:51 := disjoint

def part'  (h₀ h₁ : heap) (_ : h₀ ## h₁) : heap
 | p := h₀ p <|> h₁ p

def maplet (p : pointer) (v : word) : heap
  | q :=
if p = q then some v else none

def heap.emp : heap :=
λ _, none

lemma heap_emp_disjoint (h : heap)
: heap.emp ## h :=
by { unfold disjoint heap.emp, intros, left, refl }

@[simp]
lemma heap_emp_part_eq_self (h : heap)
: part' heap.emp h (heap_emp_disjoint _) = h :=
begin
  apply funext, intro,
  unfold part',
  cases (h x) ; simp [heap.emp,has_orelse.orelse,option_orelse]
end

def heap.mk : pointer → list word → heap
| _ [] := heap.emp
| p (v :: vs) := λ q, maplet p v q <|> heap.mk (p+1) vs q

def left_combine (h₀ h₁ : heap) : heap
 | p := h₀ p <|> h₁ p

def heap.delete : pointer → ℕ → heap → heap
 | p 0 h q := h q
 | p (succ n) h q :=
if p = q then none
else heap.delete (p+1) n h q

infix ` <+ `:54 := left_combine

section noncomp

local attribute [instance] classical.prop_decidable

noncomputable def part (h₀ h₁ : heap) : option heap :=
if Hd : disjoint h₀ h₁
then some (part' h₀ h₁ Hd)
else none

end noncomp

lemma part_comm (h₀ h₁ : heap)
: part h₀ h₁ = part h₁ h₀ :=
sorry

lemma disjoint_symm {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: h₁ ## h₀ :=
sorry

lemma part_comm' {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: part' h₀ h₁ h = part' h₁ h₀ (disjoint_symm h) :=
sorry

lemma part'_part_assoc {h₀ h₁ h₂ : heap}
  (Hdisj : disjoint h₀ h₁)
  (Hdisj' : disjoint h₁ h₂)
: part (part' h₀ h₁ Hdisj) h₂ = part h₀ (part' h₁ h₂ Hdisj') := sorry

lemma disjoint_of_part {h h₀ h₁ : heap}
  (HH : some h = part h₀ h₁)
: h₀ ## h₁ :=
sorry

lemma part'_of_part {h h₀ h₁ : heap}
  (H : some h = part h₀ h₁)
: h = part' h₀ h₁ (disjoint_of_part H) :=
sorry

lemma disjoint_disjoint {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ H₁ ## h₁)
: h₁ ## h₃ :=
sorry
