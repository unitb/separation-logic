import data.bitvec
import data.dlist
import util.logic
import util.control.applicative
import util.control.monad.non_termination
import util.data.option
import util.meta.tactic

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

def part'  (h₀ h₁ : heap) (_ : h₀ ## h₁ . tactic.assumption) : heap
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
  cases (h x) ; simp [heap.emp,has_orelse.orelse,option.orelse]
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
if Hd : h₀ ## h₁
then some (part' h₀ h₁)
else none

end noncomp

lemma disjoint_symm {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: h₁ ## h₀ :=
assume p, or.symm (h p)

lemma part_comm' {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: part' h₀ h₁ = part' h₁ h₀ (disjoint_symm h) :=
begin
  funext p, unfold part',
  cases h p with h h ; simp [h],
end

lemma part_comm (h₀ h₁ : heap)
: part h₀ h₁ = part h₁ h₀ :=
begin
  unfold part,
  cases classical.em (h₀ ## h₁) with H H,
  { have H' := disjoint_symm H,
    simp [dif_pos,H,H',part_comm' H] },
  { have H' := mt disjoint_symm H,
    simp [dif_neg,H,H'] }
end

lemma disjoint_of_part {h h₀ h₁ : heap}
  (HH : some h = part h₀ h₁)
: h₀ ## h₁ :=
begin
  unfold part at HH,
  apply classical.by_contradiction _,
  intro H,
  rw [dif_neg] at HH,
  { contradiction },
  { assumption }
end

lemma part_disjoint_assoc {h₀ h₁ h₂ : heap}
  (Hdisj : h₀ ## h₁)
  (Hdisj' : h₁ ## h₂)
  (h : part' h₀ h₁ Hdisj ## h₂)
: h₀ ## part' h₁ h₂ Hdisj' :=
begin
  intro p,
  cases h p with h' h' ; unfold part' at *,
  { rw or_else_eq_none_iff at h',
    simp [h'.left] },
  { simp [h',Hdisj p], },
end

lemma part'_part_assoc {h₀ h₁ h₂ : heap}
  (Hdisj : disjoint h₀ h₁)
  (Hdisj' : disjoint h₁ h₂)
: part (part' h₀ h₁) h₂ = part h₀ (part' h₁ h₂) :=
begin
  unfold part,
  cases classical.em (part' h₀ h₁ Hdisj ## h₂) with h h,
  { have h' : (h₀ ## part' h₁ h₂ Hdisj') := part_disjoint_assoc _ _ h,
    simp [dif_pos,h,h'],
    apply congr_arg,
    funext p, simp [part',or_else_assoc], },
  { have h' : ¬ (h₀ ## part' h₁ h₂ Hdisj'),
    { rw part_comm',
      apply mt disjoint_symm,
      apply mt (part_disjoint_assoc _ _),
      apply mt disjoint_symm,
      rw part_comm',
      apply h,
      apply disjoint_symm Hdisj },
    simp [dif_neg,h,h'] }
end

lemma part'_of_part {h h₀ h₁ : heap}
  (H : some h = part h₀ h₁)
: h = part' h₀ h₁ (disjoint_of_part H) :=
begin
  unfold part at H, dedup,
  simp [dif_pos,disjoint_of_part H] at H_1,
  injection H_1,
end

lemma disjoint_disjoint {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ H₁ ## h₁)
: h₁ ## h₃ :=
begin
  intro p,
  cases H₀ p with H₂ H₂,
  { unfold part' at H₂,
    rw or_else_eq_none_iff at H₂,
    simp [H₂.right] },
  { simp [H₂] }
end
