import data.bitvec
import data.dlist
import data.list.perm
import util.logic
import util.control.applicative
import util.control.monad.non_termination
import util.data.option
import util.meta.tactic

universes u v w w'

open nat list (hiding bind) function

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

@[simp]
lemma heap_emp_disjoint (h : heap)
: heap.emp ## h :=
by { dunfold disjoint heap.emp, intros, left, refl }

@[simp]
lemma disjoint_heap_emp (h : heap)
: h ## heap.emp :=
by { dunfold disjoint heap.emp, intros, right, refl }

@[simp]
lemma heap_emp_part'_eq_self (h : heap)
: part' heap.emp h (heap_emp_disjoint _) = h :=
begin
  apply funext, intro,
  unfold part',
  cases (h x) ; simp [heap.emp,has_orelse.orelse,option.orelse]
end

@[simp]
lemma part'_heap_emp_eq_self (h : heap)
: part' h heap.emp (disjoint_heap_emp _) = h :=
begin
  apply funext, intro,
  unfold part',
  cases (h x) ; simp [heap.emp,has_orelse.orelse,option.orelse]
end

def heap.mk : pointer → list word → heap
| _ [] := heap.emp
| p (v :: vs) := λ q, maplet p v q <|> heap.mk (p+1) vs q

lemma maplet_disjoint_heap_mk (p : pointer) (v : word) (vs : list word)
: disjoint (maplet p v) (heap.mk (p + 1) vs) :=
sorry

def left_combine (h₀ h₁ : heap) : heap
 | p := h₀ p <|> h₁ p

def heap.delete : pointer → ℕ → heap → heap
 | p 0 h q := h q
 | p (succ n) h q :=
if p = q then none
else heap.delete (p+1) n h q

infix ` <+ `:54 := left_combine

@[symm]
lemma disjoint_symm {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: h₁ ## h₀ :=
assume p, or.symm (h p)

lemma part'_comm {h₀ h₁ : heap}
  (h : h₀ ## h₁)
: part' h₀ h₁ = part' h₁ h₀ (disjoint_symm h) :=
begin
  funext p, unfold part',
  cases h p with h h ; simp [h],
end

lemma part_disjoint_assoc_left {h₀ h₁ h₂ : heap}
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

lemma part_disjoint_assoc_right {h₀ h₁ h₂ : heap}
  (Hdisj : h₀ ## h₁)
  (Hdisj' : h₁ ## h₂)
  (h : h₀ ## part' h₁ h₂)
: part' h₀ h₁ ## h₂ :=
begin
  intro p,
  cases h p with h' h' ; unfold part' at *,
  { simp [h',Hdisj' p], },
  { rw or_else_eq_none_iff at h',
    simp [h'.right] },
end

@[simp]
lemma eq_emp_of_part' (hp a : heap)
  (h  : a ## hp)
: a = part' a hp ↔ hp = heap.emp :=
sorry

lemma part'_assoc {h₀ h₁ h₂ : heap}
  (Hdisj₀ : h₀ ## h₁)
  (Hdisj₁ : h₁ ## h₂)
  (Hdisj₂ : part' h₀ h₁ ## h₂)
  (Hdisj₃ : h₀ ## part' h₁ h₂)
: part' (part' h₀ h₁) h₂ Hdisj₂ = part' h₀ (part' h₁ h₂) Hdisj₃ :=
sorry

lemma delete_part'_heap_mk {p : pointer} {vs : list word} {hp : heap}
  (h : heap.mk p vs ## hp)
: heap.delete p (length vs) (part' (heap.mk p vs) hp) = hp :=
sorry

lemma part'_disjoint {h₁ h₂ h₃ : heap}
  {H₀ : h₂ ## h₃}
  (H₁ : h₁ ## h₃)
  (H₁ : h₁ ## h₂)
: part' h₂ h₃ ## h₁ :=
sorry

lemma disjoint_part' {h₁ h₂ h₃ : heap}
  {H₀ : h₂ ## h₃}
  (H₁ : h₁ ## h₃)
  (H₁ : h₁ ## h₂)
: h₁ ## part' h₂ h₃ :=
sorry

lemma disjoint_of_part'_disjoint_right {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ ## h₁)
: h₁ ## h₃ :=
begin
  intro p,
  cases H₀ p with H₂ H₂,
  { unfold part' at H₂,
    rw or_else_eq_none_iff at H₂,
    simp [H₂.right] },
  { simp [H₂] }
end

lemma disjoint_of_part'_disjoint_left {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : part' h₂ h₃ ## h₁)
: h₁ ## h₂ :=
begin
  have H₁ := disjoint_symm H₁,
  apply disjoint_of_part'_disjoint_right H₁,
  rw part'_comm, apply H₀,
end

lemma disjoint_of_disjoint_part'_right {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : h₁ ## part' h₂ h₃)
: h₁ ## h₃ :=
sorry

lemma disjoint_of_disjoint_part'_left {h₁ h₂ h₃ : heap}
  (H₁ : h₂ ## h₃)
  (H₀ : h₁ ## part' h₂ h₃)
: h₁ ## h₂ :=
sorry

def heap.insert (hp : heap) (p : pointer) (v : word) : heap
 | q := if p = q then some v else hp q

lemma part'_insert (hp hp' : heap) (p : pointer) (v : word)
  (h₀ : hp.insert p v ## hp')
  (h₁ : hp ## hp')
: part' (hp.insert p v) hp' = (part' hp hp').insert p v :=
sorry

lemma maplet_insert_disjoint_iff (p : pointer) (v v' : word) (hp : heap)
: (maplet p v).insert p v' ## hp ↔ maplet p v ## hp :=
sorry
