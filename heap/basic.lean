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

namespace heap

def disjoint (h₀ h₁ : heap) :=
(∀ p, h₀ p = none ∨ h₁ p = none)

infix ` ## `:51 := disjoint

def part'  (h₀ h₁ : heap) (_ : h₀ ## h₁ . tactic.assumption) : heap
 | p := h₀ p <|> h₁ p

def maplet (p : pointer) (v : word) : heap
  | q :=
if p = q then some v else none

protected def emp : heap :=
λ _, none

section classical

local attribute [instance] classical.prop_decidable

noncomputable def part  : option heap → option heap → option heap
| (some hp₀) (some hp₁) :=
if h : hp₀ ## hp₁
then some $ part' hp₀ hp₁
else none
| _ _ := none

end classical

protected def mk : pointer → list word → heap
| _ [] := heap.emp
| p (v :: vs) := λ q, maplet p v q <|> mk (p+1) vs q

protected def delete : pointer → ℕ → heap → heap
 | p 0 h q := h q
 | p (succ n) h q :=
if p = q then none
else delete (p+1) n h q

protected def insert (hp : heap) (p : pointer) (v : word) : heap
 | q := if p = q then some v else hp q

def left_combine (h₀ h₁ : heap) : heap
 | p := h₀ p <|> h₁ p

infix ` <+ `:54 := left_combine

end heap
