import avlnode.init
import avlnode.basic

universes u v

open avlnode 

/- an avltree is an avlnode with the well balanced property -/
def avltree (α : Type u) [linear_order α] : Type u := {t : avlnode α // t.well_balanced}

def mk_empty_avltree (α : Type u) [linear_order α] : avltree α := ⟨nil, wb_nil⟩

namespace avltree

variables {α : Type u} [linear_order α] {β : Type v} [linear_order β]

def min : avltree α → option α
  | ⟨n, _⟩ := n.min

def max : avltree α → option α
  | ⟨n, _⟩ := n.max

def depth : avltree α → int
  | ⟨n, _⟩ := n.depth

def size : avltree α → nat
  | ⟨n, _⟩ := n.size

def foldr (f : α → β → β) : avltree α → β → β
  | ⟨n, _⟩ b            := n.foldr f b

/- applies fold as if traversing in-order in reverse (i.e. ~right to left) -/
def foldl (f : α → β → β) : avltree α → β → β
  | ⟨n, _⟩ b            := n.foldl f b

def ins : avltree α → α → avltree α
  | ⟨n, p⟩ val := ⟨n.ins val, wb_n_then_wb_ins_n_val n val p⟩

def mem : avltree α → α → Prop
  | ⟨n, _⟩ val := n.mem val 

/- insert a list of values into an AVL tree -/
def ins_vals : avltree α → list α → avltree α 
 | t []      := t
 | t (x::xs) := ins_vals (ins t x) xs

/- create avltree from list of values -/
def mk_avltree (vals : list α) : avltree α := ins_vals (mk_empty_avltree α) vals

/- traversal functions -/
def pre_order : avltree α → list α 
  | ⟨n, _⟩ := n.pre_order

def in_order : avltree α → list α 
  | ⟨n, _⟩ := n.in_order

def post_order : avltree α → list α 
  | ⟨n, _⟩ := n.post_order

def empty : avltree α → Prop 
  | ⟨n, _⟩ := n.empty

def balance_factor : avltree α → int
  | ⟨n, _⟩ := n.balance_factor

def well_balanced : avltree α → Prop
  | ⟨n, _⟩ := n.well_balanced
  
end avltree
