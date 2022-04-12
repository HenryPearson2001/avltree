open nat
open int

universes u v

/- nil represents a non existant node -/
inductive avlnode (α : Type u)
  | nil                                               : avlnode 
  | node (left : avlnode) (val : α) (right : avlnode) : avlnode

namespace avlnode

variables {α : Type u} [linear_order α] {β : Type v} [linear_order β]

/- use binary tree property of avltree -/
def min : avlnode α → option α
  | nil              := none
  | (node nil val _) := some val
  | (node l _ _)     := min l

def max : avlnode α → option α
  | nil              := none
  | (node _ val nil) := some val
  | (node _ _ r)     := max r

def depth : avlnode α → int
  | nil              := -1
  | (node l _ r)     := if (depth l) ≤ (depth r) then depth r + 1 else depth l + 1

/- applies fold as if traversing in-order (i.e. ~left to right) -/
def foldr (f : α → β → β) : avlnode α → β → β
  | nil b            := b
  | (node l val r) b := foldr l (f val (foldr r b))

/- applies fold as if traversing in-order in reverse (i.e. ~right to left) -/
def foldl (f : α → β → β) : avlnode α → β → β
  | nil b            := b
  | (node l val r) b := foldl r (f val (foldl l b))

@[simp] def rotate_left : avlnode α → avlnode α
  | nil                              := nil
  | (node l1 val1 nil)               := node l1 val1 nil
  | (node l1 val1 (node l2 val2 r2)) := node (node l1 val1 l2) val2 r2

@[simp] def rotate_right : avlnode α → avlnode α
  | nil                              := nil
  | (node nil val1 r1)               := node nil val1 r1
  | (node (node l2 val2 r2) val1 r1) := node l2 val2 (node r2 val1 r1)

/- gives the balance factor of a node -/
def balance_factor : avlnode α → int
  | nil              := 0
  | (node l _ r)     := (depth r) - (depth l)

def balance : avlnode α → avlnode α 
  | nil                                             := nil
  | (node nil valX nil)                             := (node nil valX nil)
  | (node (node lZ valZ rZ) valX nil)               := if balance_factor (node (node lZ valZ rZ) valX nil) ≤ -2 then 
                                                        if 0 ≤ (depth lZ) - (depth rZ) then rotate_right (node (node lZ valZ rZ) valX nil)
                                                        else rotate_right (node (rotate_left (node lZ valZ rZ)) valX nil)
                                                       else (node (node lZ valZ rZ) valX nil)
  | (node nil valX (node lZ valZ rZ))               := if 2 ≤ balance_factor (node nil valX (node lZ valZ rZ)) then 
                                                        if 0 ≤ (depth rZ) - (depth lZ) then rotate_left (node nil valX (node lZ valZ rZ))
                                                        else rotate_left (node nil valX (rotate_right (node lZ valZ rZ)))
                                                        else (node nil valX (node lZ valZ rZ))
  | (node (node lY valY rY) valX (node lZ valZ rZ)) := if 2 ≤ balance_factor (node (node lY valY rY) valX (node lZ valZ rZ)) then
                                                          if 0 ≤ (depth rZ) - (depth lZ) then rotate_left (node (node lY valY rY) valX (node lZ valZ rZ))
                                                          else rotate_left (node (node lY valY rY) valX (rotate_right (node lZ valZ rZ)))
                                                       else if balance_factor (node (node lY valY rY) valX (node lZ valZ rZ)) ≤ -2 then
                                                          if 0 ≤ (depth lY) - (depth rY) then rotate_right (node (node lY valY rY) valX (node lZ valZ rZ))
                                                          else rotate_right (node (rotate_left (node lY valY rY)) valX (node lZ valZ rZ))
                                                       else (node (node lY valY rY) valX (node lZ valZ rZ))
                        
def ins : avlnode α → α → avlnode α
  | nil ins_val            := node nil ins_val nil
  | (node l val r) ins_val := if ins_val ≤ val then balance (node (ins l ins_val) val r)
                              else balance (node l val (ins r ins_val))

def leftmost : avlnode α → avlnode α
  | nil              := nil
  | (node nil val r) := node nil val r
  | (node l val r)   := leftmost l

/- returns nil if empty tree input or there is no successor -/
def successor : avlnode α → avlnode α 
  | nil            := nil
  | (node l val r) := leftmost r

/- function needed for node deletion -/
private def replace_leftmost  : avlnode α → avlnode α → avlnode α 
  | nil n := n
  | (node nil val r) n := n
  | (node l val r) n := node (replace_leftmost l n) val r

/- returns original tree if value not in the tree, otherwise returns new tree -/
def del : avlnode α → α → avlnode α 
  | nil del_val := nil
  | (node l val r) del_val := if del_val < val then balance (node (del l del_val) val r)
                              else if val < del_val then balance (node l val (del r del_val))
                              else match l, r with
                                | nil, nil               := nil 
                                | nil, r2                := r2
                                | l2, nil                := l2
                                | l2, (node nil val3 r3) := node l val3 r3
                                | l2, (node l3 val3 r3)  := match successor (node l val r) with
                                                              | nil               := nil
                                                              | (node l4 val4 r4) := balance (node l val4 (replace_leftmost r r4))
                                                            end  
                              end

/- returns a prop as to whether an element is in the tree -/
def mem : avlnode α → α → Prop 
  | nil mem_val := false
  | (node l val r) mem_val := if mem_val = val then true
                              else if mem_val < val then mem l mem_val
                              else mem r mem_val

/- insert a list of values into an AVL tree -/
def ins_vals : avlnode α → list α → avlnode α 
 | n []      := n
 | n (x::xs) := ins_vals (ins n x) xs

/- build an AVL tree from a list of values -/
def mk_node (vals : list α) : avlnode α := ins_vals nil vals 

/- traversal functions -/
def pre_order : avlnode α → list α 
  | nil            := []
  | (node l val r) := val :: ((pre_order l) ++ (pre_order r))

def in_order : avlnode α → list α 
  | nil            := []
  | (node l val r) := (in_order l) ++ [val] ++ (in_order r)

def post_order : avlnode α → list α 
  | nil            := []
  | (node l val r) := (post_order l) ++ (post_order r) ++ [val]

def empty : avlnode α → Prop 
  | nil := true
  | _   := false

/- prop which checks if a avlnode is well balanced -/
def well_balanced : avlnode α → Prop
  | nil            := true
  | (node l val r) := balance_factor (node l val r) ≤ 1 ∧ -1 ≤ balance_factor (node l val r) ∧ well_balanced l ∧ well_balanced r

instance avlnode_has_repr [has_repr α] : has_repr (avlnode α) := ⟨λ t, repr (pre_order t)⟩

/- datatype that constructs a proof that an avl tree is well formed -/
/- here define well formed to be created from a series of defined insert and delete operations -/
/- thus every empty tree is well formed (so proof given), 
and given a proof n1 is well formed, and that n2 is n1 after either insert or delete performed with val, provide proof n2 is well formed-/
inductive well_formed : avlnode α → Prop
| wf_nil                                             : well_formed nil
| wf_ins {n1 : avlnode α} {n2 : avlnode α} {val : α} : well_formed n1 → n2 = ins n1 val → well_formed n2
| wf_del {n1 : avlnode α} {n2 : avlnode α} {val : α} : well_formed n1 → n2 = del n1 val → well_formed n2


end avlnode

open avlnode 

/- thus define avltree to be an avlnode structure with proof that the structre is well formed -/
def avltree (α : Type u) [linear_order α] : Type u := {t : avlnode α // t.well_formed}

def mk_empty_avltree (α : Type u) [linear_order α] : avltree α := ⟨nil, well_formed.wf_nil⟩

namespace avltree

variables {α : Type u} [linear_order α] {β : Type v} [linear_order β]

def min : avltree α → option α
  | ⟨n, _⟩ := n.min

def max : avltree α → option α
  | ⟨n, _⟩ := n.max

def depth : avltree α → int
  | ⟨n, _⟩ := n.depth

def foldr (f : α → β → β) : avltree α → β → β
  | ⟨n, _⟩ b            := n.foldr f b

/- applies fold as if traversing in-order in reverse (i.e. ~right to left) -/
def foldl (f : α → β → β) : avltree α → β → β
  | ⟨n, _⟩ b            := n.foldl f b

def ins : avltree α → α → avltree α
  | ⟨n, p⟩ val := ⟨n.ins val, well_formed.wf_ins p rfl⟩

def del : avltree α → α → avltree α
  | ⟨n, p⟩ val := ⟨n.del val, well_formed.wf_del p rfl⟩

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









#print option

open avlnode

def myTree : avlnode nat := node (node nil 1 (node nil 2 nil)) 3 (node (node nil 4 nil) 5 (node nil 6 (node nil 7 nil)))

def myNewTree : avlnode nat := node (node (node nil 1 nil) 2 (node nil 3 nil)) 4 (node (node nil 5 (node nil 6 nil)) 7 (node nil 8 nil))

def badlyFormedTree : avlnode nat := node (node (node nil 1 nil) 2 nil) 3 nil


#eval del myNewTree 4

def myFunc : nat → nat → nat 
  | x y := x + 2 * y

#eval foldl myFunc myTree 0
#eval rotate_right myTree
#eval del myTree 5
#eval balance_factor badlyFormedTree
#eval depth badlyFormedTree
#reduce well_formed badlyFormedTree 

#eval post_order myTree

#eval myTree