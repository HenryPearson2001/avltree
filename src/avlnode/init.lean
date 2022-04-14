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

def size : avlnode α → nat
  | nil          := 0
  | (node l _ r) := (size l) + (size r) + 1

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

end avlnode