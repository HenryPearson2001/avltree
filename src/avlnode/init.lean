/-
Copyright (c) 2022 Henry Pearson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Henry Pearson.
-/

import init.data.int.basic

/-!
# AVL node

This file defines a BST type with operations for AVL trees, to be later extended in `avltree.lean`
to a specific AVL tree type with enforced balance properties.

## Main definitions

* `avlnode` is a BST structure with 'in built' option type thus `nil` represents the empty tree,
and `node nil val nil` represents a leaf node.

* `avlnode.depth` is the number of edges between the root and leaf node on path to the leaf of max
length, thus the empty tree `nil` has depth -1, and a leaf node has depth 0.

* `avlnode.size` is the total number of nodes in a tree (this does not include `nil`s).

* `avlnode.rotate_left` and `avlnode.rotate_right` are simple binary tree rotations.

* `avlnode.balance_factor` of a node n is the depth of the right subtree of n subtract the depth 
of the left subtree of n.

* `avlnode.balance` performs one balance operation on a node, as described in 
<https://en.wikipedia.org/wiki/AVL_tree>.

* `avlnode.ins` inserts a single node into a tree using a normal BST insert, then recursively
applies balance along the path from the inserted node back to the root.

* `avlnode.mk_node` builds an avlnode from a list of values.

* `avlnode.well_balanced` returns a Prop which represents whether the structure observes AVL tree
properties (balance factor between -1 and 1 for every node).

## Implementation notes

* Throughout this module, α and β are types with an implemented linear order in order to be able to
build a BST structure - this is enforced automatically.

* Don't use option types in `avlnode` structure definition to allow Lean to detect well founded
recursion.

## References

* <https://en.wikipedia.org/wiki/AVL_tree>
-/

open nat
open int

universes u v

/--
An AVL node is either the empty tree `nil`, or a structure consisting of two subtrees and a value
-/
inductive avlnode (α : Type u)
  | nil                                               : avlnode 
  | node (left : avlnode) (val : α) (right : avlnode) : avlnode

namespace avlnode

variables {α : Type u} [linear_order α] {β : Type v} [linear_order β]

/--
Returns minimum value in tree according to defined ordering on α (returns none if called on empty
tree).
Uses BST property to find value.
-/
def min : avlnode α → option α
  | nil              := none
  | (node nil val _) := some val
  | (node l _ _)     := min l

/--
Returns maximum value in tree according to defined ordering on α (returns none if called on empty
tree).
Uses BST property to find value.
-/
def max : avlnode α → option α
  | nil              := none
  | (node _ val nil) := some val
  | (node _ _ r)     := max r

/--
Returns depth of node, defined as number of edges between the root and leaf nodes on the longest
such path. Thus the depth of the empty tree is defined as -1 and the depth of a leaf node is 0.
-/
def depth : avlnode α → int
  | nil              := -1
  | (node l _ r)     := if (depth l) ≤ (depth r) then depth r + 1 else depth l + 1

/--
Returns the number of nodes in a tree (`nil`s do not count as nodes).
-/
def size : avlnode α → nat
  | nil          := 0
  | (node l _ r) := (size l) + (size r) + 1

/--
Definition of a right fold.
Applies fold as if traversing in-order (i.e. ~left to right) 
-/
def foldr (f : α → β → β) : avlnode α → β → β
  | nil b            := b
  | (node l val r) b := foldr l (f val (foldr r b))

/--
Definition of a left fold.
Applies fold as if traversing in-order in reverse (i.e. ~right to left) 
-/
def foldl (f : α → β → β) : avlnode α → β → β
  | nil b            := b
  | (node l val r) b := foldl r (f val (foldl l b))

/--
Simple left rotation operation on binary tree. Returns the rotated tree.
-/
@[simp] def rotate_left : avlnode α → avlnode α
  | nil                              := nil
  | (node l1 val1 nil)               := node l1 val1 nil
  | (node l1 val1 (node l2 val2 r2)) := node (node l1 val1 l2) val2 r2

/--
Simple right rotation operation on binary tree. Returns the rotated tree.
-/
@[simp] def rotate_right : avlnode α → avlnode α
  | nil                              := nil
  | (node nil val1 r1)               := node nil val1 r1
  | (node (node l2 val2 r2) val1 r1) := node l2 val2 (node r2 val1 r1)

/--
Returns the balance factor of a given node, defined as the depth of the right subtree subtract the
depth of the left subtree.
-/
def balance_factor : avlnode α → int
  | nil              := 0
  | (node l _ r)     := (depth r) - (depth l)

/--
Performs a single balance operation on a node (if balance factor is not between -1 and 1, perform
a sequence of operations to ensure it subsequently is in that range while maintaining BST 
ordering), as defined in <https://en.wikipedia.org/wiki/AVL_tree>.
-/
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
                        
/--
AVL tree insert - inserts a node into the tree as if it is a normal BST then applies balance to
each node on the path from inserted leaf node to root.
-/
def ins : avlnode α → α → avlnode α
  | nil ins_val            := node nil ins_val nil
  | (node l val r) ins_val := if ins_val ≤ val then balance (node (ins l ins_val) val r)
                              else balance (node l val (ins r ins_val))

/--
Returns Prop which represents whether element is in the tree or not.
-/
def mem : avlnode α → α → Prop 
  | nil mem_val := false
  | (node l val r) mem_val := if mem_val = val then true
                              else if mem_val < val then mem l mem_val
                              else mem r mem_val

/--
Insert a list of values into a given AVL tree
-/
def ins_vals : avlnode α → list α → avlnode α 
  | n []      := n
  | n (x::xs) := ins_vals (ins n x) xs

/--
Create a fresh AVL tree from a given list of values.
-/
def mk_node (vals : list α) : avlnode α := ins_vals nil vals 

/--
Traverses tree using pre-order and returns list of values of nodes in given order.
-/
def pre_order : avlnode α → list α 
  | nil            := []
  | (node l val r) := val :: ((pre_order l) ++ (pre_order r))

/--
Traverses tree using in-order and returns list of values of nodes in given order.
-/
def in_order : avlnode α → list α 
  | nil            := []
  | (node l val r) := (in_order l) ++ [val] ++ (in_order r)

/--
Traverses tree using post-order and returns list of values of nodes in given order.
-/
def post_order : avlnode α → list α 
  | nil            := []
  | (node l val r) := (post_order l) ++ (post_order r) ++ [val]

/--
Returns Prop which represents if the tree is the empty tree or not.
-/
def empty : avlnode α → Prop 
  | nil := true
  | _   := false

/-- 
Returns a Prop which represents whether the structure observes AVL tree properties (balance factor 
between -1 and 1 for every node).
-/
def well_balanced : avlnode α → Prop
  | nil            := true
  | (node l val r) := balance_factor (node l val r) ≤ 1 ∧ -1 ≤ balance_factor (node l val r) ∧ well_balanced l ∧ well_balanced r

instance avlnode_has_repr [has_repr α] : has_repr (avlnode α) := ⟨λ t, repr (pre_order t)⟩

end avlnode