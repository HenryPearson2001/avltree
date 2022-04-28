/-
Copyright (c) 2022 Henry Pearson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Henry Pearson.
-/

import avlnode.init
import avlnode.basic

/-!
# AVL tree

This files follows from both `avlnode.init.lean` and `avlnode.basic.lean`, and defines the avltree
type (which is essentially the set of avlnode structures with the correct balance factor 
properties). It also defines a series of basic operations on this type, most importantly the `ins`
operation which automatically constructs a proof that the tree is well balanced after an insert.

## Main definitions

* `avltree` is the type of avlnodes that observe the `avlnode.well_balanced` property (each node in 
the tree has a balance factor of between -1 and 1). The structure consists of the avlnode tree
structure and a proof that the structure is well_balanced.

* `avltree.depth` is the number of edges between the root and leaf node on path to the leaf of max
length, thus the empty tree `⟨nil, _⟩` has depth -1, and a leaf node has depth 0.

* `avltree.size` is the total number of nodes in a tree (this does not include `nil`s).

* `avltree.ins` inserts a single node into a tree using defined `avlnode.ins` and then constructs
a proof this new tree is well balanced using `avlnode.wb_n_then_wb_ins_n_val`.

* `avltree.mk_node` builds an avltree from a list of values.

* `avltree.balance_factor` of a tree ⟨n, _⟩ is the depth of the right subtree of n subtract the depth 
of the left subtree of n.

## Implementation notes

* Throughout this module, α and β are types with an implemented linear order in order to be able to
build a BST structure - this is enforced automatically.
-/

universes u v

open avlnode 

/--
Structure consisting of an avlnode structure n alongside a proof that n is well balanced (all nodes
in n have balance factor between -1 and 1).
-/
def avltree (α : Type u) [linear_order α] : Type u := {t : avlnode α // t.well_balanced}

/--
Construct the empty avltree (empty tree and proof the empty tree is balanced).
-/
def mk_empty_avltree (α : Type u) [linear_order α] : avltree α := ⟨nil, wb_nil⟩

namespace avltree

variables {α : Type u} [linear_order α] {β : Type v} [linear_order β]

/--
Returns minimum value in tree according to defined ordering on α (returns none if called on empty
tree).
-/
def min : avltree α → option α
  | ⟨n, _⟩ := n.min

/--
Returns maximum value in tree according to defined ordering on α (returns none if called on empty
tree).
-/
def max : avltree α → option α
  | ⟨n, _⟩ := n.max

/--
Returns depth of node, defined as number of edges between the root and leaf nodes on the longest
such path. Thus the depth of the empty tree is defined as -1 and the depth of a leaf node is 0.
-/
def depth : avltree α → int
  | ⟨n, _⟩ := n.depth

/--
Returns the number of nodes in a tree (`⟨nil, _⟩`s do not count as nodes).
-/
def size : avltree α → nat
  | ⟨n, _⟩ := n.size

/--
Definition of a right fold.
Applies fold as if traversing in-order (i.e. ~left to right) 
-/
def foldr (f : α → β → β) : avltree α → β → β
  | ⟨n, _⟩ b            := n.foldr f b

/--
Definition of a left fold.
Applies fold as if traversing in-order in reverse (i.e. ~right to left) 
-/
def foldl (f : α → β → β) : avltree α → β → β
  | ⟨n, _⟩ b            := n.foldl f b

/--
Insert a new value into an avltree - automatically constructs a proof that the new structure is 
well balanced using `avlnode.wb_n_then_wb_ins_n_val`.
-/
def ins : avltree α → α → avltree α
  | ⟨n, p⟩ val := ⟨n.ins val, wb_n_then_wb_ins_n_val n val p⟩

/--
Returns Prop which represents whether element is in the tree or not.
-/
def mem : avltree α → α → Prop
  | ⟨n, _⟩ val := n.mem val 

/--
Insert a list of values into a given AVL tree
-/
def ins_vals : avltree α → list α → avltree α 
 | t []      := t
 | t (x::xs) := ins_vals (ins t x) xs

/--
Create a fresh AVL tree from a given list of values.
-/
def mk_avltree (vals : list α) : avltree α := ins_vals (mk_empty_avltree α) vals

/--
Traverses tree using pre-order and returns list of values of nodes in given order.
-/
def pre_order : avltree α → list α 
  | ⟨n, _⟩ := n.pre_order

/--
Traverses tree using in-order and returns list of values of nodes in given order.
-/
def in_order : avltree α → list α 
  | ⟨n, _⟩ := n.in_order

/--
Traverses tree using post-order and returns list of values of nodes in given order.
-/
def post_order : avltree α → list α 
  | ⟨n, _⟩ := n.post_order

/--
Returns Prop which represents if the tree is the empty tree or not.
-/
def empty : avltree α → Prop 
  | ⟨n, _⟩ := n.empty

/--
Returns the balance factor of a given node, defined as the depth of the right subtree subtract the
depth of the left subtree.
-/
def balance_factor : avltree α → int
  | ⟨n, _⟩ := n.balance_factor
  
end avltree