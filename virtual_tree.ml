
module Virtual_tree (Data : sig
  type t
  val compress : t -> t -> t
end) = struct

  let next_id =
    let counter = ref 0 in
    fun () ->
      incr counter;
      !counter

  type data = Data.t

  type tree = 
  | Root
  | Node of {
    id : int;
    mutable parent : tree; (* mutable so we can reroute when merging with a branch tree node *)
    mutable child : tree;
    mutable data : data (* needs to be mutable so we can compress it *)
  }
  | Branch of { (* ensures binary tree with unlimited splits *)
    id : int;
    mutable parent : tree;
    mutable left : tree;
    mutable right : tree
  }
  | Leaf of { (* handling point for user *) (* should know if left/right/single child ?? bad idea *)
    id : int;
    mutable parent : tree (* mutable because copy needs to return only one element *)
  }

  let empty() : tree = Leaf({id=next_id(); parent=Root})

  let is_leaf (t : tree) : bool =
    match t with 
    | Leaf _ -> true
    | _ -> false

  let get_parent (child: tree) : tree =
    match child with 
    | Root -> child
    | Node n -> n.parent
    | Branch b -> b.parent
    | Leaf l -> l.parent

  let update_parent_in_child (child : tree) (new_parent : tree) : unit =
    match child with
    | Root -> ()
    | Node n -> n.parent <- new_parent
    | Branch b -> b.parent <- new_parent
    | Leaf l -> l.parent <- new_parent

  let update_child_in_parent (old_child : tree) (new_child : tree) : unit =
    match (get_parent old_child) with 
    | Root -> ()
    | Node n -> 
      if n.child = old_child then n.child <- new_child
      else ()
    | Branch b -> 
      if b.left = old_child then b.left <- new_child
      else if b.right = old_child then b.right <- new_child
      else ()
    | Leaf l -> failwith "Illegal state: a Leaf cannot be a parent."

  let split (leaf : tree) : tree = 
    match leaf with 
    | Root | Node _ | Branch _  -> failwith "Invalid argument: leaf must be a Leaf."
    | Leaf l -> 
      let new_leaf = Leaf({id=next_id(); parent=l.parent}) in
      let b = Branch({id=next_id(); parent=l.parent; left=leaf; right=new_leaf}) in
      l.parent <- b;
      update_parent_in_child new_leaf b; (* now new_leaf's parent is b*)
      update_child_in_parent leaf b; (* now leaf's parent's child is b *)
      new_leaf

  let insert (leaf : tree) (new_data : data) : tree =
    match leaf with 
    | Root | Node _ | Branch _ -> failwith "Illegal argument: leaf must be a Leaf."
    | Leaf l -> 
      match l.parent with 
      | Root -> (* create a node pointing to Root, reroute leaf to that node *)
        let new_node = Node({id=next_id(); parent=Root; child=leaf; data=new_data}) in
        update_parent_in_child leaf new_node; (* now leaf's parent is new_node *)
        leaf
      | Node n -> (* update n's data: compress it with new_data *)
        n.data <- Data.compress n.data new_data;
        leaf
      | Branch b -> (* create a node pointing to b, reroute leaf and b to that node *)
        let new_node = Node({id=next_id(); parent=l.parent; child=leaf; data=new_data}) in
        update_parent_in_child leaf new_node; (* now leaf's parent is new_node *)
        update_child_in_parent l.parent new_node; (* now leaf's parent's child is new_node *)
        leaf
      | Leaf _ -> failwith "Illegal state: a Leaf cannot be a parent."

end