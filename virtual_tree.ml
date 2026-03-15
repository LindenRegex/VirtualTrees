module Virtual_tree (Data : sig
  type t
  val compress : t -> t -> t
  val to_string : t -> string (* debugging purposes *)
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

  let get_id (t: tree): int = 
    match t with 
    | Root -> 0
    | Node n -> n.id
    | Branch b -> b.id
    | Leaf l -> l.id

  let equal (t1: tree) (t2: tree): bool = (get_id t1) = (get_id t2)

  let is_empty (t: tree): bool =
    match t with 
    | Root | Node _ | Branch _ -> false
    | Leaf l ->
      match l.parent with 
      | Root -> true
      | _ -> false

  let rec print (t: tree): unit =
    match t with 
    | Root -> Printf.printf "Root\n"
    | Node n -> 
      Printf.printf "Node %d (%s) -> " n.id (Data.to_string n.data);
      print n.parent
    | Branch b -> 
      Printf.printf "Branch %d -> " b.id;
      print b.parent
    | Leaf l -> 
      Printf.printf "Leaf %d -> " l.id; 
      print l.parent

  let empty() : tree = Leaf({id=next_id(); parent=Root})

  let is_leaf (t : tree) : bool =
    match t with 
    | Leaf _ -> true
    | _ -> false

  let is_node (t : tree) : bool =
    match t with 
    | Node _ -> true
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
      if (equal n.child old_child) then n.child <- new_child
      else ()
    | Branch b -> 
      if (equal b.left old_child) then (b.left <- new_child)
      else if (equal b.right old_child) then (b.right <- new_child)
      else ()
    | Leaf l -> failwith "Illegal state: a Leaf cannot be a parent."

  let split (leaf : tree) : tree = 
    match leaf with 
    | Root | Node _ | Branch _  -> failwith "Invalid argument: leaf must be a Leaf."
    | Leaf l -> 
      let new_leaf = Leaf({id=next_id(); parent=l.parent}) in
      let b = Branch({id=next_id(); parent=l.parent; left=leaf; right=new_leaf}) in
      update_child_in_parent leaf b; (* now leaf's parent's child is b *)
      update_parent_in_child new_leaf b; (* now new_leaf's parent is b*)
      l.parent <- b;
      new_leaf

  let insert (leaf : tree) (new_data : data) : unit =
    match leaf with 
    | Root | Node _ | Branch _ -> failwith "Illegal argument: leaf must be a Leaf."
    | Leaf l -> (
      match l.parent with 
      | Root -> (* create a node pointing to Root, reroute leaf to that node *)
        let new_node = Node({id=next_id(); parent=Root; child=leaf; data=new_data}) in
        update_parent_in_child leaf new_node (* now leaf's parent is new_node *)
      | Node n -> (* update n's data: compress it with new_data *)
        n.data <- Data.compress n.data new_data
      | Branch b -> (* create a node pointing to b, reroute leaf and b to that node *)
        let new_node = Node({id=next_id(); parent=l.parent; child=leaf; data=new_data}) in
        update_child_in_parent leaf new_node; (* now leaf's parent's child is new_node *)
        update_parent_in_child leaf new_node; (* now leaf's parent is new_node *)
      | Leaf _ -> failwith "Illegal state: a Leaf cannot be a parent."
    )

  let merge_and_compress_nodes (parent : tree) (child : tree) : unit =
    match parent, child with 
    | Node n1, Node n2 -> (* compress n2's data into n1, reroute n2's child to n1 *)
      n1.data <- Data.compress n1.data n2.data;
      update_parent_in_child n2.child parent; (* now n2's child's parent is n1 *)
      n1.child <- n2.child (* now n1's child in n2's child*)
    | _, _ -> ()

  let delete_from_branch (to_del : tree) (branch : tree) : unit =
    match branch with 
    | Root | Node _ -> failwith "Illegal argument: branch must be a Branch."
    | Branch b -> 
      let other_child = if (equal b.left to_del) then b.right else if (equal b.right to_del) then b.left 
                  else invalid_arg "Argument to_del is not a child of branch."
                in
      if is_node other_child && is_node b.parent then ((* must merge the two nodes and compress their data *)
        merge_and_compress_nodes b.parent other_child
      ) else (
        update_child_in_parent branch other_child; (* now branch's parent's child is other_child *)
        update_parent_in_child other_child b.parent (* now other_child's parent is b.parent*)
      )
    | Leaf _ -> failwith "Illegal argument: branch must be a Branch."

  (* deletes all parents until it gets to a Branch *)
  (* if that Branch's parent is a node, compress node's data with branch's other child *)
  let rec delete (to_delete : tree) : unit =
    match to_delete with 
    | Root -> ()
    | Node n -> (
      match n.parent with
      | Root -> ()
      | Node n -> (* Impossible: to_delete and its parent (a Node) should be compressed into one Node *)
        failwith "Illegal state: A Node's parent cannot be a Node." 
      | Branch b ->
        delete_from_branch to_delete n.parent
      | Leaf _ -> failwith "Illegal state: a Leaf cannot be a parent."
    )
    | Branch _ -> () (* branches cannot be deleted, must delete its children separately *)
    | Leaf l -> (
      match l.parent with
      | Root -> ()
      | Node n -> (* Delete the node recursively. The node parent is either Root or a Branch *)
        delete l.parent
      | Branch b -> (* Replace the branch with its other child. Compress if possible. *)
        delete_from_branch to_delete l.parent
      | Leaf _ -> failwith "Illegal state: a Leaf cannot be a parent."
    )

end