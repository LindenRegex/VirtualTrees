
module Virtual_tree (Data : sig
  type t
  val compress : t -> t -> t
end) = struct

  type data = Data.t

  type tree = 
  | Root
  | Node of {
    mutable parent : tree; (* mutable so we can reroute when merging with a branch tree node *)
    mutable child : tree;
    mutable data : data (* needs to be mutable so we can compress it *)
  }
  | Branch of {
    mutable parent : tree;
    mutable left : tree;
    mutable right : tree
  }
  | Leaf of tree (* handling point for user *) (* should know if left/right/single child ??*)

  let empty() : tree = Leaf(Root)

end