(* The distinguished Set level must be retained even if it does not occur
   syntactically in the exported term. This helper is shared with the test. *)
let project levels graph =
  UGraph.constraints_for
    ~kept:(Univ.Level.Set.add Univ.Level.set levels) graph
