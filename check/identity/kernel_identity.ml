(* Isolated, read-only kernel identity exporter prototype for Rocq 9.1.1.
   No proofs are generated; no project modules are loaded by this module.
   Alpha names of local binders and non-kernel case-printing hints are omitted.
   Every other supported term field is explicit. Unsupported roots fail closed. *)
open Names
open Constr
open Declarations

type json = S of string | I of int | B of bool | L of json list | O of (string * json) list | N
let quote s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (fun c -> match c with
    | '"' -> Buffer.add_string b "\\\""
    | '\\' -> Buffer.add_string b "\\\\"
    | c when Char.code c < 32 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"'; Buffer.contents b
let rec encode = function
  | S s -> quote s | I i -> string_of_int i | B b -> string_of_bool b | N -> "null"
  | L xs -> "[" ^ String.concat "," (List.map encode xs) ^ "]"
  | O xs -> "{" ^ String.concat "," (List.map (fun (k,v) -> quote k ^ ":" ^ encode v) xs) ^ "}"
let arr f xs = L (Array.to_list (Array.map f xs))
let tag n xs = O (("tag",S n)::xs)
let reject s = CErrors.user_err Pp.(str ("KernelIdentity: " ^ s))
let dirpath d = L (List.rev_map (fun x -> S (Id.to_string x)) (DirPath.repr d))
let rec modpath = function
  | ModPath.MPfile d -> tag "MPfile" ["path",dirpath d]
  | ModPath.MPdot (m,l) -> tag "MPdot" ["parent",modpath m; "label",S(Label.to_string l)]
  | ModPath.MPbound _ -> reject "uninstantiated functor/module parameter (MPbound) is unsupported"
let kernel_name k = let (m,l)=KerName.repr k in O ["module",modpath m;"label",S(Label.to_string l)]
let constant c = O ["user",kernel_name(Constant.user c);"canonical",kernel_name(Constant.canonical c)]
let mutual m = O ["user",kernel_name(MutInd.user m);"canonical",kernel_name(MutInd.canonical m)]
let inductive (m,i) = O ["mutual",mutual m;"index",I i]
let constructor (i,c) = O ["inductive",inductive i;"index",I c]
let projection p = O ["constant",constant(Projection.constant p);
  "inductive",inductive(Projection.inductive p);"npars",I(Projection.npars p);
  "arg",I(Projection.arg p);"label",S(Label.to_string(Projection.label p));
  "unfolded",B(Projection.unfolded p)]

type context = { mutable levels : Univ.Level.Set.t }
let level ctx l =
  if Univ.Level.is_set l then (ctx.levels <- Univ.Level.Set.add l ctx.levels; tag "Set" [])
  else match Univ.Level.var_index l,Univ.Level.name l with
  | Some i,_ -> tag "LevelVar" ["index",I i]
  | None,Some g ->
      ctx.levels <- Univ.Level.Set.add l ctx.levels;
      let (p,s,i)=Univ.UGlobal.repr g in tag "LevelGlobal" ["path",dirpath p;"name",S s;"index",I i]
  | None,None -> reject "unknown universe level representation"
let qvar q = match Sorts.QVar.repr q with
  | Sorts.QVar.Var i -> tag "QVar" ["index",I i]
  | Sorts.QVar.Global g -> let p,i=Sorts.QGlobal.repr g in tag "QGlobal" ["path",dirpath p;"name",S(Id.to_string i)]
  | Sorts.QVar.Unif _ -> reject "unresolved quality variable"
let quality = function
  | Sorts.Quality.QVar q -> qvar q
  | Sorts.Quality.QConstant Sorts.Quality.QProp -> S "QProp"
  | Sorts.Quality.QConstant Sorts.Quality.QSProp -> S "QSProp"
  | Sorts.Quality.QConstant Sorts.Quality.QType -> S "QType"
let relevance = function
  | Sorts.Relevant -> S "Relevant" | Sorts.Irrelevant -> S "Irrelevant"
  | Sorts.RelevanceVar q -> tag "RelevanceVar" ["quality",qvar q]
let binder a = O ["relevance",relevance(Context.binder_relevance a)]
let universe ctx u =
  let items = List.map (fun(l,n) -> O["level",level ctx l;"offset",I n]) (Univ.Universe.repr u) in
  L(List.sort (fun a b -> String.compare (encode a) (encode b)) items)
let sort ctx = function
  | Sorts.SProp -> S "SProp" | Sorts.Prop -> S "Prop" | Sorts.Set -> S "Set"
  | Sorts.Type u -> tag "Type" ["universe",universe ctx u]
  | Sorts.QSort(q,u) -> tag "QSort" ["quality",qvar q;"universe",universe ctx u]
let instance ctx u = let(q,l)=UVars.Instance.to_array u in O["qualities",arr quality q;"levels",arr(level ctx) l]
let constraint_json ctx (l,r,h) =
  O["left",level ctx l;"relation",S(match r with Univ.Lt->"Lt"|Univ.Le->"Le"|Univ.Eq->"Eq");"right",level ctx h]
let constraints ctx cs =
  L(List.sort (fun a b -> String.compare (encode a) (encode b))
      (List.map (constraint_json ctx) (Univ.Constraints.elements cs)))
let universes ctx = function
  | Monomorphic -> S "Monomorphic"
  | Polymorphic abs -> let c=UVars.AbstractContext.repr abs in
      tag "Polymorphic" ["instance",instance ctx (UVars.UContext.instance c);
                          "constraints",constraints ctx (UVars.UContext.constraints c)]
let cast_kind = function VMcast->S"VMcast"|NATIVEcast->S"NATIVEcast"|DEFAULTcast->S"DEFAULTcast"
let rec term ctx c = match Constr.kind c with
  | Rel i -> tag "Rel" ["index",I i]
  | Var _ -> reject "open section/local Var is unsupported"
  | Meta _ -> reject "Meta in stored declaration"
  | Evar _ -> reject "Evar in stored declaration"
  | Sort s -> tag "Sort" ["sort",sort ctx s]
  | Cast(c,k,t) -> tag "Cast" ["term",term ctx c;"kind",cast_kind k;"type",term ctx t]
  | Prod(b,t,c) -> tag "Prod" ["binder",binder b;"domain",term ctx t;"codomain",term ctx c]
  | Lambda(b,t,c) -> tag "Lambda" ["binder",binder b;"domain",term ctx t;"body",term ctx c]
  | LetIn(b,v,t,c) -> tag "LetIn" ["binder",binder b;"value",term ctx v;"type",term ctx t;"body",term ctx c]
  | App(f,xs) -> tag "App" ["function",term ctx f;"arguments",arr(term ctx) xs]
  | Const(c,u) -> tag "Const" ["identity",constant c;"instance",instance ctx u]
  | Ind(i,u) -> tag "Ind" ["identity",inductive i;"instance",instance ctx u]
  | Construct(c,u) -> tag "Construct" ["identity",constructor c;"instance",instance ctx u]
  | Case(ci,u,params,((bs,ret),rel),iv,scrut,branches) ->
      let invert=match iv with NoInvert->tag"NoInvert"[]|CaseInvert{indices}->tag"CaseInvert"["indices",arr(term ctx) indices] in
      tag "Case" ["inductive",inductive ci.ci_ind;"npar",I ci.ci_npar;
        "constructor_ndecls",arr(fun i->I i) ci.ci_cstr_ndecls;
        "constructor_nargs",arr(fun i->I i) ci.ci_cstr_nargs;
        "instance",instance ctx u;"parameters",arr(term ctx) params;
        "return_binders",arr binder bs;"return",term ctx ret;"relevance",relevance rel;
        "inversion",invert;"scrutinee",term ctx scrut;
        "branches",arr(fun(bs,c)->O["binders",arr binder bs;"body",term ctx c]) branches]
  | Fix((rs,i),(bs,ts,cs)) -> tag"Fix"["recursion_indices",arr(fun x->I x) rs;"index",I i;
      "binders",arr binder bs;"types",arr(term ctx) ts;"bodies",arr(term ctx) cs]
  | CoFix(i,(bs,ts,cs)) -> tag"CoFix"["index",I i;"binders",arr binder bs;"types",arr(term ctx) ts;"bodies",arr(term ctx) cs]
  | Proj(p,r,c) -> tag "Proj" ["identity",projection p;"relevance",relevance r;"term",term ctx c]
  | Int x -> tag "Int" ["decimal",S(Uint63.to_string x)]
  | Float x -> tag "Float" ["hex",S(Float64.to_hex_string x)]
  | String x -> tag "String" ["bytes_hex",S(String.concat "" (List.init (String.length(Pstring.to_string x))
      (fun i->Printf.sprintf "%02x" (Char.code((Pstring.to_string x).[i])))))]
  | Array(u,xs,d,t) -> tag "Array" ["instance",instance ctx u;"values",arr(term ctx) xs;"default",term ctx d;"type",term ctx t]
let flags f = O["check_guarded",B f.check_guarded;"check_positive",B f.check_positive;
  "check_universes",B f.check_universes;"indices_matter",B f.indices_matter;
  "impredicative_set",B f.impredicative_set;"sprop_allowed",B f.sprop_allowed;"allow_uip",B f.allow_uip]
let full_registered_name g = let d,i=Libnames.repr_path(Nametab.path_of_global g) in
  String.concat "." (List.rev_map Id.to_string (DirPath.repr d) @ [Id.to_string i])
let export ?opaque_access mode name =
  if Coq_config.version <> "9.1.1" then reject("requires Rocq 9.1.1, found "^Coq_config.version);
  let g=try Nametab.global_of_path(Libnames.path_of_string name) with Not_found->reject("no exact global target "^name) in
  if full_registered_name g <> name then reject "requested path does not equal registered absolute target";
  let c=match g with GlobRef.ConstRef c->c|_->reject "prototype supports constant roots only" in
  let cb=Global.lookup_constant c in
  if cb.const_hyps <> [] then reject "open section hypotheses are unsupported";
  let ctx={levels=Univ.Level.Set.empty} in
  let ty=term ctx cb.const_type in
  let body,private_levels=match mode,cb.const_body with
    | "type",_ -> [],Univ.Level.Set.empty
    | "definition",Def c -> ["body",term ctx c],Univ.Level.Set.empty
    | "definition",_ -> reject "definition mode requires a transparent Def body"
    | "opaque-body",OpaqueDef _ ->
        let access=match opaque_access with Some a->a | None->reject "opaque access was not supplied" in
        let c,private_u,body_context=match Global.body_of_constant access c with
          | Some body->body | None->reject "opaque proof body is unavailable" in
        let b=term ctx c in
        let pu,levels=match private_u with
          | Opaqueproof.PrivateMonomorphic () -> tag "PrivateMonomorphic" [],Univ.Level.Set.empty
          | Opaqueproof.PrivatePolymorphic cs ->
              let levels=Univ.ContextSet.levels cs in
              let encoded=List.map (level ctx) (Univ.Level.Set.elements levels) in
              tag "PrivatePolymorphic" [
                "levels",L(List.sort(fun a b->String.compare(encode a)(encode b)) encoded);
                "constraints",constraints ctx (Univ.ContextSet.constraints cs)],levels in
        ["body",b;"body_private_universes",pu;
         "body_polymorphic_context",universes ctx (Polymorphic body_context)],levels
    | "opaque-body",_ -> reject "opaque-body mode requires an OpaqueDef body"
    | _ -> reject "mode must be type, definition or opaque-body" in
  let us=universes ctx cb.const_universes in
  let uh=instance ctx cb.const_univ_hyps in
  (* Private proof levels are encoded with their own constraints above;
     they need not be registered in the global universe graph. *)
  let global_levels=Univ.Level.Set.diff ctx.levels private_levels in
  let graph=Environ.universes(Global.env()) in
  let missing=Univ.Level.Set.diff global_levels (UGraph.domain graph) in
  if not(Univ.Level.Set.is_empty missing) then reject "universe level is neither global nor explicitly private";
  let result=O(["schema",S"rocq-kernel-identity-pilot-v3";"rocq",S Coq_config.version;
    "target",S name;"mode",S mode;"identity",constant c;"type",ty;
    "relevance",relevance cb.const_relevance;"universes",us;"section_universes",uh;
    "typing_flags",flags cb.const_typing_flags]@body) in
  Feedback.msg_notice(Pp.str("KERNEL_IDENTITY " ^ encode result))
let _=Mltop.add_known_module "kernel_identity"
let () =
  let open Stdarg in
  Vernacextend.static_vernac_extend ~plugin:(Some "kernel_identity") ~command:"KernelIdentity"
    ~classifier:(fun ~atts:_ _ -> Vernacextend.classify_as_query) ?entry:None
    [(Vernacextend.TyML(false,
       Vernacextend.TyTerminal("KernelIdentity",
         Vernacextend.TyNonTerminal(Extend.TUentry(Genarg.get_arg_tag wit_string),
           Vernacextend.TyNonTerminal(Extend.TUentry(Genarg.get_arg_tag wit_string),Vernacextend.TyNil))),
       (fun mode name ?loc:_ ~atts () ->
         Attributes.unsupported_attributes atts;
         if mode="opaque-body" then
           Vernactypes.vtopaqueaccess(fun ~opaque_access -> export ~opaque_access mode name)
         else Vernactypes.vtdefault(fun () -> export mode name)),None))]
