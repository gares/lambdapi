open Elpi.API

let sym : Terms.sym Conversion.t = OpaqueData.declare {
  OpaqueData.name = "symbol";
  doc = "A symbol";
  pp = Print.pp_symbol;
  compare = Terms.Sym.compare;
  hash = Hashtbl.hash;
  hconsed = false;
  constants = [];
}

let typec = RawData.Constants.declare_global_symbol "typ"
let kindc = RawData.Constants.declare_global_symbol "kin"
let symbc = RawData.Constants.declare_global_symbol "symb"
let prodc = RawData.Constants.declare_global_symbol "prod"
let abstc = RawData.Constants.declare_global_symbol "abst"
let applc = RawData.Constants.declare_global_symbol "appl"

let embed_term : Terms.term Conversion.embedding = fun ~depth st t ->
  let open RawData in
  let open Terms in
  let gls = ref [] in
  let call f ~depth s x = let s, x, g = f ~depth s x in gls := g @ !gls; s, x in
  let rec aux ~depth st ctx = function
    | Vari v ->
        let d = Ctxt.type_of v ctx in
        st, mkBound d
    | Type -> st, mkGlobal typec
    | Kind -> st, mkGlobal kindc
    | Symb s ->
        let st, s = call sym.Conversion.embed ~depth st s in
        st, mkApp symbc s []
    | Prod (src, tgt) ->
        let st, src = aux ~depth st ctx src in
        let _,tgt,ctx = Ctxt.unbind ctx depth None tgt in
        let st, tgt = aux ~depth:(depth+1) st ctx tgt in
        st, mkApp prodc src [mkLam tgt]
    | Abst (ty, body) ->
        let st, ty = aux ~depth st ctx ty in
        let _,body,ctx = Ctxt.unbind ctx depth None body in
        let st, body = aux ~depth:(depth+1) st ctx body in
        st, mkApp prodc ty [mkLam body]
    | Appl (hd, arg) ->
        let st, hd = aux ~depth st ctx hd in
        let st, arg = aux ~depth st ctx arg in
        st, mkApp applc hd [arg]
    | Meta _ -> assert false
    | Patt _ -> Console.fatal_no_pos "embed_term: Patt not implemented"
    | TEnv _ -> Console.fatal_no_pos "embed_term: TEnv not implemented"
    | Wild   -> Console.fatal_no_pos "embed_term: Wild not implemented"
    | TRef _ -> Console.fatal_no_pos "embed_term: TRef not implemented"
    | LLet _ -> Console.fatal_no_pos "embed_term: LLet not implemented"
  in
  let st, t = aux ~depth st [] t in
  st, t, List.rev !gls

let readback_term : Terms.term Conversion.readback = fun ~depth st t ->
  let open RawData in
  let open Terms in
  let gls = ref [] in
  let call f ~depth s x = let s, x, g = f ~depth s x in gls := g @ !gls; s, x in
  let rec aux ~depth st ctx t =
    match look ~depth t with
    | Const c when c == typec -> st, _Type
    | Const c when c == kindc -> st, _Kind
    | Const c when c >= 0 ->
        begin try
          let v = Extra.IntMap.find c ctx in
          st, _Vari v
        with Not_found -> Utils.type_error "readback_term" end
    | App(c,s,[]) when c == symbc ->
        let st, s = call sym.Conversion.readback ~depth st s in
        st, _Symb s
    | App(c,ty,[bo]) when c == prodc ->
        let st, ty = aux ~depth st ctx ty in
        let st, bo = aux_lam ~depth st ctx bo in
        st, _Prod ty bo
    | App(c,ty,[bo]) when c == abstc ->
        let st, ty = aux ~depth st ctx ty in
        let st, bo = aux_lam ~depth st ctx bo in
        st, _Abst ty bo
    | App(c,hd,[arg]) when c == applc ->
        let st, hd = aux ~depth st ctx hd in
        let st, arg = aux ~depth st ctx arg in
        st, _Appl hd arg
    | _ -> Utils.type_error "readback_term"
  and aux_lam ~depth st ctx t =
    match look ~depth t with
    | Lam bo ->
        let v = Bindlib.new_var mkfree "x" in
        let ctx = Extra.IntMap.add depth v ctx in
        let st, bo = aux ~depth:(depth+1) st ctx bo in
        st, Bindlib.bind_var v bo
    | _ -> Utils.type_error "readback_term"
  in
  let st, t = aux ~depth st Extra.IntMap.empty t in
  st, Bindlib.unbox t, List.rev !gls

let term : Terms.term Conversion.t = {
  Conversion.ty = Conversion.TyName "term";
  pp = Print.pp_term;
  pp_doc = (fun fmt () -> Format.fprintf fmt {|
kind term type.
type typ term.
type kin term.
type symb symbol -> term.
type appl term -> term -> term.
type abst term -> (term -> term) -> term.
type prod term -> (term -> term) -> term.
  |});
  readback = readback_term;
  embed = embed_term;
}

let lambdapi_builtin_declarations : BuiltIn.declaration list =
  let open BuiltIn in
  let open BuiltInPredicate in
  let open BuiltInData in
  let open BuiltInPredicate.Notation in
[
  LPDoc "---- Lambdapi datatypes ----";

  MLData sym;
  MLData term;

  LPDoc "---- Builtin predicates ----";

  MLCode(Pred("lp.term->string",
    In(term,"T",
    Out(string,"S",
    Easy "Pretty prints a term T to the string S")),
    (fun t _ ~depth:_ -> !: (Format.asprintf "%a" Print.pp_term t))),
    DocAbove);

  LPDoc "---- Elpi predicates ----";

] @ Elpi.Builtin.core_builtins @ Elpi.Builtin.elpi_builtins

let lambdapi_builtins =
  BuiltIn.declare ~file_name:"lambdap.elpi" lambdapi_builtin_declarations

let elpi = ref None

let document () =
  BuiltIn.document_file ~header:"% automatically generated" lambdapi_builtins

let init () =
  let e, _ = Setup.init ~builtins:[lambdapi_builtins] ~basedir:"." [] in
  elpi := Some e;
  document ()

let loc_of_pos = function
  | None -> Ast.Loc.initial "(elpi)"
  | Some x ->
      let { Pos.fname; start_line; start_col; _ } = Lazy.force x in
      {
        Ast.Loc.source_name = Extra.Option.get "(.)" fname;
        source_start = 0;
        source_stop = 0;
        line = start_line;
        line_starts_at = start_col;
      }

let run : Sig_state.t -> string -> string -> Syntax.p_term -> unit =
fun ss file predicate arg ->
  let pos = arg.Pos.pos in
  let arg = Scope.scope_term Public ss Env.empty arg in
  let elpi = match !elpi with None -> assert false | Some x -> x in
  let ast = Parse.program ~elpi [file] in
  let prog = Elpi.API.Compile.program ~flags:Elpi.API.Compile.default_flags ~elpi [ast] in
  let loc = loc_of_pos pos in
  let arguments = Query.(D(term,arg,N)) in
  let query = Query.(compile prog loc (Query { predicate; arguments })) in
  if not (Elpi.API.Compile.static_check ~checker:(Elpi.Builtin.default_checker ()) query) then
    Console.fatal pos "elpi: type error";
  let exe = Elpi.API.Compile.optimize query in
  match Execute.once exe with
  | Execute.Success _ -> ()
  | Failure -> Console.fatal_no_pos "elpi: failure"
  | NoMoreSteps -> assert false
