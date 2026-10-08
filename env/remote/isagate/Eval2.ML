(* Lean <-> Isabelle structured-value gate: evaluate one chunk of cases in l4v's ExecSpec.
   Run by `isabelle process -l ExecSpec -f Eval2.ML` with GATE_CASES (id<TAB>term lines) and GATE_RESULTS.
   One process per chunk, so a case that exhausts the ML heap costs only its own chunk. *)
val thy = Thy_Info.get_theory "ExecSpec.ArchIntermediate_H";
val ctxt = Proof_Context.init_global thy;
val space = Consts.space_of (Sign.consts_of thy);
(* a spec definition to unfold: defined in ExecSpec, and not datatype machinery (constructors and case
   combinators are ExecSpec constants too; unfolding them exposes the datatype package's representation) *)
fun is_ctr c =
  (case try (body_type o Sign.the_const_type thy) c of
    SOME (Type (tn, _)) =>
      (case Ctr_Sugar.ctr_sugar_of ctxt tn of
        SOME (sugar : Ctr_Sugar.ctr_sugar) => exists (fn t => fst (dest_Const t) = c) (#ctrs sugar)
      | NONE => false)
  | _ => false);
fun datatype_const c =
  is_ctr c orelse is_some (Ctr_Sugar.ctr_sugar_of_case ctxt c)
  orelse exists (fn p => String.isSubstring p c) ["Abs_", "Rep_", ".ctor_", ".dtor_", "_IITN_", "pre_"];
fun spec_const c = (String.isPrefix "ExecSpec." (#theory_long_name (Name_Space.the_entry space c))
                    handle ERROR _ => false) andalso not (datatype_const c);
val def_tab =
  fold (fn (_, th) => fn tab =>
      (case Thm.prop_of th of
        Const ("Pure.eq", _) $ lhs $ _ =>
          (case head_of lhs of
            Const (c, _) => if spec_const c then Symtab.cons_list (c, th) tab else tab
          | _ => tab)
      | _ => tab))
    (Thm.all_axioms_of thy) Symtab.empty;
fun consts_in t = Term.fold_aterms (fn Const (c, _) => insert (op =) c | _ => I) t [];
fun unfold t n =
  let val defs = maps (Symtab.lookup_list def_tab) (consts_in t) in
    if null defs orelse n = 0 then t
    else
      let val t' = Thm.rhs_of (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps defs)
                                 (Thm.cterm_of ctxt t)) |> Thm.term_of
      in if t' aconv t then t else unfold t' (n - 1) end
  end;
val word_size = Proof_Context.get_thms ctxt "word_size";
val value = Timeout.apply (Time.fromSeconds 30) (Value_Command.value ctxt);
fun simp u = Thm.rhs_of (Timeout.apply (Time.fromSeconds 30)
               (Simplifier.rewrite (ctxt addsimps word_size)) (Thm.cterm_of ctxt u)) |> Thm.term_of;
(* only values print: constructors (of datatypes), numerals, literals; anything else is not evaluated yet *)
fun sexp t =
  (case try HOLogic.dest_number t of
    SOME (_, n) => string_of_int n
  | NONE =>
    (case strip_comb t of
      (Const ("Nat.Suc", _), [a]) =>   (* the simplifier writes 1 as Suc 0 *)
        (case Int.fromString (sexp a) of SOME n => string_of_int (n + 1) | NONE => raise TERM ("Suc", [t]))
    | (Const ("HOL.True", _), []) => "True"
    | (Const ("HOL.False", _), []) => "False"
    | (Const ("Option.option.None", _), []) => "None"
    | (Const ("Option.option.Some", _), [a]) => "(Some " ^ sexp a ^ ")"
    | (Const ("List.list.Nil", _), []) => "[]"
    | (Const ("List.list.Cons", _), _) =>
        (case try HOLogic.dest_list t of
          SOME xs => "[" ^ space_implode ", " (map sexp xs) ^ "]"
        | NONE => raise TERM ("open list", [t]))
    | (Const ("Product_Type.Pair", _), [a, b]) => "(Pair " ^ sexp a ^ " " ^ sexp b ^ ")"
    | (Const (c, _), args) =>
        if is_ctr c then
          (if null args then Long_Name.base_name c
           else "(" ^ Long_Name.base_name c ^ " " ^ space_implode " " (map sexp args) ^ ")")
        else raise TERM ("not a value", [t])
    | _ => raise TERM ("not a value", [t])));
(* datatypes declared inside `context Arch` keep their simp rules local to it: add the case/distinctness/
   injectivity equations of every datatype whose case combinator or constructors occur in the term *)
fun sugar_thms u =
  maps (fn c =>
      (case Ctr_Sugar.ctr_sugar_of_case ctxt c of
        SOME (sg : Ctr_Sugar.ctr_sugar) => #case_thms sg @ #distincts sg @ #injects sg
      | NONE => []))
    (consts_in u);
fun simp_term u =
  Thm.rhs_of (Timeout.apply (Time.fromSeconds 20)
    (Simplifier.rewrite (ctxt addsimps (word_size @ sugar_thms u))) (Thm.cterm_of ctxt u)) |> Thm.term_of;
(* code evaluation first; else rounds of unfold (spec definitions) + simplification (case on constructors,
   word arithmetic) until the term is a value *)
fun eval1 s =
  let
    val t = Syntax.read_term ctxt s
    fun rounds u n =
      (case try sexp u of
        SOME r => r
      | NONE =>
          (case try (sexp o value) u of
            SOME r => r
          | NONE =>
              if n = 0 then error ("stuck: " ^ Print_Mode.setmp [] (fn () => Syntax.string_of_term ctxt u) ())
              else
                let val u' = simp_term (unfold u 4)
                in if u' aconv u then error ("stuck: " ^ Print_Mode.setmp [] (fn () =>
                                     Syntax.string_of_term ctxt u) ())
                   else rounds u' (n - 1) end))
  in rounds t 8 end;
fun ev line =
  (case space_explode "\t" line of
    [id, s] =>
      (case Exn.result (Timeout.apply (Time.fromSeconds 40) eval1) s of
        Exn.Res r => id ^ "\t" ^ r
      | Exn.Exn e => id ^ "\tERR " ^ space_implode " | " (take 6 (split_lines
                       (XML.content_of (YXML.parse_body (Runtime.exn_message e))))))
  | _ => "");
val out = Path.explode (getenv "GATE_RESULTS");
val _ = File.write out "";
val _ = List.app (fn l => if l = "" then () else File.append out (ev l ^ "\n"))
          (split_lines (File.read (Path.explode (getenv "GATE_CASES"))));
