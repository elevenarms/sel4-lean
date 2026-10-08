theory Consts
  imports ExecSpec.API_H ExecSpec.ArchIntermediate_H
begin

text \<open>Dump every constant defined in l4v's executable spec (session ExecSpec, including the machine
theories it loads): name, defining theory, type. Output: GATE_OUT/consts.tsv\<close>

ML \<open>
  val out = Path.explode (getenv "GATE_OUT") + Path.basic "consts.tsv"
  val ctxt = Config.put show_question_marks false @{context}
  val consts = Sign.consts_of @{theory}
  val space = Consts.space_of consts
  val {constants, ...} = Consts.dest consts
  (* constants with a definitional axiom (definition, defs, primrec, fun, …), and datatype constructors:
     every other constant is unspecified in l4v's spec (`consts` without a definition) *)
  val defined = fold (fn (_, th) =>
      (case Thm.prop_of th of
        Const (@{const_name Pure.eq}, _) $ lhs $ _ =>
          (case head_of lhs of Const (c, _) => Symtab.update (c, ()) | _ => I)
      | _ => I)) (Thm.all_axioms_of @{theory}) Symtab.empty
  fun is_ctr c =
    (case try (body_type o Sign.the_const_type @{theory}) c of
      SOME (Type (tn, _)) =>
        (case Ctr_Sugar.ctr_sugar_of ctxt tn of
          SOME (sg : Ctr_Sugar.ctr_sugar) => exists (fn t => fst (dest_Const t) = c) (#ctrs sg)
        | NONE => false)
    | _ => false)
  fun status c = if Symtab.defined defined c then "def" else if is_ctr c then "ctr"
                 else if can (Consts.the_abbreviation consts) c then "abbrev" else "unspecified"
  fun row (name, (ty, _)) =
    let val thy = #theory_long_name (Name_Space.the_entry space name)
    in if String.isPrefix "ExecSpec." thy
       then SOME (name ^ "\t" ^ thy ^ "\t" ^
                  (Print_Mode.setmp [] (fn () => Syntax.string_of_typ ctxt ty) ()
                   |> String.translate (fn #"\n" => " " | c => str c)) ^ "\t" ^ status name)
       else NONE
    end
  val rows = map_filter row constants
  val _ = File.write out (cat_lines rows ^ "\n")
  val _ = writeln ("GATE consts: " ^ string_of_int (length rows))
\<close>

end
